%% -------------------------------------------------------------------
%%
%% Copyright <2013-2018> <
%%  Technische Universität Kaiserslautern, Germany
%%  Université Pierre et Marie Curie / Sorbonne-Université, France
%%  Universidade NOVA de Lisboa, Portugal
%%  Université catholique de Louvain (UCL), Belgique
%%  INESC TEC, Portugal
%% >
%%
%% This file is provided to you under the Apache License,
%% Version 2.0 (the "License"); you may not use this file
%% except in compliance with the License.  You may obtain
%% a copy of the License at
%%
%%   http://www.apache.org/licenses/LICENSE-2.0
%%
%% Unless required by applicable law or agreed to in writing,
%% software distributed under the License is distributed on an
%% "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
%% KIND, either expressed or implied.  See the License for the
%% specific language governing permissions and limitations
%% under the License.
%%
%% List of the contributors to the development of Antidote: see AUTHORS file.
%% Description and complete License: see LICENSE file.
%% -------------------------------------------------------------------

%% -------------------------------------------------------------------
%% @author pedrolopes
%% @doc module antidote_crdt_index_s - A secondary index CRDT
%%
%% An operation-based CRDT that serves as an index, mapping raw values
%% to AntidoteDB keys. It also exports update operations to add and
%% to delete (i.e. reset) index entries.
%% It keeps two data structures, the index map and the indirection map:
%% - the index map stores index entries; each entry maps a raw indexed
%%   value to a set of primary keys (represented as AntidoteDB keys);
%% - the indirection map stores the inverted bindings between primary
%%   keys and indexed values and has a similar behaviour as the
%%   grow-only map CRDT.
%%
%% This data type uses the Erlang's gb_trees to store index entries
%% and a dictionary to store data from the indirection map.
%% It was specially designed to support the Antidote Query Language
%% (AQL) system.
%% -------------------------------------------------------------------

-module(antidote_crdt_index_s).
-behaviour(antidote_crdt).

-define(LOWER_BOUND_PRED, [greater, greatereq]).
-define(UPPER_BOUND_PRED, [lesser, lessereq]).
-define(WRONG_PRED(Preds), io_lib:format("Some of the predicates don't respect a range query: ~p", [Preds])).
-define(BCOUNTER_DT, antidote_crdt_counter_b).

%% API
-export([new/0,
         value/1,
         value/2,
         downstream/2,
         update/2,
         equal/2,
         to_binary/1, from_binary/1,
         is_operation/1,
         require_state_downstream/1]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

-export_type([antidote_crdt_index_s/0,
              antidote_crdt_index_s_op/0,
              antidote_crdt_index_s_query/0]).

-type antidote_crdt_index_s() :: {indexmap(), indirectionmap()}.
-type gb_tree_node() :: nil | {_, _, _, _}.
-type indexmap() :: {non_neg_integer(), gb_tree_node()}.
-type indirectionmap() :: dict:dict(Key::term(), [{FieldName::atom(), FieldType::atom(), FieldState::term()}]).

-type pred_type() :: greater | greatereq | lesser | lessereq | equality | notequality.
-type pred_arg() :: number().
-type predicate() :: {pred_type(), pred_arg()} | infinity.

-type antidote_crdt_index_s_query() :: {range, {predicate(), predicate()} | predicate()} |
                                       {get, term()} |
                                       {lookup, term()}.

-type antidote_crdt_index_s_op() :: {update, nested_op()} |
                                    {update, [nested_op()]} |
                                    {remove, remove_op()} |
                                    {remove, [remove_op()]}.
-type nested_op() :: {Key::term(), Op::[term()]} | {Key::term(), Op::term()}.
-type remove_op() :: {Key::term()}.

-type index_effect() :: {update, nested_downstream()} |
                        {update, [nested_downstream()]} |
                        {remove, remove_downstream()} |
                        {remove, [remove_downstream()]}.
-type nested_downstream() :: {Key::term(), Op::[term()]}.
-type remove_downstream() :: {Key::term(), none} | {Key::term(), Op::[term()]}.

-type key_not_found() :: {error, key_not_found}.
-type wrong_predicate() :: erlang:throw(string()).
-type value_output() :: [{term(), term()}] | {term(), term()} |
                        key_not_found() |
                        wrong_predicate().

-spec new() -> antidote_crdt_index_s().
new() ->
  {gb_trees:empty(), dict:new()}.

-spec value(antidote_crdt_index_s()) -> value_output().
value({IndexTree, _Indirection}) ->
  gb_trees:to_list(IndexTree).

-spec value(antidote_crdt_index_s_query(), antidote_crdt_index_s()) -> value_output().
value({range, {equality, Val}}, Index) ->
  value({get, Val}, Index);
value({range, {notequality, _Val} = Pred}, {IndexTree, _Indirection}) ->
  iterate_and_filter({Pred, [key]}, gb_trees:iterator(IndexTree), []);
value({range, {LowerPred, UpperPred}}, {IndexTree, _Indirection}) ->
  case validate_pred(lower, LowerPred) andalso validate_pred(upper, UpperPred) of
    true ->
      Iterator = case LowerPred of
                   infinity ->
                     gb_trees:iterator(IndexTree);
                   _ ->
                     gb_trees:iterator_from(lookup_lower_bound(LowerPred, IndexTree), IndexTree)
                 end,
      iterate_and_filter({UpperPred, [key]}, gb_trees:next(Iterator), []);
    false ->
      throw(lists:flatten(?WRONG_PRED({LowerPred, UpperPred})))
  end;
value({get, Key}, {IndexTree, _Indirection}) ->
  case gb_trees:lookup(Key, IndexTree) of
    {value, Value} ->
      {Key, Value};
    none ->
      {error, key_not_found}
  end;
value({lookup, Key}, {_IndexTree, Indirection} = Index) ->
  case dict:find(Key, Indirection) of
    {ok, Entry} ->
      {index_val, FieldType, FieldState} = entry_field(index_val, undefined, Entry),
      case FieldType of
        undefined ->
          {error, key_not_found};
        _ ->
          Value = FieldType:value(FieldState),
          value({get, calc_value(FieldType, Value)}, Index)
      end;
    error ->
      {error, key_not_found}
  end.

-spec downstream(antidote_crdt_index_s_op(), antidote_crdt_index_s()) -> {ok, index_effect()}.
downstream({update, {Key, Ops}}, {_IndexTree, Indirection}) when is_list(Ops) ->
  Entry =
    case dict:find(Key, Indirection) of
      {ok, State} ->
        State;
      error ->
        []
    end,
  DownstreamOps =
    lists:map(fun({FieldName, FieldType, Op}) ->
      {FieldName, FieldType, FieldState} = entry_field(FieldName, FieldType, Entry),
      {ok, DownstreamOp} = FieldType:downstream(Op, FieldState),
      {FieldName, FieldType, DownstreamOp}
    end, Ops),
  {ok, {update, {Key, DownstreamOps}}};
downstream({update, {Key, Op}}, Index) ->
  downstream({update, {Key, [Op]}}, Index);
downstream({update, Ops}, Index) when is_list(Ops) ->
  {ok, {update, lists:map(fun(Op) -> {ok, DSOp} = downstream({update, Op}, Index), DSOp end, Ops)}};
downstream({remove, Ops}, Index) when is_list(Ops) ->
  {ok, {remove, lists:map(fun(Op) -> {ok, DSOp} = downstream({remove, Op}, Index), DSOp end, Ops)}};
downstream({remove, Key}, Index) ->
  DownstreamOp = generate_downstream_remove(Key, Index),
  {ok, {remove, DownstreamOp}}.

-spec update(index_effect(), antidote_crdt_index_s()) -> {ok, antidote_crdt_index_s()}.
update({update, {Key, Ops}}, {IndexTree, Indirection}) when is_list(Ops) ->
  {OldEntry, NewEntry} = apply_op(Key, Ops, Indirection),
  case OldEntry == NewEntry of
    true ->
      {ok, {IndexTree, Indirection}};
    false ->
      NewIndirection = dict:store(Key, NewEntry, Indirection),
      NewIndexTree =
        case is_bottom(NewEntry) orelse length(NewEntry) < 2 of
          true ->
            IndexTree;
          false ->
            update_index(get_value(OldEntry), get_value(NewEntry), IndexTree)
        end,
      {ok, {NewIndexTree, NewIndirection}}
  end;
update({update, Ops}, Index) when is_list(Ops) ->
    apply_ops(Ops, Index);
update({remove, {_Key, none}}, Index) ->
    {ok, Index};
update({remove, {Key, Ops}}, {IndexTree, Indirection}) when is_list(Ops) ->
  {OldEntry, NewEntry} = apply_op(Key, Ops, Indirection),
  case OldEntry == NewEntry of
    true ->
      {ok, {IndexTree, Indirection}};
    false ->
      NewIndirection = dict:store(Key, NewEntry, Indirection),
      NewIndexTree =
        case is_bottom(NewEntry) orelse length(NewEntry) < 2 of
          true ->
            {_, _, OldBObj} = entry_field(bound_obj, undefined, get_value(OldEntry)),
            {_, _, OldIndexVal} = entry_field(index_val, undefined, get_value(OldEntry)),
            remove_entry(OldIndexVal, OldBObj, IndexTree);
          false ->
            update_index(get_value(OldEntry), get_value(NewEntry), IndexTree)
        end,
      {ok, {NewIndexTree, NewIndirection}}
  end;
update({remove, Ops}, Index) when is_list(Ops) ->
  apply_ops(Ops, Index).

-spec equal(antidote_crdt_index_s(), antidote_crdt_index_s()) -> boolean().
equal({IndexTree1, Indirection1}, {IndexTree2, Indirection2}) ->
  IndexTree1 =:= IndexTree2 andalso
    dict:size(Indirection1) =:= dict:size(Indirection2) andalso
    rec_equals(Indirection1, Indirection2).

-define(TAG, 101).
-define(V1_VERS, 1).

-spec to_binary(antidote_crdt_index_s()) -> binary().
to_binary(Index) ->
  <<?TAG:8/integer, ?V1_VERS:8/integer, (term_to_binary(Index))/binary>>.

-spec from_binary(binary()) -> {ok, antidote_crdt_index_s()}.
from_binary(<<?TAG:8/integer, ?V1_VERS:8/integer, Bin/binary>>) ->
  {ok, binary_to_term(Bin)}.

-spec is_operation(term()) -> boolean().
is_operation(Operation) ->
  case Operation of
    {range, {_LowerPred, _UpperPred}} ->
      true;
    {get, _Key} ->
      true;
    {lookup, _Key} ->
      true;
    {update, {_Key, Ops}} when is_list(Ops) ->
      EmptyEntry = [],
      try
        lists:foldl(fun({FieldName, FieldType, Op}, BoolAcc) ->
          {FieldName, FieldType, _} = entry_field(FieldName, FieldType, EmptyEntry),
          BoolAcc andalso FieldType:is_operation(Op)
        end, true, Ops)
      of
        Result -> Result
      catch
        _:_ -> false
      end;
    {update, {Key, Op}} ->
      is_operation({update, {Key, [Op]}});
    {remove, {_Key, Ops}} ->
      EmptyEntry = [],
      try
        (Ops == none orelse
          lists:foldl(fun({FieldName, FieldType, Op}, BoolAcc) ->
            {FieldName, FieldType, _} = entry_field(FieldName, FieldType, EmptyEntry),
            BoolAcc andalso (Op == none orelse FieldType:is_operation(Op))
          end, true, Ops))
      of
        Result -> Result
      catch
        _:_ -> false
      end;
    {remove, _Key} ->
      true;
    {OpType, Ops} when is_list(Ops) ->
      distinct([Key || {Key, _} <- Ops]) andalso
        lists:all(fun(Op) -> is_operation({OpType, Op}) end, Ops);
    _ ->
      false
  end.

-spec require_state_downstream(term()) -> boolean().
require_state_downstream(_Op) ->
  true.

%% ===================================================================
%% Internal functions
%% ===================================================================
entry_field(FieldName, FieldType, Entry) ->
  case lists:keyfind(FieldName, 1, Entry) of
    false -> empty_field(FieldName, FieldType);
    Tuple -> Tuple
  end.

empty_field(FieldName, undefined) ->
  {FieldName, undefined, undefined};
empty_field(FieldName, FieldType) ->
  {FieldName, FieldType, FieldType:new()}.

update_index(OldEntry, NewEntry, IndexTree) ->
  {_, _, OldEntryValue} = entry_field(bound_obj, undefined, OldEntry),
  {_, _, OldEntryKey} = entry_field(index_val, undefined, OldEntry),
  {_, _, NewEntryValue} = entry_field(bound_obj, undefined, NewEntry),
  {_, _, NewEntryKey} = entry_field(index_val, undefined, NewEntry),
  Removed = remove_entry(OldEntryKey, OldEntryValue, IndexTree),

  %% The insert is much slower than the update in gb_trees.
  %% That's why we first lookup for an entry and, if it
  %% exists, we update it, instead of forcing to insert
  %% an already existing entry.
  case gb_trees:lookup(NewEntryKey, Removed) of
    {value, Set2} ->
      gb_trees:update(NewEntryKey, ordsets:add_element(NewEntryValue, Set2), Removed);
    none ->
      gb_trees:insert(NewEntryKey, ordsets:add_element(NewEntryValue, ordsets:new()), Removed)
  end.

remove_entry(undefined, _, IndexTree) ->
  IndexTree;
remove_entry(_, undefined, IndexTree) ->
  IndexTree;
remove_entry(EntryKey, EntryValue, IndexTree) ->
  case gb_trees:lookup(EntryKey, IndexTree) of
    {value, Set} ->
      case ordsets:is_element(EntryValue, Set) of
        true ->
          NewSet = ordsets:del_element(EntryValue, Set),
          case ordsets:size(NewSet) > 0 of
            false ->
              gb_trees:delete(EntryKey, IndexTree);
            true ->
              gb_trees:update(EntryKey, NewSet, IndexTree)
          end;
        false ->
          full_search(EntryValue, IndexTree)
      end;
    none ->
      IndexTree
  end.

apply_op(Key, Ops, Indirection) ->
  case dict:find(Key, Indirection) of
    {ok, Entry} ->
      NewStates =
        lists:foldl(fun({FieldName, FieldType, Op}, AccEntry) ->
          {FieldName, FieldType, FieldState} = entry_field(FieldName, FieldType, AccEntry),
          {ok, UpdatedState} = FieldType:update(Op, FieldState),
          lists:keystore(FieldName, 1, AccEntry, {FieldName, FieldType, UpdatedState})
        end, Entry, Ops),

      {Entry, NewStates};
    error ->
      NewStates =
        lists:foldl(fun({FieldName, FieldType, Op}, AccEntry) ->
          {FieldName, FieldType, FieldState} = entry_field(FieldName, FieldType, AccEntry),
          {ok, UpdatedState} = FieldType:update(Op, FieldState),
          lists:keystore(FieldName, 1, AccEntry, {FieldName, FieldType, UpdatedState})
        end, [], Ops),

      {[], NewStates}
  end.

generate_downstream_remove(Key, {_IndexTree, Indirection}) ->
  Entry =
    case dict:find(Key, Indirection) of
      {ok, State} ->
        State;
      error ->
        []
    end,

  DownstreamOps =
    lists:map(fun({FieldName, FieldType, FieldState}) ->
      DownstreamEffect = resolve_downstream(FieldType, FieldState),
      {FieldName, FieldType, DownstreamEffect}
    end, Entry),

  case DownstreamOps of
    [] ->
      {Key, none};
    _ ->
      {Key, DownstreamOps}
  end.

resolve_downstream(Type, State) ->
  case Type:is_operation({reset, {}}) of
    true ->
      {ok, DownS} = Type:downstream({reset, {}}, State),
      DownS;
    false ->
      resolve_downstream0(Type, State)
  end.

%% A simple solver for CRDTs which do not have a reset operation.
resolve_downstream0(antidote_crdt_register_lww = Type, State) ->
  {ok, DS} = Type:downstream({assign, <<>>}, State),
  DS;
%% This function assumes there's only one actor updating the counter.
resolve_downstream0(antidote_crdt_counter_b = Type, State) ->
  CounterV = calc_value(Type, Type:value(State)),
  {ok, DS} = Type:downstream({decrement, {CounterV, term}}, State),
  DS;
resolve_downstream0(antidote_crdt_counter_pn = Type, State) ->
  CounterV = Type:value(State),
  {ok, DS} = Type:downstream({decrement, CounterV}, State),
  DS;
resolve_downstream0(_, _) ->
  none.

is_bottom(Entry) ->
  lists:foldl(fun({_FieldName, FieldType, FieldState}, BoolAcc) ->
    BoolAcc orelse is_bottom0(FieldType, FieldState)
  end, false, Entry).

is_bottom0(Type, State) ->
  Val1 = calc_value(Type, Type:value(State)),
  Val2 = calc_value(Type, Type:value(Type:new())),
  (erlang:function_exported(Type, is_bottom, 1) andalso Type:is_bottom(State))
    orelse Val1 == Val2.

get_value(State) ->
  lists:map(fun({FieldName, FieldType, FieldState}) ->
    Value = FieldType:value(FieldState),
    {FieldName, FieldType, calc_value(FieldType, Value)}
  end, State).

%% A special case for a bounded counter, where the value of an index entry
%% supported by this CRDT corresponds to the difference between the sum of
%% increments and the sum of decrements.
calc_value(?BCOUNTER_DT, {Inc, Dec}) ->
  IncList = orddict:to_list(Inc),
  DecList = orddict:to_list(Dec),
  SumInc = sum_values(IncList),
  SumDec = sum_values(DecList),
  SumInc - SumDec;
calc_value(_, Value) ->
  Value.

sum_values(List) when is_list(List) ->
  lists:sum([Value || {_Ids, Value} <- List]).

apply_ops([], Index) ->
  {ok, Index};
apply_ops([Op | Rest], Index) ->
  {ok, Index2} = update(Op, Index),
  apply_ops(Rest, Index2).

rec_equals(Indirection1, Indirection2) ->
  IndList1 = dict:to_list(Indirection1),
  IndList2 = dict:to_list(Indirection2),
  Remaining =
    lists:dropwhile(fun({Key, Value}) ->
      case proplists:lookup(Key, IndList2) of
        none ->
          false;
        {Key, Value2} ->
          is_equal(Value, Value2)
      end
    end, IndList1),
  length(Remaining) =:= 0.

is_equal(Entry1, Entry2) ->
  lists:foldl(fun({FieldName, FieldType, FieldState}, BoolAcc) ->
    {_, OtherFieldType, OtherState} = entry_field(FieldName, FieldType, Entry2),
    BoolAcc andalso FieldType == OtherFieldType andalso FieldType:equal(FieldState, OtherState)
  end, true, Entry1).

distinct([]) ->
  true;
distinct([X | Xs]) ->
  not lists:member(X, Xs) andalso distinct(Xs).

lookup_lower_bound(_LowerPred, {0, _Tree}) ->
  nil;
lookup_lower_bound(LowerPred, {Size, Tree}) when Size > 0 ->
  lookup_lower_bound(LowerPred, Tree, nil).
lookup_lower_bound(_LowerPred, nil, Final) ->
  Final;
lookup_lower_bound(LowerPred, {Key, _Value, Left, Right}, Final) ->
  case apply_pred(LowerPred, Key) of
    true ->
      lookup_lower_bound(LowerPred, Left, Key);
    false ->
      lookup_lower_bound(LowerPred, Right, Final)
  end.

iterate_and_filter(_Predicate, none, Acc) ->
  Acc;
iterate_and_filter({infinity, _} = Predicate, {Key, Value, Iter}, Acc) ->
  iterate_and_filter(Predicate, gb_trees:next(Iter), lists:append(Acc, [{Key, Value}]));
iterate_and_filter({Bound, Params} = Predicate, {Key, Value, Iter}, Acc) ->
  Result = case Params of
             [key] ->
               apply_pred(Bound, Key);
             [value, V] ->
               apply_pred(Bound, [Value, V])
           end,
  case Result of
    true ->
      iterate_and_filter(Predicate, gb_trees:next(Iter), lists:append(Acc, [{Key, Value}]));
    false ->
      iterate_and_filter(Predicate, gb_trees:next(Iter), Acc)
  end.

full_search(EntryValue, IndexTree) ->
  Iterator = gb_trees:iterator(IndexTree),
  FilterFun = fun([Set, V]) -> ordsets:is_element(V, Set) end,
  case iterate_and_filter({FilterFun, [value, EntryValue]}, gb_trees:next(Iterator), []) of
    [] ->
      IndexTree;
    Entries ->
      lists:foldl(fun({Key, Value}, AccIndex) ->
        NewSet = ordsets:del_element(EntryValue, Value),
        case ordsets:size(NewSet) > 0 of
          false ->
            gb_trees:delete(Key, AccIndex);
          true ->
            gb_trees:update(Key, NewSet, AccIndex)
        end
      end, IndexTree, Entries)
  end.

validate_pred(_BoundType, infinity) ->
  true;
validate_pred(lower, {Type, _Val}) ->
  lists:member(Type, ?LOWER_BOUND_PRED);
validate_pred(upper, {Type, _Val}) ->
  lists:member(Type, ?UPPER_BOUND_PRED).

apply_pred(infinity, _Param) ->
  true;
apply_pred({Type, Val}, Param) ->
  to_predicate(Type, Param, Val);
apply_pred(Func, Param) when is_function(Func) ->
  Func(Param).

to_predicate(greater, Val1, Val2) -> Val1 > Val2;
to_predicate(greatereq, Val1, Val2) -> Val1 >= Val2;
to_predicate(lesser, Val1, Val2) -> Val1 < Val2;
to_predicate(lessereq, Val1, Val2) -> Val1 =< Val2;
to_predicate(equality, Val1, Val2) -> Val1 == Val2;
to_predicate(notequality, Val1, Val2) -> Val1 /= Val2.

%% ===================================================================
%% EUnit tests
%% ===================================================================
-ifdef(TEST).

update_entry_aux(Key, Op, Index) ->
  {ok, DownstreamOp} = downstream({update, {Key, Op}}, Index),
  {ok, Index2} = update(DownstreamOp, Index),
  Index2.

new_test() ->
  ?assertEqual({gb_trees:empty(), dict:new()}, new()).

update_test() ->
  Index1 = new(),
  BObjType = antidote_crdt_register_lww,
  IndexValType = antidote_crdt_register_lww,
  Update1 = [{bound_obj, BObjType, {assign, bobj1}}, {index_val, IndexValType, {assign, "col"}}],
  {ok, DownstreamOp} = downstream({update, {key1, Update1}}, Index1),
  ?assertMatch({update, {key1,
    [{bound_obj, BObjType, {_TS1, bobj1}}, {index_val, IndexValType, {_TS2, "col"}}]}}, DownstreamOp),
  {ok, Index2} = update(DownstreamOp, Index1),
  ?assertEqual([{"col", [bobj1]}], value(Index2)).

update2_test() ->
  Index1 = new(),
  BObjType = antidote_crdt_register_lww,
  IndexValType1 = antidote_crdt_set_aw,
  IndexValType2 = antidote_crdt_counter_pn,
  Update1 = [{bound_obj, BObjType, {assign, bobj1}}, {index_val, IndexValType1, {add, <<"elem">>}}],
  Update2 = [{bound_obj, BObjType, {assign, bobj1}}, {index_val, IndexValType2, {increment, 5}}],
  Index2 = update_entry_aux(key1, Update1, Index1),
  Index3 = update_entry_aux(key1, Update2, Index1),

  ?assertEqual([{[<<"elem">>], [bobj1]}], value(Index2)),
  ?assertEqual([{5, [bobj1]}], value(Index3)).

update3_test() ->
  Index1 = new(),
  BObjType = antidote_crdt_register_lww,
  RegType = antidote_crdt_register_lww,
  Update1 = [{bound_obj, BObjType, {assign, bobj1}}],
  Index2 = update_entry_aux(key1, Update1, Index1),

  Update2 = [{bound_obj, BObjType, {assign, bobj1_2}}],
  Index3 = update_entry_aux(key1, Update2, Index2),

  Update3 = [{index_val, RegType, {assign, "col"}}],
  Index4 = update_entry_aux(key1, Update3, Index3),

  ?assertEqual([], value(Index2)),
  ?assertEqual([], value(Index3)),
  ?assertEqual([{"col", [bobj1_2]}], value(Index4)).

remove_test() ->
  RegType = antidote_crdt_register_lww,
  BObjType = antidote_crdt_register_lww,
  Index1 = new(),
  Update1 = [{bound_obj, BObjType, {assign, bobj1}}, {index_val, RegType, {assign, "col"}}],
  Update2 = [{bound_obj, BObjType, {assign, bobj2}}, {index_val, RegType, {assign, "col2"}}],
  Update3 = [{bound_obj, BObjType, {assign, bobj3}}, {index_val, RegType, {assign, "col"}}],
  Index2 = update_entry_aux(key1, Update1, Index1),
  Index3 = update_entry_aux(key2, Update2, Index2),
  Index4 = update_entry_aux(key3, Update3, Index3),

  Removes = [key1, key3],
  {ok, DS} = downstream({remove, Removes}, Index4),
  {ok, Index5} = update(DS, Index4),
  FinalRes = [{"col2", [bobj2]}],
  ?assertEqual(FinalRes, value(Index5)).

concurrent_test() ->
  RegType = antidote_crdt_register_lww,
  BObjType = antidote_crdt_register_lww,
  Index1 = new(),
  Update1 = [{bound_obj, BObjType, {assign, bobj1}}, {index_val, RegType, {assign, "col"}}],
  Update2 = [{bound_obj, BObjType, {assign, bobj2}}, {index_val, RegType, {assign, "col2"}}],
  Index2 = update_entry_aux(key1, Update1, Index1),
  Index3 = update_entry_aux(key2, Update2, Index2),

  %% Node 1
  Update3 = [{bound_obj, BObjType, {assign, bobj2}}, {index_val, RegType, {assign, "col"}}],
  {ok, DownSN1} = downstream({update, {key2, Update3}}, Index3),
  {ok, IndexN1} = update(DownSN1, Index3),

  %% Node 2
  {ok, DownSN2} = downstream({remove, key2}, Index3),
  {ok, IndexN2} = update(DownSN2, Index3),

  %% Node 3
  Update4 = [{bound_obj, BObjType, {assign, bobj3}}, {index_val, RegType, {assign, "col2"}}],
  {ok, DownSN3} = downstream({update, {key3, Update4}}, Index3),
  {ok, IndexN3} = update(DownSN3, Index3),

  %% Merge
  {ok, MIndexN1_1} = update(DownSN2, IndexN1),
  {ok, MIndexN1_2} = update(DownSN3, MIndexN1_1),

  {ok, MIndexN2_1} = update(DownSN3, IndexN2),
  {ok, MIndexN2_2} = update(DownSN1, MIndexN2_1),

  {ok, MIndexN3_1} = update(DownSN1, IndexN3),
  {ok, MIndexN3_2} = update(DownSN2, MIndexN3_1),

  FinalRes = [{"col", [bobj1]}, {"col2", [bobj3]}],
  ?assertEqual(FinalRes, value(MIndexN1_2)),
  ?assertEqual(FinalRes, value(MIndexN2_2)),
  ?assertEqual(FinalRes, value(MIndexN3_2)).

equal_test() ->
  Index1 = new(),
  RegType = antidote_crdt_register_lww,
  CounterType = antidote_crdt_counter_pn,
  BObjType = antidote_crdt_register_lww,
  Update1 = [{bound_obj, BObjType, {assign, bobj1}}, {index_val, RegType, {assign, "col1"}}],
  Update2 = [{bound_obj, BObjType, {assign, bobj1}}, {index_val, RegType, {assign, "col2"}}],
  Update3 = [{bound_obj, BObjType, {assign, bobj1}}, {index_val, CounterType, {increment, 1}}],

  {ok, DownstreamOp1} = downstream({update, {key1, Update1}}, Index1),
  {ok, DownstreamOp2} = downstream({update, {key1, Update2}}, Index1),
  {ok, DownstreamOp3} = downstream({update, {key1, Update3}}, Index1),
  {ok, Index2} = update(DownstreamOp1, Index1),
  {ok, Index3} = update(DownstreamOp2, Index1),
  {ok, Index4} = update(DownstreamOp3, Index1),
  ?assertEqual(true, equal(Index1, Index1)),
  ?assertEqual(true, equal(Index2, Index2)),
  ?assertEqual(false, equal(Index1, Index2)),
  ?assertEqual(false, equal(Index2, Index3)),
  ?assertEqual(false, equal(Index2, Index4)).

range_test() ->
  Index1 = new(),
  RegType = antidote_crdt_register_lww,
  BObjType = antidote_crdt_register_lww,
  GenerateUpd =
    fun(Val) ->
      [{bound_obj, BObjType, {assign, list_to_atom("bobj" ++ integer_to_list(Val))}}, {index_val, RegType, {assign, Val}}]
    end,

  Updates = [
    {"col1", GenerateUpd(1)}, {"col2", GenerateUpd(2)},
    {"col3", GenerateUpd(3)}, {"col4", GenerateUpd(4)},
    {"col5", GenerateUpd(5)}, {"col6", GenerateUpd(6)}
  ],
  {ok, DownstreamOp1} = downstream({update, Updates}, Index1),
  {ok, Index2} = update(DownstreamOp1, Index1),
  LowerPred1 = {greatereq, 3},
  UpperPred1 = {lesser, 6},
  ?assertEqual([], value({range, {LowerPred1, UpperPred1}}, Index1)),
  ?assertEqual([{3, [bobj3]}, {4, [bobj4]}, {5, [bobj5]}], value({range, {LowerPred1, UpperPred1}}, Index2)).

is_operation_test() ->
  Op1 = {update, {k, [{index_val, antidote_crdt_register_lww, {assign, v}}]}},
  Op2 = {remove, {k, [{index_val, antidote_crdt_flag_ew, {enable, {}}}]}},
  Op3 = {update, {k, [{index_val, antidote_crdt_counter_pn, {increment, 1}}]}},
  Op4 = {remove, {k, none}},
  Op5 = {update, {k, [{index_val, antidote_crdt_set_aw, {assign, v}}]}},
  Op6 = {range, pred1, pred2},
  Op7 = {get, key},
  Op8 = {lookup, key},
  Op9 = {update, {k, antidote_crdt_register_lww, {assign, v}}},

  ?assertEqual(true, is_operation(Op1)),
  ?assertEqual(true, is_operation(Op2)),
  ?assertEqual(true, is_operation(Op3)),
  ?assertEqual(true, is_operation(Op4)),
  ?assertEqual(false, is_operation(Op5)),
  ?assertEqual(false, is_operation(Op6)),
  ?assertEqual(true, is_operation(Op7)),
  ?assertEqual(true, is_operation(Op8)),
  ?assertEqual(false, is_operation(Op9)).

-endif.