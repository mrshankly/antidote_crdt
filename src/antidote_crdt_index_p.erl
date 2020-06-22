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
%% @doc module antidote_crdt_index_p - A primary index CRDT
%%
%% An operation-based CRDT that acts as a basic index structure, by
%% mapping raw values to AntidoteDB keys. It also exports update
%% operations to add and to delete (i.e. reset) index entries.
%% It keeps one data structure, the index itself, that stores index
%% entries in the form:
%%   pk_value -> bound_obj
%%
%% , where pk_value is the raw primary key value, and bound_obj is
%% a register CRDT that stores the AntidoteDB key, respectively.
%%
%% This data type uses the Erlang's gb_trees to store index entries.
%% It was specially designed to support the Antidote Query Language
%% (AQL) system.
%% -------------------------------------------------------------------

-module(antidote_crdt_index_p).
-behaviour(antidote_crdt).

-define(BOBJ_DT, antidote_crdt_register_lww).

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

-export_type([antidote_crdt_index_p/0,
              antidote_crdt_index_p_op/0,
              antidote_crdt_index_p_query/0]).

-type antidote_crdt_index_p() :: indextree().
-type indextree() :: gb_trees:tree(Key::term(), Key::term()).

-type pred_type() :: greater | greatereq | lesser | lessereq | equality | notequality.
-type pred_arg() :: number().
-type predicate() :: {pred_type(), pred_arg()} | infinity.

-type antidote_crdt_index_p_query() :: {range, {predicate(), predicate()} | predicate()} |
                                       {get, term()}.

-type antidote_crdt_index_p_op() :: {update, nested_op()} |
                                    {update, [nested_op()]} |
                                    {remove, remove_op()} |
                                    {remove, [remove_op()]}.
-type nested_op() :: {Key::term(), Op::term()}.
-type remove_op() :: Key::term().

-type index_effect() :: {update, nested_downstream()} |
                        {update, [nested_downstream()]} |
                        {remove, remove_downstream()} |
                        {remove, [remove_downstream()]}.
-type nested_downstream() :: {Key::term(), Op::term()}.
-type remove_downstream() :: {Key::term(), none} | {Key::term(), Op::term()}.

-type key_not_found() :: {error, key_not_found}.
-type wrong_predicate() :: erlang:throw(string()).
-type value_output() :: [{term(), term()}] | {term(), term()} |
                        key_not_found() |
                        wrong_predicate().

-spec new() -> antidote_crdt_index_p().
new() ->
  gb_trees:empty().

-spec value(antidote_crdt_index_p()) -> value_output().
value(Index) ->
  to_value(Index).

-spec value(antidote_crdt_index_p_query(), antidote_crdt_index_p()) -> value_output().
value({range, {equality, Val}}, Index) ->
  value({get, Val}, Index);
value({range, {notequality, _Val} = Pred}, Index) ->
  Iterator = gb_trees:iterator(Index),
  iterate_and_filter(Pred, gb_trees:next(Iterator), []);
value({range, {LowerPred, UpperPred}}, Index) ->
  case validate_pred(lower, LowerPred) andalso validate_pred(upper, UpperPred) of
    true ->
      Iterator = case LowerPred of
                   infinity ->
                     gb_trees:iterator(Index);
                   _ ->
                     iterator_from_predicate(LowerPred, Index)
                 end,
      iterate_and_filter(UpperPred, gb_trees:next(Iterator), []);
    false ->
      throw(lists:flatten(?WRONG_PRED({LowerPred, UpperPred})))
  end;
value({get, Key}, Index) ->
  case fetch_tree_key(Key, Index, undefined) of
    undefined ->
      {error, key_not_found};
    Value ->
      case entry_value(Value) of
        none ->
          {error, key_not_found};
        {ok, Val} ->
          {Key, Val}
      end
  end.

-spec downstream(antidote_crdt_index_p_op(), antidote_crdt_index_p()) -> {ok, index_effect()}.
downstream({update, {Key, Op}}, Index) ->
  CurrentValue = fetch_tree_key(Key, Index, new_entry()),
  {ok, DownstreamOp} = generate_downstream_update(Op, CurrentValue),
  {ok, {update, {Key, DownstreamOp}}};
downstream({update, Ops}, Index) when is_list(Ops) ->
  {ok, {update, lists:map(fun(Op) -> {ok, DSOp} = downstream({update, Op}, Index), DSOp end, Ops)}};
downstream({remove, Ops}, Index) when is_list(Ops) ->
  {ok, {remove, lists:map(fun(Op) -> {ok, DSOp} = downstream({remove, Op}, Index), DSOp end, Ops)}};
downstream({remove, Key}, Index) ->
  DownstreamOp = generate_downstream_remove(Key, Index),
  {ok, {remove, DownstreamOp}}.

-spec update(index_effect(), antidote_crdt_index_p()) -> {ok, antidote_crdt_index_p()}.
update({update, {Key, Op}}, Index) ->
  CurrEntry = fetch_tree_key(Key, Index, undefined),
  NewEntry = apply_op(Op, CurrEntry),
  case CurrEntry == NewEntry of
    true ->
      {ok, Index};
    false ->
      NewIndex =
        case CurrEntry of
          undefined ->
            gb_trees:insert(Key, NewEntry, Index);
          _ ->
            gb_trees:update(Key, NewEntry, Index)
        end,
      {ok, NewIndex}
  end;
update({update, Ops}, Index) when is_list(Ops) ->
  apply_ops(Ops, Index);
update({remove, {_Key, none}}, Index) ->
  {ok, Index};
update({remove, {Key, Op}}, Index) ->
  update({update, {Key, Op}}, Index);
update({remove, Ops}, Index) when is_list(Ops) ->
  apply_ops(Ops, Index).

-spec equal(antidote_crdt_index_p(), antidote_crdt_index_p()) -> boolean().
equal(Index1, Index2) ->
  gb_trees:size(Index1) =:= gb_trees:size(Index2) andalso
    rec_equals(Index1, Index2).

-define(TAG, 101).
-define(V1_VERS, 1).

-spec to_binary(antidote_crdt_index_p()) -> binary().
to_binary(Index) ->
  <<?TAG:8/integer, ?V1_VERS:8/integer, (term_to_binary(Index))/binary>>.

-spec from_binary(binary()) -> {ok, antidote_crdt_index_p()}.
from_binary(<<?TAG:8/integer, ?V1_VERS:8/integer, Bin/binary>>) ->
  {ok, binary_to_term(Bin)}.

-spec is_operation(term()) -> boolean().
is_operation(Operation) ->
  case Operation of
    {range, {_LowerPred, _UpperPred}} ->
      true;
    {get, _Key} ->
      true;
    {update, {_Key, Op}} ->
      is_operation0(Op);
    {remove, {_Key, Op}} ->
      (Op == none orelse is_operation0(Op));
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
new_entry() ->
  ?BOBJ_DT:new().

to_value(IndexTree) ->
  Iter = gb_trees:iterator(IndexTree),
  to_value(gb_trees:next(Iter), []).
to_value({Key, Value, Iter2}, Acc) ->
  case entry_value(Value) of
    none ->
      to_value(gb_trees:next(Iter2), Acc);
    {ok, Val} ->
      NewAcc = lists:append(Acc, [{Key, Val}]),
      to_value(gb_trees:next(Iter2), NewAcc)
  end;
to_value(none, Acc) ->
  Acc.

entry_value(Entry) ->
  case is_bottom(?BOBJ_DT, Entry) of
    true ->
      none;
    false ->
      {ok, ?BOBJ_DT:value(Entry)}
  end.

apply_op(Op, IndexEntry) ->
  Entry0 = case IndexEntry of
             undefined -> new_entry();
             _Else -> IndexEntry
           end,

  {ok, StateUpdated} = apply_update(Op, Entry0),
  StateUpdated.

generate_downstream_update(Op, BObjCRDT) ->
  ?BOBJ_DT:downstream(Op, BObjCRDT).

generate_downstream_remove(Key, Index) ->
  Entry = case gb_trees:lookup(Key, Index) of
            {value, CRDT} -> CRDT;
            none -> new_entry()
          end,
  ResetOp = {reset, {}},

  DownstreamEffect = generate_downstream_reset(ResetOp, ?BOBJ_DT, Entry),
  {Key, DownstreamEffect}.

%% TODO keep the 'Op' in case LWW-register starts to support reset operations
generate_downstream_reset(_Op, Type, State) ->
  {ok, DS} = Type:downstream({assign, <<>>}, State),
  DS.

apply_update(Op, BObjCRDT) ->
  ?BOBJ_DT:update(Op, BObjCRDT).

is_bottom(Type, State) ->
  Val1 = Type:value(State),
  Val2 = Type:value(Type:new()),
  (erlang:function_exported(Type, is_bottom, 1) andalso Type:is_bottom(State))
    orelse Val1 == Val2.

is_operation0(Op) -> ?BOBJ_DT:is_operation(Op).

apply_ops([], Index) ->
  {ok, Index};
apply_ops([Op | Rest], Index) ->
  {ok, Index2} = update(Op, Index),
  apply_ops(Rest, Index2).

rec_equals(IndexTree1, IndexTree2) ->
  IdxIter1 = gb_trees:iterator(IndexTree1),
  rec_equals0(gb_trees:next(IdxIter1), IndexTree2) =:= true.

rec_equals0({Key, Value, Iter2}, IndexTree2) ->
  IsEqual = case gb_trees:lookup(Key, IndexTree2) of
              none ->
                false;
              {value, Value2} ->
                Value == Value2
            end,
  case IsEqual of
    false ->
      false;
    true ->
      rec_equals0(gb_trees:next(Iter2), IndexTree2)
  end;
rec_equals0(none, _IndexTree2) ->
  true.

distinct([]) ->
  true;
distinct([X | Xs]) ->
  not lists:member(X, Xs) andalso distinct(Xs).

iterator_from_predicate(LowerPred, Tree) ->
  iterator_from_lower_bound(LowerPred, gb_trees:iterator(Tree)).

iterator_from_lower_bound(LowerPred, Iterator) ->
  case gb_trees:next(Iterator) of
    none ->
      Iterator;
    {Key, _Value, Iter} ->
      case apply_pred(LowerPred, Key) of
        true -> Iterator;
        false -> iterator_from_lower_bound(LowerPred, Iter)
      end
  end.

iterate_and_filter(_Predicate, none, Acc) ->
  Acc;
iterate_and_filter(Bound, {Key, Value, Iter}, Acc) ->
  NewAcc = case apply_pred(Bound, Key) of
             true ->
               case entry_value(Value) of
                 none ->
                   Acc;
                 {ok, Val} ->
                   lists:append(Acc, [{Key, Val}])
               end;
             false ->
               Acc
           end,
  iterate_and_filter(Bound, gb_trees:next(Iter), NewAcc).

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

fetch_tree_key(Key, Tree, Default) ->
  case gb_trees:lookup(Key, Tree) of
    {value, Value} -> Value;
    none -> Default
  end.

%% ===================================================================
%% EUnit tests
%% ===================================================================
-ifdef(TEST).

update_entry_aux(Key, Op, Index) ->
  {ok, DownstreamOp} = downstream({update, {Key, Op}}, Index),
  {ok, Index2} = update(DownstreamOp, Index),
  Index2.

new_test() ->
  ?assertEqual([], value(new())).

update_test() ->
  Index1 = new(),
  BoundObj = {key, type, bucket},
  {ok, DownstreamOp} = downstream({update, {key, {assign, BoundObj}}}, Index1),
  ?assertMatch({update, {key, {_, BoundObj}}}, DownstreamOp),
  {ok, Index2} = update(DownstreamOp, Index1),

  Tree = value(Index2),
  Entry = BoundObj,
  ?assertEqual([{key, Entry}], Tree).

update2_test() ->
  Index1 = new(),
  BObj1 = {key, type, bucket1},
  BObj2 = {key, type, bucket2},
  Index2 = update_entry_aux(key, {assign, BObj1}, Index1),
  Index3 = update_entry_aux(key, {assign, BObj2}, Index1),

  Tree1 = value(Index2),
  Entry1 = BObj1,

  Tree2 = value(Index3),
  Entry2 = BObj2,

  ?assertEqual([{key, Entry1}], Tree1),
  ?assertEqual([{key, Entry2}], Tree2).

remove_test() ->
  Index1 = new(),
  BObj1 = {key1, type, bucket1},
  BObj2 = {key2, type, bucket1},
  BObj3 = {key3, type, bucket1},
  Index2 = update_entry_aux(key1, {assign, BObj1}, Index1),
  Index3 = update_entry_aux(key2, {assign, BObj2}, Index2),
  Index4 = update_entry_aux(key3, {assign, BObj3}, Index3),

  Removes = [key1, key3],
  {ok, DS} = downstream({remove, Removes}, Index4),
  {ok, Index5} = update(DS, Index4),

  Tree = value(Index5),
  Entry = BObj2,
  FinalRes = [{key2, Entry}],
  ?assertEqual(FinalRes, Tree).

concurrent_test() ->
  Index1 = new(),
  BObj1 = {key1, type, bucket1},
  BObj2 = {key2, type, bucket1},
  BObj2_2 = {key2, type, bucket2},
  BObj3 = {key3, type, bucket1},
  Index2 = update_entry_aux(key1, {assign, BObj1}, Index1),
  Index3 = update_entry_aux(key2, {assign, BObj2}, Index2),

  %% Node 1
  {ok, DownSN1} = downstream({update, {key2, {assign, BObj2_2}}}, Index3),
  {ok, IndexN1} = update(DownSN1, Index3),

  %% Node 2
  {ok, DownSN2} = downstream({remove, key2}, Index3),
  {ok, IndexN2} = update(DownSN2, Index3),

  %% Node 3
  {ok, DownSN3} = downstream({update, {key3, {assign, BObj3}}}, Index3),
  {ok, IndexN3} = update(DownSN3, Index3),

  %% Merge
  {ok, MIndexN1_1} = update(DownSN2, IndexN1),
  {ok, MIndexN1_2} = update(DownSN3, MIndexN1_1),

  {ok, MIndexN2_1} = update(DownSN3, IndexN2),
  {ok, MIndexN2_2} = update(DownSN1, MIndexN2_1),

  {ok, MIndexN3_1} = update(DownSN1, IndexN3),
  {ok, MIndexN3_2} = update(DownSN2, MIndexN3_1),

  DefaultEntry = [
    {key1, BObj1},
    {key3, BObj3}
  ],

  FinalRes = DefaultEntry,
  ?assertEqual(FinalRes, value(MIndexN1_2)),
  ?assertEqual(FinalRes, value(MIndexN2_2)),
  ?assertEqual(FinalRes, value(MIndexN3_2)).

equal_test() ->
  Index1 = new(),
  {ok, DownstreamOp1} = downstream({update, {key1, {assign, bobj1}}}, Index1),
  {ok, DownstreamOp2} = downstream({update, {key1, {assign, bobj2}}}, Index1),
  {ok, Index2} = update(DownstreamOp1, Index1),
  {ok, Index3} = update(DownstreamOp2, Index1),
  ?assertEqual(true, equal(Index1, Index1)),
  ?assertEqual(true, equal(Index2, Index2)),
  ?assertEqual(false, equal(Index1, Index2)),
  ?assertEqual(false, equal(Index2, Index3)).

range_test() ->
  Index1 = new(),
  Updates = [
    {1, {assign, bobj}}, {2, {assign, bobj}},
    {3, {assign, bobj}}, {4, {assign, bobj}},
    {5, {assign, bobj}}, {6, {assign, bobj}}
  ],
  {ok, DownstreamOp1} = downstream({update, Updates}, Index1),
  {ok, Index2} = update(DownstreamOp1, Index1),
  LowerPred1 = {greatereq, 3},
  UpperPred1 = {lesser, 6},
  Result1 = value({range, {LowerPred1, UpperPred1}}, Index1),
  Result2 = value({range, {LowerPred1, UpperPred1}}, Index2),

  DefaultEntry = bobj,
  ?assertEqual([], Result1),
  ?assertEqual([{3, DefaultEntry}, {4, DefaultEntry}, {5, DefaultEntry}], Result2).

is_operation_test() ->
  Op1 = {update, {k, {assign, {k, t, b}}}},
  Op2 = {remove, {k, none}},
  Op3 = {range, pred1, pred2},
  Op4 = {range, {pred1, pred2}},
  Op5 = {get, key},
  Op6 = {lookup, key},

  ?assertEqual(true, is_operation(Op1)),
  ?assertEqual(true, is_operation(Op2)),
  ?assertEqual(false, is_operation(Op3)),
  ?assertEqual(true, is_operation(Op4)),
  ?assertEqual(true, is_operation(Op5)),
  ?assertEqual(false, is_operation(Op6)).

-endif.