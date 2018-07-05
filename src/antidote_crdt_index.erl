%% -------------------------------------------------------------------
%%
%% Copyright (c) 2014 SyncFree Consortium.  All Rights Reserved.
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
%% KIND, either express or implied.  See the License for the
%% specific language governing permissions and limitations
%% under the License.
%%
%% ------------------------------------------------------------------

%% ------------------------------------------------------------------
%% @author pedrolopes
%% @doc module antidote_crdt_index- An index CRDT
%%
%% An operation-based CRDT, very similar to antidote_crdt_map_go with
%% the particularity that contains a remove operation to delete index
%% entries.
%% It keeps two structures, the index map and the indirection map:
%% - the index map stores index entries, each entry maps an indexed
%%   value to a set of primary keys;
%% - the indirection map stores the inverted bindings between primary
%%   keys and indexed values and has a similar behaviour as the
%%   map in the antidote_crdt_map_go.
%%
%% This data type uses the Erlang's gb_trees to store index entries
%% and a dict to store the indirection map.
%% ------------------------------------------------------------------

-module(antidote_crdt_index).
-behaviour(antidote_crdt).

-define(LOWER_BOUND_PRED, [greater, greatereq]).
-define(UPPER_BOUND_PRED, [lesser, lessereq]).
-define(WRONG_PRED(Preds), io_lib:format("Some of the predicates don't respect a range query: ~p", [Preds])).
-define(BCOUNTER_DT, antidote_crdt_counter_b).

%% API
-export([new/0,
         new/1,
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

-type index() :: {index_type(), indexmap(), indirectionmap()}.
-type index_type() :: atom().
-type gb_tree_node() :: nil | {_, _, _, _}.
-type indexmap() :: {non_neg_integer(), gb_tree_node()}.
-type indirectionmap() :: dict:dict({Key::term(), Type::atom()}, NestedState::term()).

-type pred_type() :: greater | greatereq | lesser | lessereq.
-type pred_arg() :: number().
-type predicate() :: {pred_type(), pred_arg()} | infinity.

-type index_query() :: {range, {predicate(), predicate()}} |
                       {get, term()} |
                       {lookup, term()}.

-type index_op() :: {update, nested_op()} | {update, [nested_op()]}.
-type nested_op() :: {{Key::term(), Type::atom()}, Op::term()}.
-type index_effect() :: {update, nested_downstream()} | {update, [nested_downstream()]}.
-type nested_downstream() :: {{Key::term(), Type::atom()}, Op::term()}.

-type invalid_type() :: {error, wrong_type}.
-type key_not_found() :: {error, key_not_found}.
-type wrong_predicate() :: erlang:throw(string()).
-type value_output() :: [{term(), term()}] | {term(), term()} |
                        invalid_type() |
                        key_not_found() |
                        wrong_predicate().

-spec new() -> index().
new() ->
    {undefined, gb_trees:empty(), dict:new()}.

-spec new(term()) -> index().
new(Type) ->
    case antidote_crdt:is_type(Type) of
        true ->
            {Type, gb_trees:empty(), dict:new()};
        false ->
            new()
    end.

-spec value(index()) -> value_output().
value({_Type, IndexTree, _Indirection}) ->
    gb_trees:to_list(IndexTree).

-spec value(index_query(), index()) -> value_output().
value({range, {LowerPred, UpperPred}}, {_Type, IndexTree, _Indirection}) ->
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
value({get, Key}, {_Type, IndexTree, _Indirection}) ->
    case gb_trees:lookup(Key, IndexTree) of
        {value, Value} ->
            {Key, Value};
        none ->
            {error, key_not_found}
    end;
value({lookup, Key}, {Type, _IndexTree, Indirection} = Index) ->
    case dict:find(Key, Indirection) of
        {ok, CRDTValue} ->
            Value = Type:value(CRDTValue),
            value({get, Value}, Index);
        error ->
            {error, key_not_found}
    end.

-spec downstream(index_op(), index()) -> {ok, index_effect()} | invalid_type().
downstream({update, {Type, Key, Op}}, {_Type, _IndexTree, Indirection} = Index) ->
    case index_type(Index, Type) of
        Type ->
            CurrentValue = case dict:is_key(Key, Indirection) of
                               true ->
                                   dict:fetch(Key, Indirection);
                               false ->
                                   Type:new()
                           end,
            {ok, DownstreamOp} = Type:downstream(Op, CurrentValue),
            {ok, {update, {Type, Key, DownstreamOp}}};
        _Else ->
            {error, wrong_type}
    end;
downstream({update, Ops}, Index) when is_list(Ops) ->
    {ok, {update, lists:map(fun(Op) -> {ok, DSOp} = downstream({update, Op}, Index), DSOp end, Ops)}};
downstream({remove, {Type, Key}}, Index) ->
    DownstreamOp = generate_downstream_remove({Type, Key}, Index),
    {ok, {remove, DownstreamOp}};
downstream({remove, Ops}, Index) when is_list(Ops) ->
    {ok, {remove, lists:map(fun(Op) -> {ok, DSOp} = downstream({remove, Op}, Index), DSOp end, Ops)}}.

-spec update(index_effect(), index()) -> {ok, index()}.
update({update, {Type, Key, Op}}, {_Type, IndexTree, Indirection}) ->
    {OldValue, NewValue} = apply_op(Key, Type, Op, Indirection),
    case OldValue == NewValue of
        true ->
            {ok, {Type, IndexTree, Indirection}};
        false ->
            NewIndirection = dict:store(Key, NewValue, Indirection),

            NewIndexTree = update_index(get_value(Type, OldValue), get_value(Type, NewValue), Key, IndexTree),
            {ok, {Type, NewIndexTree, NewIndirection}}
    end;
update({update, Ops}, Index) ->
    apply_ops(Ops, Index);
update({remove, {_Type, _Key, none}}, Index) ->
    {ok, Index};
update({remove, {Type, Key, Op}}, {_Type, IndexTree, Indirection}) ->
    {OldValue, NewValue} = apply_op(Key, Type, Op, Indirection),
    case OldValue == NewValue of
        true ->
            {ok, {Type, IndexTree, Indirection}};
        false ->
            NewIndirection = dict:store(Key, NewValue, Indirection),
            NewIndexTree =
                case is_bottom(Type, NewValue) of
                    true ->
                        remove_entry(get_value(Type, OldValue), Key, IndexTree);
                    false ->
                        update_index(get_value(Type, OldValue), get_value(Type, NewValue), Key, IndexTree)
                end,
            {ok, {Type, NewIndexTree, NewIndirection}}
    end;
update({remove, Ops}, Index) ->
    apply_ops(Ops, Index).

-spec equal(index(), index()) -> boolean().
equal({Type1, IndexTree1, Indirection1}, {Type2, IndexTree2, Indirection2}) ->
    Type1 =:= Type2 andalso
    IndexTree1 =:= IndexTree2 andalso
    dict:size(Indirection1) =:= dict:size(Indirection2) andalso
    rec_equals(Type1, Indirection1, Indirection2).

-define(TAG, 101).
-define(V1_VERS, 1).

-spec to_binary(index()) -> binary().
to_binary(Index) ->
    <<?TAG:8/integer, ?V1_VERS:8/integer, (term_to_binary(Index))/binary>>.

-spec from_binary(binary()) -> {ok, index()}.
from_binary(<<?TAG:8/integer, ?V1_VERS:8/integer, Bin/binary>>) ->
    {ok, binary_to_term(Bin)}.

-spec is_operation(term()) -> boolean().
is_operation(Operation) ->
    case Operation of
        {update, {Type, _Key, Op}} ->
            antidote_crdt:is_type(Type)
                andalso Type:is_operation(Op);
        {remove, {Type, _Key, Op}} ->
            antidote_crdt:is_type(Type)
                andalso (Type:is_operation(Op) orelse Op == none);
        {OpType, Ops} when is_list(Ops) ->
            distinct([Key || {Key, _} <- Ops])
                andalso lists:all(fun(Op) -> is_operation({OpType, Op}) end, Ops);
        _ ->
            false
    end.

-spec require_state_downstream(term()) -> boolean().
require_state_downstream(_Op) ->
    true.

%% ===================================================================
%% Internal functions
%% ===================================================================
index_type({Type, _IndexTree, _Indirection}, Default) ->
    case Type of
        undefined -> Default;
        Default -> Type;
        _Else -> undefined
    end;
index_type({_IndexTree, Indirection}, Default) ->
    Keys = dict:fetch_keys(Indirection),
    Types = lists:foldl(
        fun({_Key, Type}, SetAcc) -> sets:add_element(Type, SetAcc) end,
        sets:new(), Keys),
    case sets:to_list(Types) of
        [Type] -> Type;
        [] -> Default;
        _Else -> undefined
    end.

update_index(OldEntryKey, NewEntryKey, EntryValue, IndexTree) ->
    Removed = remove_entry(OldEntryKey, EntryValue, IndexTree),

    %% The insert is much slower than the update in gb_trees.
    %% That's why we first lookup for an entry and, if it
    %% exists, we update it, instead of forcing to insert
    %% an already existing entry.
    case gb_trees:lookup(NewEntryKey, Removed) of
         {value, Set2} ->
             gb_trees:update(NewEntryKey, ordsets:add_element(EntryValue, Set2), Removed);
         none ->
             gb_trees:insert(NewEntryKey, ordsets:add_element(EntryValue, ordsets:new()), Removed)
    end.

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

apply_op(Key, Type, Op, Indirection) ->
    case dict:find(Key, Indirection) of
        {ok, Value} ->
            {ok, ValueUpdated} = Type:update(Op, Value),
            {Value, ValueUpdated};
        error ->
            NewCRDT = Type:new(),
            {ok, NewValueUpdated} = Type:update(Op, NewCRDT),
            {undefined, NewValueUpdated}
    end.

generate_downstream_remove({Type, Key}, {Type, _IndexTree, Indirection}) ->
    CurrentValue =
        case dict:is_key(Key, Indirection) of
            true ->
                dict:fetch(Key, Indirection);
            false ->
                Type:new()
        end,
    DownstreamEffect =
        case Type:is_operation({reset, {}}) of
            true ->
                {ok, _} = Type:downstream({reset, {}}, CurrentValue);
            false ->
                resolve_downstream(Type, CurrentValue)
        end,
    {Type, Key, DownstreamEffect};
generate_downstream_remove({Type, Key}, _) ->
    {Type, Key, none}.

%% A simple solver for CRDTs which do not have a reset operation.
resolve_downstream(antidote_crdt_register_lww = Type, State) ->
    {ok, DS} = Type:downstream({assign, <<>>}, State),
    DS;
%% This assumes there's only one actor updating the counter.
resolve_downstream(antidote_crdt_counter_b = Type, State) ->
    CounterV = calc_value(Type, Type:value(State)),
    {ok, DS} = Type:downstream({decrement, {CounterV, term}}, State),
    DS;
resolve_downstream(antidote_crdt_counter_pn = Type, State) ->
    CounterV = Type:value(State),
    {ok, DS} = Type:downstream({decrement, CounterV}, State),
    DS;
resolve_downstream(_, _) ->
    none.

is_bottom(Type, State) ->
    Val1 = calc_value(Type, Type:value(State)),
    Val2 = calc_value(Type, Type:value(Type:new())),
    (erlang:function_exported(Type, is_bottom, 1) andalso Type:is_bottom(State))
        orelse Val1 == Val2.

get_value(_Type, undefined) ->
    undefined;
get_value(Type, CRDTValue) ->
    Value = Type:value(CRDTValue),
    calc_value(Type, Value).

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

rec_equals(Type, Indirection1, Indirection2) ->
    IndList1 = dict:to_list(Indirection1),
    IndList2 = dict:to_list(Indirection2),
    Remaining = lists:dropwhile(fun({Key, Value}) ->
        case proplists:lookup(Key, IndList2) of
            none ->
                false;
            {Key, Value2} ->
                Type:equal(Value, Value2)
        end
    end, IndList1),
    length(Remaining) =:= 0.

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
    Func = to_predicate(Type, Val),
    Func(Param);
apply_pred(Func, Param) when is_function(Func) ->
    Func(Param).

to_predicate(greater, Val) -> fun(V) -> V > Val end;
to_predicate(greatereq, Val) -> fun(V) -> V >= Val end;
to_predicate(lesser, Val) -> fun(V) -> V < Val end;
to_predicate(lessereq, Val) -> fun(V) -> V =< Val end;
to_predicate(equality, Val) -> fun(V) -> V == Val end;
to_predicate(notequality, Val) -> fun(V) -> V /= Val end.

%% ===================================================================
%% EUnit tests
%% ===================================================================
-ifdef(TEST).

update_entry_aux(Type, Key, Op, Index) ->
    {ok, DownstreamOp} = downstream({update, {Type, Key, Op}}, Index),
    {ok, Index2} = update(DownstreamOp, Index),
    Index2.

new_test() ->
    ?assertEqual({undefined, gb_trees:empty(), dict:new()}, new()),
    ?assertEqual({undefined, gb_trees:empty(), dict:new()}, new(dummytype)),
    ?assertEqual({antidote_crdt_register_lww, gb_trees:empty(), dict:new()}, new(antidote_crdt_register_lww)).

update_test() ->
    Index1 = new(antidote_crdt_register_lww),
    {ok, DownstreamOp} = downstream({update, {antidote_crdt_register_lww, key1, {assign, "col"}}}, Index1),
    ?assertMatch({update, {antidote_crdt_register_lww, key1, {_TS, "col"}}}, DownstreamOp),
    {ok, Index2} = update(DownstreamOp, Index1),
    Set = ordsets:add_element(key1, ordsets:new()),
    ?assertEqual([{"col", Set}], value(Index2)).

update2_test() ->
    Index1 = new(),
    Index2 = update_entry_aux(antidote_crdt_set_aw, key1, {add, <<"elem">>}, Index1),
    Index3 = update_entry_aux(antidote_crdt_counter_pn, key1, {increment, 5}, Index1),

    Set = ordsets:add_element(key1, ordsets:new()),

    ?assertEqual([{[<<"elem">>], Set}], value(Index2)),
    ?assertEqual([{5, Set}], value(Index3)).

update3_test() ->
    Index1 = new(),
    Index2 = update_entry_aux(antidote_crdt_register_lww, key1, {assign, "col"}, Index1),
    Response = downstream({update, {antidote_crdt_counter_pn, key2, {assign, 2}}}, Index2),
    ?assertEqual({error, wrong_type}, Response).

remove_test() ->
    RegType = antidote_crdt_register_lww,
    Index1 = new(RegType),
    Index2 = update_entry_aux(RegType, key1, {assign, "col"}, Index1),
    Index3 = update_entry_aux(RegType, key2, {assign, "col2"}, Index2),
    Index4 = update_entry_aux(RegType, key3, {assign, "col"}, Index3),

    Removes = [
        {RegType, key1},
        {RegType, key3}
    ],
    {ok, DS} = downstream({remove, Removes}, Index4),
    {ok, Index5} = update(DS, Index4),
    FinalRes = [{"col2", [key2]}],
    ?assertEqual(FinalRes, value(Index5)).

concurrent_test() ->
    RegType = antidote_crdt_register_lww,
    Index1 = new(RegType),
    Index2 = update_entry_aux(RegType, key1, {assign, "col"}, Index1),
    Index3 = update_entry_aux(RegType, key2, {assign, "col2"}, Index2),

    %% Node 1
    {ok, DownSN1} = downstream({update, {RegType, key2, {assign, "col"}}}, Index3),
    {ok, IndexN1} = update(DownSN1, Index3),

    %% Node 2
    {ok, DownSN2} = downstream({remove, {RegType, key2}}, Index3),
    {ok, IndexN2} = update(DownSN2, Index3),

    %% Node 3
    {ok, DownSN3} = downstream({update, {RegType, key3, {assign, "col2"}}}, Index3),
    {ok, IndexN3} = update(DownSN3, Index3),

    %% Merge
    {ok, MIndexN1_1} = update(DownSN2, IndexN1),
    {ok, MIndexN1_2} = update(DownSN3, MIndexN1_1),

    {ok, MIndexN2_1} = update(DownSN3, IndexN2),
    {ok, MIndexN2_2} = update(DownSN1, MIndexN2_1),

    {ok, MIndexN3_1} = update(DownSN1, IndexN3),
    {ok, MIndexN3_2} = update(DownSN2, MIndexN3_1),

    Set1 = [key1],
    Set2 = [key3],
    FinalRes = [{"col", Set1}, {"col2", Set2}],
    ?assertEqual(FinalRes, value(MIndexN1_2)),
    ?assertEqual(FinalRes, value(MIndexN2_2)),
    ?assertEqual(FinalRes, value(MIndexN3_2)).

equal_test() ->
    Index1 = new(),
    {ok, DownstreamOp1} = downstream({update, {antidote_crdt_register_lww, key1, {assign, "col1"}}}, Index1),
    {ok, DownstreamOp2} = downstream({update, {antidote_crdt_register_lww, key1, {assign, "col2"}}}, Index1),
    {ok, DownstreamOp3} = downstream({update, {antidote_crdt_counter_pn, key1, {increment, 1}}}, Index1),
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
    Updates = [
        {antidote_crdt_register_lww, "col1", {assign, 1}}, {antidote_crdt_register_lww, "col2", {assign, 2}},
        {antidote_crdt_register_lww, "col3", {assign, 3}}, {antidote_crdt_register_lww, "col4", {assign, 4}},
        {antidote_crdt_register_lww, "col5", {assign, 5}}, {antidote_crdt_register_lww, "col6", {assign, 6}}
    ],
    {ok, DownstreamOp1} = downstream({update, Updates}, Index1),
    {ok, Index2} = update(DownstreamOp1, Index1),
    LowerPred1 = {greatereq, 3},
    UpperPred1 = {lesser, 6},
    ?assertEqual([], value({range, {LowerPred1, UpperPred1}}, Index1)),
    ?assertEqual([{3, ["col3"]}, {4, ["col4"]}, {5, ["col5"]}], value({range, {LowerPred1, UpperPred1}}, Index2)).

is_operation_test() ->
    Op1 = {update, {antidote_crdt_register_lww, k, {assign, v}}},
    Op2 = {remove, {antidote_crdt_flag_ew, k, {enable, {}}}},
    Op3 = {update, {antidote_crdt_counter_pn, k, {increment, 1}}},
    Op4 = {remove, {antidote_crdt_register_lww, k, none}},
    Op5 = {update, {antidote_crdt_set_aw, k, {assign, v}}},

    ?assertEqual(true, is_operation(Op1)),
    ?assertEqual(true, is_operation(Op2)),
    ?assertEqual(true, is_operation(Op3)),
    ?assertEqual(true, is_operation(Op4)),
    ?assertEqual(false, is_operation(Op5)).

-endif.