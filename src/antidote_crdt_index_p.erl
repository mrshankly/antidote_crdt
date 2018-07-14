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
%% @doc module antidote_crdt_index_p - A primary index CRDT
%%
%% An operation-based CRDT, very similar to antidote_crdt_map_go with
%% the particularity that contains a remove operation to delete index
%% entries.
%% It keeps one data structure, the index itself, that stores index
%% entries in the form:
%%   pk_value -> metadata_map
%%
%% , where pk_value is the primary key value, and metadata_map is a
%% map/dictionary that contains four elements:
%%   {bound_obj -> {key, type, bucket},
%%    state -> crdt_register_mv,
%%    version -> crdt_register_lww,
%%    refs -> [ref1, ..., refn]}
%%
%% Additionally, a primary index has an index policy (add-wins or
%% remove-wins) and a dependency policy (update-wins or delete-wins).
%%
%% This data type uses the Erlang's gb_trees to store index entries.
%% ------------------------------------------------------------------

-module(antidote_crdt_index_p).
-behaviour(antidote_crdt).

-define(BOBJ_DT, antidote_crdt_register_lww).
-define(STATE_DT, antidote_crdt_register_mv).
-define(VRS_DT, antidote_crdt_register_lww).
-define(REF_DT, antidote_crdt_register_lww).
-define(bound_obj_key, {bound_obj, ?BOBJ_DT}).
-define(state_key, {state, ?STATE_DT}).
-define(version_key, {version, ?VRS_DT}).
-define(refs_key, {refs, ?REF_DT}).

-define(LOWER_BOUND_PRED, [greater, greatereq]).
-define(UPPER_BOUND_PRED, [lesser, lessereq]).
-define(WRONG_PRED(Preds), io_lib:format("Some of the predicates don't respect a range query: ~p", [Preds])).
-define(BCOUNTER_DT, antidote_crdt_counter_b).

%% API
-export([new/0,
         new/2,
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

-type antidote_crdt_index_p() :: {policy(), policy(), indexmap()}.
-type policy() :: add | remove.
-type entry() :: map().
-type gb_tree_node() :: nil | {_, entry(), _, _}.
-type indexmap() :: {non_neg_integer(), gb_tree_node()}.

-type pred_type() :: greater | greatereq | lesser | lessereq | equality | notequality.
-type pred_arg() :: number().
-type predicate() :: {pred_type(), pred_arg()} | infinity.

-type antidote_crdt_index_p_query() :: {range, {predicate(), predicate()} | predicate()} |
                                       {get, term()} |
                                       {policies, {}}.

-type antidote_crdt_index_p_op() :: {update, nested_op()} |
                                    {update, [nested_op()]} |
                                    {remove, remove_op()} |
                                    {remove, [remove_op()]} |
                                    {set, set_op()}.
-type nested_op() :: {Key::term(), Op::term()}.
-type remove_op() :: Key::term().
-type set_op() :: {index_policy, policy()} | {dep_policy, policy()}.

-type index_effect() :: {update, nested_downstream()} |
                        {update, [nested_downstream()]} |
                        {remove, remove_downstream()} |
                        {remove, [remove_downstream()]} |
                        {set, set_downstream()}.
-type nested_downstream() :: {Key::term(), Op::term()}.
-type remove_downstream() :: {Key::term(), none} | {Key::term(), map()}.
-type set_downstream() :: {index_policy, policy()} | {dep_policy, policy()}.

-type invalid_type() :: {error, wrong_type}.
-type key_not_found() :: {error, key_not_found}.
-type invalid_policy() :: {error, {invalid_index_policy, term()}}.
-type wrong_predicate() :: erlang:throw(string()).
-type value_output() :: [{term(), term()}] | {term(), term()} |
                        invalid_type() |
                        key_not_found() |
                        wrong_predicate().

-spec new() -> antidote_crdt_index_p().
new() ->
    {undefined, undefined, gb_trees:empty()}.

-spec new(policy(), policy()) -> antidote_crdt_index_p().
new(IndexPolicy, DepPolicy) ->
    {IndexPolicy, DepPolicy, gb_trees:empty()}.

-spec value(antidote_crdt_index_p()) -> value_output().
value({IndexPolicy, DepPolicy, IndexTree}) ->
    {IndexPolicy, DepPolicy, to_value(IndexTree)}.

-spec value(antidote_crdt_index_p_query(), antidote_crdt_index_p()) -> value_output().
value({range, {equality, Val}}, Index) ->
    value({get, Val}, Index);
value({range, {notequality, _Val} = Pred}, {_IndexPolicy, _DepPolicy, IndexTree}) ->
    iterate_and_filter({Pred, [key]}, gb_trees:iterator(IndexTree), []);
value({range, {LowerPred, UpperPred}}, {_IndexPolicy, _DepPolicy, IndexTree}) ->
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
value({get, Key}, {_IndexPolicy, _DepPolicy, IndexTree}) ->
    case fetch_tree_key(Key, IndexTree, undefined) of
        undefined ->
            {error, key_not_found};
        Value ->
            case entry_value(Value) of
                none ->
                    {error, key_not_found};
                {ok, Val} ->
                    {Key, Val}
            end
    end;
value({policies, {}}, {IndexPolicy, DepPolicy, _IndexTree}) ->
    {IndexPolicy, DepPolicy}.

-spec downstream(antidote_crdt_index_p_op(), antidote_crdt_index_p()) ->
    {ok, index_effect()} | invalid_type() | invalid_policy().
downstream({update, {Key, Op}}, {_IndexPolicy, _DepPolicy, IndexTree}) ->
    CurrentValue = fetch_tree_key(Key, IndexTree, new_entry()),
    {ok, DownstreamOp} = generate_downstream_update(Op, CurrentValue),
    {ok, {update, {Key, DownstreamOp}}};
downstream({update, Ops}, Index) when is_list(Ops) ->
    {ok, {update, lists:map(fun(Op) -> {ok, DSOp} = downstream({update, Op}, Index), DSOp end, Ops)}};
downstream({remove, Ops}, Index) when is_list(Ops) ->
    {ok, {remove, lists:map(fun(Op) -> {ok, DSOp} = downstream({remove, Op}, Index), DSOp end, Ops)}};
downstream({remove, Key}, Index) ->
    DownstreamOp = generate_downstream_remove(Key, Index),
    {ok, {remove, DownstreamOp}};
downstream({set, {index_policy, NewIndexPolicy}}, {CurrIndexPolicy, _DepPolicy, _IndexTree}) ->
    case set_policy(CurrIndexPolicy, NewIndexPolicy) of
        error -> {error, {invalid_index_policy, NewIndexPolicy}};
        _Else -> {ok, {set, {index_policy, NewIndexPolicy}}}
    end;
downstream({set, {dep_policy, NewDepPolicy}}, {_IndexPolicy, CurrDepPolicy, _IndexTree}) ->
    case set_policy(CurrDepPolicy, NewDepPolicy) of
        error -> {error, {invalid_dep_policy, NewDepPolicy}};
        _Else -> {ok, {set, {dep_policy, NewDepPolicy}}}
    end.

-spec update(index_effect(), antidote_crdt_index_p()) -> {ok, antidote_crdt_index_p()}.
update({update, {Key, Op}}, {IndexPolicy, DepPolicy, IndexTree}) ->
    CurrEntry = fetch_tree_key(Key, IndexTree, undefined),
    NewEntry = apply_op(Op, CurrEntry),
    case CurrEntry == NewEntry of
        true ->
            {ok, {IndexPolicy, DepPolicy, IndexTree}};
        false ->
            NewIndexTree = case CurrEntry of
                               undefined ->
                                   gb_trees:insert(Key, NewEntry, IndexTree);
                               _ ->
                                   gb_trees:update(Key, NewEntry, IndexTree)
                           end,
            {ok, {IndexPolicy, DepPolicy, NewIndexTree}}
    end;
update({update, Ops}, Index) when is_list(Ops) ->
    apply_ops(Ops, Index);
update({remove, {_Key, none}}, Index) ->
    {ok, Index};
update({remove, {Key, Op}}, {IndexPolicy, DepPolicy, IndexTree}) ->
    CurrEntry = fetch_tree_key(Key, IndexTree, undefined),
    NewEntry =
        maps:fold(fun({FieldName, _} = OpKey, OpVal, NewValAcc) ->
            AuxNewV = apply_op({FieldName, OpVal}, CurrEntry),
            UpdatedEntry = maps:get(OpKey, AuxNewV),
            maps:put(OpKey, UpdatedEntry, NewValAcc)
        end, maps:new(), Op),
    case CurrEntry == NewEntry of
        true ->
            {ok, {IndexPolicy, DepPolicy, IndexTree}};
        false ->
            NewIndexTree =
                case CurrEntry of
                    undefined ->
                        gb_trees:insert(Key, NewEntry, IndexTree);
                    _ ->
                        gb_trees:update(Key, NewEntry, IndexTree)
                end,
            {ok, {IndexPolicy, DepPolicy, NewIndexTree}}
    end;
update({remove, Ops}, Index) when is_list(Ops) ->
    apply_ops(Ops, Index);
update({set, {index_policy, NewIndexPolicy}}, {_CurrIndexPolicy, DepPolicy, IndexTree}) ->
    {ok, {NewIndexPolicy, DepPolicy, IndexTree}};
update({set, {dep_policy, NewDepPolicy}}, {IndexPolicy, _CurrDepPolicy, IndexTree}) ->
    {ok, {IndexPolicy, NewDepPolicy, IndexTree}}.

-spec equal(antidote_crdt_index_p(), antidote_crdt_index_p()) -> boolean().
equal({IndexPolicy1, DepPolicy1, IndexTree1}, {IndexPolicy2, DepPolicy2, IndexTree2}) ->
    IndexPolicy1 =:= IndexPolicy2 andalso
    DepPolicy1 =:= DepPolicy2 andalso
    IndexTree1 =:= IndexTree2 andalso
    gb_trees:size(IndexTree1) =:= gb_trees:size(IndexTree2) andalso
    rec_equals(IndexTree1, IndexTree2).

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
        {policies, {}} ->
            true;
        {update, {_Key, Op}} ->
            is_operation0(Op);
        {remove, {_Key, Op}} ->
            (is_operation0(Op) orelse Op == none);
        {set, {index_policy, _}} ->
            true;
        {set, {dep_policy, _}} ->
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
new_entry() ->
    WithBObj = maps:put(?bound_obj_key, ?BOBJ_DT:new(), maps:new()),
    WithState = maps:put(?state_key, ?STATE_DT:new(), WithBObj),
    WithVersion = maps:put(?version_key, ?VRS_DT:new(), WithState),
    WithRefs = maps:put(?refs_key, [], WithVersion),
    WithRefs.

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
    case is_bottom(Entry) of
        true ->
            none;
        false ->
            BoundKey = fetch_map_key(?bound_obj_key, Entry, ?BOBJ_DT:new()),
            State = fetch_map_key(?state_key, Entry, ?STATE_DT:new()),
            Version = fetch_map_key(?version_key, Entry, ?VRS_DT:new()),
            Refs = fetch_map_key(?refs_key, Entry, []),
            RefValues = lists:map(fun({RefName, RefState}) -> {RefName, ?REF_DT:value(RefState)} end, Refs),
            {ok, {?BOBJ_DT:value(BoundKey), ?STATE_DT:value(State), ?VRS_DT:value(Version), RefValues}}
    end.

apply_op(Op, IndexEntry) ->
    Entry0 = case IndexEntry of
                 undefined -> new_entry();
                 _Else -> IndexEntry
             end,

    {ok, StateUpdated} = apply_update(Op, Entry0),
    StateUpdated.

generate_downstream_update({bound_obj, Op}, Entry) ->
    BObjCRDT = fetch_map_key(?bound_obj_key, Entry, ?BOBJ_DT:new()),
    {ok, DownS} = ?BOBJ_DT:downstream(Op, BObjCRDT),
    {ok, {bound_obj, DownS}};
generate_downstream_update({state, Op}, Entry) ->
    StateCRDT = fetch_map_key(?state_key, Entry, ?STATE_DT:new()),
    {ok, DownS} = ?STATE_DT:downstream(Op, StateCRDT),
    {ok, {state, DownS}};
generate_downstream_update({version, Op}, Entry) ->
    VrsCRDT = fetch_map_key(?version_key, Entry, ?VRS_DT:new()),
    {ok, DownS} = ?VRS_DT:downstream(Op, VrsCRDT),
    {ok, {version, DownS}};
generate_downstream_update({refs, Ops}, Entry) when is_list(Ops) ->
    Refs = fetch_map_key(?refs_key, Entry, []),
    NewRefs = lists:foldl(fun({RefName, Op}, AccRefs) ->
        State = case proplists:get_value(RefName, AccRefs) of
                    undefined -> ?REF_DT:new();
                    Val -> Val
                end,
        {ok, UpdatedState} = ?REF_DT:downstream(Op, State),
        lists:keystore(RefName, 1, AccRefs, {RefName, UpdatedState})
    end, Refs, Ops),
    {ok, {refs, NewRefs}};
generate_downstream_update({refs, {RefName, Op}}, Entry) ->
    generate_downstream_update({refs, [{RefName, Op}]}, Entry).

generate_downstream_remove(Key, {_IndexPolicy, _DepPolicy, IndexTree}) ->
    Entry = case gb_trees:lookup(Key, IndexTree) of
                {value, Map} -> Map;
                none -> new_entry()
            end,
    ResetOp = {reset, {}},

    DownstreamEffect =
        maps:fold(fun({FieldName, FieldType} = Field, State, Acc) ->
            DS = case FieldName of
                     refs ->
                         lists:map(fun({RefName, RefValue}) ->
                                 {RefName, generate_downstream_reset({refs, {ignore, ResetOp}}, ?REF_DT, RefValue)}
                             end, State);
                     _ ->
                         generate_downstream_reset({FieldName, ResetOp}, FieldType, State)
                 end,
            maps:put(Field, DS, Acc)
        end, maps:new(), Entry),

    {Key, DownstreamEffect};
generate_downstream_remove(Key, _) ->
    {Key, none}.

generate_downstream_reset(Op, StateDT, State) ->
    case is_operation0(Op) of
        true ->
            {ok, DownS} = StateDT:downstream({reset, {}}, State),
            DownS;
        false ->
            resolve_downstream(StateDT, State)
    end.

set_policy(undefined, add) -> add;
set_policy(undefined, remove) -> remove;
set_policy(NewPolicy, NewPolicy) -> NewPolicy;
set_policy(_CurrPolicy, _NewPolicy) -> error.

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

apply_update({bound_obj, Op}, Entry) ->
    BObjCRDT = fetch_map_key(?bound_obj_key, Entry, ?BOBJ_DT:new()),
    {ok, Upd} = ?BOBJ_DT:update(Op, BObjCRDT),
    {ok, maps:put(?bound_obj_key, Upd, Entry)};
apply_update({state, Op}, Entry) ->
    StateCRDT = fetch_map_key(?state_key, Entry, ?STATE_DT:new()),
    {ok, Upd} = ?STATE_DT:update(Op, StateCRDT),
    {ok, maps:put(?state_key, Upd, Entry)};
apply_update({version, Op}, Entry) ->
    VrsCRDT = fetch_map_key(?version_key, Entry, ?VRS_DT:new()),
    {ok, Upd} = ?VRS_DT:update(Op, VrsCRDT),
    {ok, maps:put(?version_key, Upd, Entry)};
apply_update({refs, Ops}, Entry) when is_list(Ops) ->
    Refs = fetch_map_key(?refs_key, Entry, []),
    NewRefs = lists:foldl(fun({RefName, Op}, AccRefs) ->
        State = case proplists:get_value(RefName, AccRefs) of
                    undefined -> ?REF_DT:new();
                    Val -> Val
                end,
        {ok, UpdatedState} = ?REF_DT:update(Op, State),
        lists:keystore(RefName, 1, AccRefs, {RefName, UpdatedState})
    end, Refs, Ops),
    {ok, maps:put(?refs_key, NewRefs, Entry)};
apply_update({refs, {RefName, Op}}, Entry) ->
    apply_update({refs, [{RefName, Op}]}, Entry).

is_bottom(Entry) ->
    BoundObj = fetch_map_key(?bound_obj_key, Entry, ?BOBJ_DT:new()),
    State = fetch_map_key(?state_key, Entry, ?STATE_DT:new()),
    Version = fetch_map_key(?version_key, Entry, ?VRS_DT:new()),
    Refs = fetch_map_key(?refs_key, Entry, []),

    is_bottom(?BOBJ_DT, BoundObj) andalso
    is_bottom(?STATE_DT, State) andalso
    is_bottom(?VRS_DT, Version) andalso
    lists:foldl(fun({_RefName, RefValue}, Acc) ->
        Acc andalso is_bottom(?REF_DT, RefValue)
    end, true, Refs).

is_bottom(Type, State) ->
    Val1 = calc_value(Type, Type:value(State)),
    Val2 = calc_value(Type, Type:value(Type:new())),
    (erlang:function_exported(Type, is_bottom, 1) andalso Type:is_bottom(State))
        orelse Val1 == Val2.

is_operation0({bound_obj, Op}) -> ?BOBJ_DT:is_operation(Op);
is_operation0({state, Op}) -> ?STATE_DT:is_operation(Op);
is_operation0({version, Op}) -> ?VRS_DT:is_operation(Op);
is_operation0({refs, {_RefName, Op}}) -> ?REF_DT:is_operation(Op);
is_operation0(_) -> false.

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
    case entry_value(Value) of
        none ->
            iterate_and_filter(Predicate, gb_trees:next(Iter), Acc);
        {ok, Val} ->
            NewAcc = lists:append(Acc, [{Key, Val}]),
            iterate_and_filter(Predicate, gb_trees:next(Iter), NewAcc)
    end;
iterate_and_filter({Bound, Params} = Predicate, {Key, Value, Iter}, Acc) ->
    Result = case Params of
                 [key] ->
                     apply_pred(Bound, Key);
                 [value, V] ->
                     apply_pred(Bound, [Value, V])
             end,
    NewAcc = case Result of
                 true ->
                     case entry_value(Value) of
                         none -> Acc;
                         {ok, Val} -> lists:append(Acc, [{Key, Val}])
                     end;
                 false -> Acc
             end,
    iterate_and_filter(Predicate, gb_trees:next(Iter), NewAcc).

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

fetch_map_key(Key, Dict, Default) ->
    case maps:find(Key, Dict) of
        {ok, Value} -> Value;
        error -> Default
    end.

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
    ?assertEqual({undefined, undefined, gb_trees:empty()}, new()),
    ?assertEqual({add, add, gb_trees:empty()}, new(add, add)),
    ?assertEqual({add, remove, gb_trees:empty()}, new(add, remove)).

update_test() ->
    Index1 = new(add, add),
    BoundObj = {key, type, bucket},
    {ok, DownstreamOp} = downstream({update, {key, {bound_obj, {assign, BoundObj}}}}, Index1),
    ?assertMatch({update, {key, {bound_obj, {_, BoundObj}}}}, DownstreamOp),
    {ok, Index2} = update(DownstreamOp, Index1),

    {_, _, Tree} = value(Index2),
    Entry = {BoundObj, [], <<>>, []},
    ?assertEqual([{key, Entry}], Tree).

update2_test() ->
    Index1 = new(),
    Index2 = update_entry_aux(key, {state, {assign, i}}, Index1),
    Index3 = update_entry_aux(key, {version, {assign, 5}}, Index1),

    {_, _, Tree1} = value(Index2),
    Entry1 = {<<>>, [i], <<>>, []},

    {_, _, Tree2} = value(Index3),
    Entry2 = {<<>>, [], 5, []},

    ?assertEqual([{key, Entry1}], Tree1),
    ?assertEqual([{key, Entry2}], Tree2).

update3_test() ->
    Index1 = new(),
    {ok, DownstreamOp} = downstream({set, {index_policy, add}}, Index1),
    {ok, Index2} = update(DownstreamOp, Index1),

    ?assertEqual({add, undefined}, value({policies, {}}, Index2)),
    Response = downstream({set, {index_policy, remove}}, Index2),
    ?assertMatch({error, _}, Response).

remove_test() ->
    Index1 = new(add, remove),
    Index2 = update_entry_aux(key1, {refs, {ref1, {assign, {refvalue1, 1}}}}, Index1),
    Index3 = update_entry_aux(key2, {state, {assign, d}}, Index2),
    Index4 = update_entry_aux(key3, {version, {assign, 10}}, Index3),

    Removes = [key1, key3],
    {ok, DS} = downstream({remove, Removes}, Index4),
    {ok, Index5} = update(DS, Index4),

    {_, _, Tree} = value(Index5),
    Entry = {<<>>, [d], <<>>, []},
    FinalRes = [{key2, Entry}],
    ?assertEqual(FinalRes, Tree).

concurrent_test() ->
    Index1 = new(add, add),
    Index2 = update_entry_aux(key1, {refs, {ref1, {assign, {refval1, 1}}}}, Index1),
    Index3 = update_entry_aux(key2, {refs, {ref2, {assign, {refval2, 1}}}}, Index2),

    %% Node 1
    {ok, DownSN1} = downstream({update, {key2, {version, {assign, 1}}}}, Index3),
    {ok, IndexN1} = update(DownSN1, Index3),

    %% Node 2
    {ok, DownSN2} = downstream({remove, key2}, Index3),
    {ok, IndexN2} = update(DownSN2, Index3),

    %% Node 3
    {ok, DownSN3} = downstream({update, {key3, {state, {assign, i}}}}, Index3),
    {ok, IndexN3} = update(DownSN3, Index3),

    %% Merge
    {ok, MIndexN1_1} = update(DownSN2, IndexN1),
    {ok, MIndexN1_2} = update(DownSN3, MIndexN1_1),

    {ok, MIndexN2_1} = update(DownSN3, IndexN2),
    {ok, MIndexN2_2} = update(DownSN1, MIndexN2_1),

    {ok, MIndexN3_1} = update(DownSN1, IndexN3),
    {ok, MIndexN3_2} = update(DownSN2, MIndexN3_1),

    DefaultEntry = [
        {key1, {<<>>, [], <<>>, [{ref1, {refval1, 1}}]}},
        {key3, {<<>>, [i], <<>>, []}}
    ],

    FinalRes = {add, add, DefaultEntry},
    ?assertEqual(FinalRes, value(MIndexN1_2)),
    ?assertEqual(FinalRes, value(MIndexN2_2)),
    ?assertEqual(FinalRes, value(MIndexN3_2)).

equal_test() ->
    Index1 = new(),
    {ok, DownstreamOp1} = downstream({update, {key1, {version, {assign, 5}}}}, Index1),
    {ok, DownstreamOp2} = downstream({update, {key1, {version, {assign, 10}}}}, Index1),
    {ok, DownstreamOp3} = downstream({update, {key1, {state, {assign, i}}}}, Index1),
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
        {1, {state, {assign, i}}}, {2, {state, {assign, i}}},
        {3, {state, {assign, i}}}, {4, {state, {assign, i}}},
        {5, {state, {assign, i}}}, {6, {state, {assign, i}}}
    ],
    {ok, DownstreamOp1} = downstream({update, Updates}, Index1),
    {ok, Index2} = update(DownstreamOp1, Index1),
    LowerPred1 = {greatereq, 3},
    UpperPred1 = {lesser, 6},
    Result1 = value({range, {LowerPred1, UpperPred1}}, Index1),
    Result2 = value({range, {LowerPred1, UpperPred1}}, Index2),

    DefaultEntry = {<<>>, [i], <<>>, []},
    ?assertEqual([], Result1),
    ?assertEqual([{3, DefaultEntry}, {4, DefaultEntry}, {5, DefaultEntry}], Result2).

is_operation_test() ->
    Op1 = {update, {k, {bound_obj, {assign, {k, t, b}}}}},
    Op2 = {update, {k, {version, {increment, 1}}}},
    Op3 = {remove, {k, none}},
    Op4 = {update, {k, {state, {assign, i}}}},
    Op5 = {range, pred1, pred2},
    Op6 = {get, key},
    Op7 = {lookup, key},
    Op8 = {policies, {}},

    ?assertEqual(true, is_operation(Op1)),
    ?assertEqual(false, is_operation(Op2)),
    ?assertEqual(true, is_operation(Op3)),
    ?assertEqual(true, is_operation(Op4)),
    ?assertEqual(false, is_operation(Op5)),
    ?assertEqual(true, is_operation(Op6)),
    ?assertEqual(false, is_operation(Op7)),
    ?assertEqual(true, is_operation(Op8)).

-endif.