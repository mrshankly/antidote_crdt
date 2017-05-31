%% -------------------------------------------------------------------
%%
%% crdt_bigset: A convergent, replicated, operation based observe remove set
%%
%% Copyright (c) 2007-2012 Basho Technologies, Inc.  All Rights Reserved.
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
%% -------------------------------------------------------------------

%% @doc
%% An operation-based Observed-Remove Set CRDT.
%% As the data structure is operation-based, to issue an operation, one should
%% firstly call `downstream/2' to get the downstream version of the
%% operation and then call `update/2'.
%%
%% It provides five operations: add, which adds an element to a set; add_all,
%% adds a list of elements to a set; remove, which removes an element from a set;
%% remove_all that removes a list of elements from the set; update, that contains
%% a list of previous four commands.
%%
%% This file is adapted from riak_dt_bigset, a state-based implementation of
%% Observed-Remove Set.
%% The changes are as follows:
%% 1. `generate_downstream/3' is added, as this is necessary for op-based CRDTs.
%% 2. `merge/2' is removed.
%% 3. There is no tombstone of removed elements.
%%
%% @reference Marc Shapiro, Nuno Preguiça, Carlos Baquero, Marek Zawirski (2011) A comprehensive study of
%% Convergent and Commutative Replicated Data Types. http://hal.upmc.fr/inria-00555588/
%%
%% @end
-module(antidote_crdt_bigset).
-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl"). 
%-include_lib("C:/Users/Luehk/workspace/Bigset/include/eunit/include/eunit.hrl"). 
-endif. 
-include("antidote_crdt.hrl").
%-include("C:/Users/Luehk/workspace/Bigset/include/antidote_crdt.hrl"). 

%% Callbacks
-export([ new/0,
	  new/2,
          value/1,
          downstream/2,
	  contains/2,
          update/2,
          equal/2,
          to_binary/1,
          from_binary/1,
          is_operation/1,
          require_state_downstream/1,
          is_bottom/1
        ]).

%-behaviour(antidote_crdt).

-export_type([bigset/0, binary_bigset/0, bigset_op/0, elem/0, token/0, elem_hash/0]).
 
-type bigset() :: {integer(), integer(), antidote_crdt_bigset_keytree : tree(), atom()}.

-type binary_bigset() :: binary(). %% A binary that from_binary/1 will operate on.

-type bigset_op() ::
      {add, elem()}
    | {remove, elem()}
    | {add_all, [elem()]}
    | {remove_all, [elem()]}
    | {reset, {}}.

%% The downstream op is a list of triples.
%% In each triple:
%%  - the first component is the elem that was added or removed
%%  - the second component is the list of supporting tokens to be added
%%  - the third component is the list of supporting tokens to be removed
-type downstream_op() :: [{elem_hash(), elem(), tokens(), tokens()}].
-type elem() :: term(). 
-type elem_hash() :: integer().
-type token() :: binary().
-type tokens() :: [token()].

-spec new() -> bigset().
new() ->
	new(32, 100).
	
%% Hash_Exponent bust be between 0 and 32
-spec new(integer(), integer()) -> bigset().
new(Hash_Exponent, Max_Count) ->
	Hash_Range = exponent_of_2(Hash_Exponent),
	Atom = erlang:binary_to_atom(unique(), latin1),
	Table = ets:new(Atom, [set, public, named_table, {keypos,1}, {heir,none}, {write_concurrency,true}, {read_concurrency,true}]),
	Key = Hash_Range div 2,
	Value = unique(),
	ets:insert(Table, {{Key, Value}, antidote_crdt_bigset_shard : new(Key, [])}),
	ets:insert(Table, {"Keyversions", maps:put(Key, [Value], maps: new())}),
	{Hash_Range, Max_Count, antidote_crdt_bigset_keytree : init(Key, Value), Table}.

-spec exponent_of_2(integer()) -> integer().
exponent_of_2(0) -> 
	1;
exponent_of_2(N) ->
	if 
		N > 32 -> 
			exponent_of_2(32);
		true ->
			2*exponent_of_2(N-1)
	end.

%% @doc return all existing elements in the bigset
-spec value(bigset()) -> [elem()].
value({_Hash_Range, _Max_Count, Tree, Table}=_BigSet) ->
	TableKeys = antidote_crdt_bigset_keytree : get_all(Tree),
    lists:usort(value_helper(TableKeys, Table)).
	
-spec value_helper([integer()], atom()) -> [elem()].
value_helper([Key|Rest], Table) ->
	case Rest of
        [] ->
			[{_Int, Shard}] = ets:lookup(Table, Key),
            antidote_crdt_bigset_shard : value(Shard);
        _ ->
			[{_Int, Shard}] = ets:lookup(Table, Key),
            antidote_crdt_bigset_shard : value(Shard) ++ value_helper(Rest, Table)
	end.

%% @doc return true if the bigset contains the element
-spec contains(elem(), bigset()) -> boolean().
contains(Elem, {Hash_Range, _Max_Count, Tree, Table} = _BigSet) ->
	H_Elem = erlang:phash2(Elem, Hash_Range),
	{ok, TableKey} = antidote_crdt_bigset_keytree : get_key(H_Elem, Tree),
	[{_Int, Shard}] = ets:lookup(Table, TableKey),
	antidote_crdt_bigset_shard : contains(H_Elem, Elem, Shard). 

%% @doc return all existing elements in the `bigset()'.
-spec get_tokens(elem_hash(), elem(), bigset()) -> [token()].
get_tokens(H_Elem, Elem, {Hash_Range, _Max_Count, Tree, Table} = _BigSet) ->
	{ok, TableKey} = antidote_crdt_bigset_keytree : get_key(H_Elem, Tree),
	Temp = ets:info(Table),
	if 
		Temp == undefined->
			Table2 = ets:new(Table, [set, public, named_table, {keypos,1}, {heir,none}, {write_concurrency,true}, {read_concurrency,true}]),
			Key = Hash_Range div 2,
			{ok,{Key2, Value}} = antidote_crdt_bigset_keytree : get_key(Key, Tree),
			ets:insert(Table2, {{Key, Value}, antidote_crdt_bigset_shard : new(Key2, [])}),
			ets:insert(Table2, {"Keyversions", maps:put(Key2, [Value], maps: new())}),
			[];
		true ->
			[{_Int, Shard}] = ets:lookup(Table, TableKey),
			antidote_crdt_bigset_shard : get_tokens(H_Elem, Elem, Shard)
	end.

%% @doc compares two bigsets, yields "true" if they contain the same elements
%% The bigsets may differ in number of shards, so we can't compare them shard by shard
-spec equal(bigset(), bigset()) -> boolean().
equal(BigSetA, BigSetB) ->
	equal_content(value(BigSetA), value(BigSetB)).
 
-spec equal_content([elem()], [elem()]) -> boolean().
%% Both lists run out of elements at the same time, so if member() was never false in the last case, both lists had equal content
equal_content([], []) ->
	true;
equal_content([], _Content) ->
	false;
equal_content(_Content, []) ->
	false;
%% delete does nothing if the element is not contained in the list, so we need to apply member(First, ContentB) first
%% then continue with the element taken out of both lists
equal_content([First|Rest], ContentB) ->
	lists : member(First, ContentB) andalso equal_content(Rest, lists : delete(First, ContentB)).

-include("riak_dt_tags.hrl").
%-include("C:/Users/Luehk/workspace/Bigset/include/riak_dt_tags.hrl"). 
-define(TAG, ?DT_BIGSET_TAG).
-define(V1_VERS, 1).

-spec to_binary(bigset()) -> binary_bigset().
to_binary(BigSet) ->
    %% @TODO something smarter
    <<?TAG:8/integer, ?V1_VERS:8/integer, (term_to_binary(BigSet))/binary>>.

-spec from_binary(<<_:16,_:_*8>>) -> {'ok', bigset()}.
from_binary(<<?TAG:8/integer, ?V1_VERS:8/integer, Bin/binary>>) ->
    %% @TODO something smarter
    {ok, binary_to_term(Bin)}.

%% @doc generate a unique identifier (best-effort).
-spec unique() -> token().
unique() ->
    crypto:strong_rand_bytes(20).

%% @doc generate downstream operations.
%% If the operation is add or add_all, generate unique tokens for
%% each element and fetch the current supporting tokens.
%% If the operation is remove or remove_all, fetch current
%% supporting tokens of these elements existing in the `bigset()'.
-spec downstream(bigset_op(), bigset()) -> {ok, downstream_op()}.
downstream({add, Elem}, BigSet) ->
    downstream({add_all, [Elem]}, BigSet);
downstream({add_all, Elems}, BigSet) ->
    CreateDownstream = fun(H_Elem, Elem, CurrentTokens) ->
        Token = unique(),
        {H_Elem , Elem, [Token], CurrentTokens}
    end,
    DownstreamOps = create_downstreams(CreateDownstream, lists:usort(Elems), BigSet, []),
    {ok, DownstreamOps};
downstream({remove, Elem}, BigSet) ->
    downstream({remove_all, [Elem]}, BigSet);
downstream({remove_all, Elems}, BigSet) ->
    CreateDownstream = fun(H_Elem, Elem, CurrentTokens) ->
        {H_Elem, Elem, [], CurrentTokens}
    end,
    DownstreamOps = create_downstreams(CreateDownstream, lists:usort(Elems), BigSet, []),
    {ok, DownstreamOps};
downstream({reset, {}}, BigSet) ->
    % reset is like removing all elements
    downstream({remove_all, value(BigSet)}, BigSet).

%% @private generic downstream op creation for adds and removals
- spec create_downstreams(any(), [elem()], bigset(), downstream_op()) -> downstream_op().
create_downstreams(_CreateDownstream, [], _BigSet, DownstreamOps) ->
    lists : keysort(1, DownstreamOps);
create_downstreams(CreateDownstream, [Elem|ElemsRest], {Hash_Range, _Max_Count, _Tree, _Table} = BigSet, DownstreamOps) ->
	H_Elem = erlang : phash2(Elem, Hash_Range),
        Tokens = get_tokens(H_Elem, Elem, BigSet),
	DownstreamOp = CreateDownstream(H_Elem, Elem, Tokens),
	create_downstreams(CreateDownstream, ElemsRest, BigSet, [DownstreamOp|DownstreamOps]).

%% @doc apply downstream operations and update a bigset.
-spec update(downstream_op(), bigset()) -> {ok, bigset()}.
update(DownstreamOp, BigSet) ->
    {ok, apply_downstreams(DownstreamOp, BigSet)}.

%% @private apply a list of downstream ops to a given bigset
%% first downstream_op() collects elements that go into the same shard, second contains remaining elements
-spec apply_downstreams(downstream_op(), bigset()) -> bigset().
apply_downstreams([], BigSet) ->
    BigSet;
apply_downstreams([{H_Elem, _Elem, _ToAdd, _ToRemove} = Op|OpsRest], {_Hash_Range, _Max_Count, Tree, Table} = BigSet) ->
	{ok, TableKey} = antidote_crdt_bigset_keytree : get_key(H_Elem, Tree),
	[{_Int, Shard}] = ets:lookup(Table, TableKey),
	{ok, Shard2} = antidote_crdt_bigset_shard : update_shard(Op, Shard),
	BigSet2 = pick_action(BigSet, Shard2),
	apply_downstreams(OpsRest, BigSet2).

-spec pick_action(bigset(), antidote_crdt_bigset_shard : shard()) -> bigset().
pick_action({Hash_Range, Max_Count, Tree, Table} = _BigSet, {Key, Siblings, Content} = Shard) ->
	Size = antidote_crdt_bigset_shard : size(Shard),
	if 
		Size < Max_Count div 4 andalso Siblings /= [] -> 
			SiblingKey = lists:last(Siblings),
			{ok, TableKey} = antidote_crdt_bigset_keytree : get_key(SiblingKey, Tree),
			[{_Int, {_SiblingKey, Siblings2, SiblingContent}}] = ets:lookup(Table, TableKey),
			SiblingSize = length(SiblingContent),
			Key2 = lists:last(Siblings2),
			if
				Key == Key2 andalso SiblingSize < (Max_Count div 2) ->
					NewKey = (Key + SiblingKey) div 2,
					NewShard = {NewKey, lists : droplast(Siblings), antidote_crdt_bigset_shard : merge_content(Content, SiblingContent)},
					Value = unique(),
					ets:insert(Table, {{NewKey, Value}, NewShard}),
					ok = garbage_collect_table(Table, {NewKey, Value}),
					{Hash_Range, Max_Count, antidote_crdt_bigset_keytree : replace(NewKey, Value, Tree), Table};
				true ->
					Value = unique(),
					ets:insert(Table, {{Key, Value}, Shard}),
					ok = garbage_collect_table(Table, {Key, Value}),
					{Hash_Range, Max_Count, antidote_crdt_bigset_keytree : replace(Key, Value, Tree), Table}	
			end;				
		Size > Max_Count ->
			Temp = exponent_of_2(length(Siblings)+1),
			if 
				Temp < Hash_Range -> 
					{{Upper_Key, _Upper_Siblings, _Upper_Content} = Upper_Shard,{Lower_Key, _Lower_Siblings, _Lower_Content} = Lower_Shard} 
						= antidote_crdt_bigset_shard : split(Shard, Hash_Range),
					Value1 = unique(),
					Value2 = unique(),
					ets:insert(Table, [{{Lower_Key, Value1}, Lower_Shard},{{Upper_Key, Value2}, Upper_Shard}]),
					ok = garbage_collect_table(Table, {Lower_Key, Value1}),
					ok = garbage_collect_table(Table, {Upper_Key, Value2}),
					{Hash_Range, Max_Count, antidote_crdt_bigset_keytree : insert_two(Lower_Key, Upper_Key, Value1, Value2, Tree), Table};
				true ->
					Value = unique(),
					ets:insert(Table, {{Key, Value}, Shard}),
					ok = garbage_collect_table(Table, {Key, Value}),
					{Hash_Range, Max_Count, antidote_crdt_bigset_keytree : replace(Key, Value, Tree), Table}
			end;
		true -> 
			Value = unique(),
			ets:insert(Table, {{Key, Value}, Shard}),
			ok = garbage_collect_table(Table, {Key, Value}),
			{Hash_Range, Max_Count, antidote_crdt_bigset_keytree : replace(Key, Value, Tree), Table}	
	end.

-spec garbage_collect_table(atom(), {}) -> ok.
garbage_collect_table(Table, {Key, Value}) ->
	[{_Int, Map}] = ets:lookup(Table, "Keyversions"),
	Temp = maps:is_key(Key, Map),
	if 
		Temp == true ->
			{ok, ValueList} = maps: find(Key, Map),
			Temp2 = lists : member(Value, ValueList),
			if 
				Temp2 == true->
					[Head | Rest] = ValueList;
				true ->
					[Head | Rest] = lists: append(ValueList, [Value])
			end,
			if
				%% if there are more than 10 versions of a shard, the oldest is deleted
				length([Head|Rest]) > 10 ->
					Temp3 = ets:member(Table, {{Key, Head}}),
					if
						Temp3 == true ->
							ets:delete(Table, {Key, Head});
						true ->
							ok
					end,
					Map2 = maps : put(Key, Rest, Map);
				true ->
					Map2 = maps : put(Key, [Head|Rest], Map)	
			end,			
			ets : insert(Table, {"Keyversions", Map2}),
			ok;
		true ->
			Map2 = maps : put(Key, [Value], Map),
			ets : insert(Table, {"Keyversions", Map2}),
			ok
	end.

%% @doc The following operation verifies
%%      that Operation is supported by this particular CRDT.
is_operation({add, _Elem}) -> true;
is_operation({add_all, L}) when is_list(L) -> true;
is_operation({remove, _Elem}) -> true;
is_operation({remove_all, L}) when is_list(L) -> true;
is_operation({reset, {}}) -> true;
is_operation(_) -> false.

require_state_downstream({add, _}) -> true;
require_state_downstream({add_all, _}) -> true;
require_state_downstream({remove, _}) -> true;
require_state_downstream({remove_all, _}) -> true;
require_state_downstream({reset, {}}) -> true.

is_bottom(State) -> State == new().

%% ===================================================================
%% EUnit tests
%% ===================================================================
-ifdef(TEST).

new_test() ->
	BigSet = new(),
    ?assertEqual([], value(BigSet)).

contains_test() ->
    Elem = <<"foo">>,
    Set1 = new(),
    {ok, DownstreamOp1} = downstream({add, Elem}, Set1),
    {ok, Set2} = update(DownstreamOp1, Set1),
    ?assertEqual(contains(Elem, Set2), true).

add_test() ->
    Elem = <<"foo">>,
	H_Elem = erlang:phash2(Elem, 4294967296),
    Elems = [<<"li">>, <<"manu">>],
	H_Elem2 = erlang:phash2(<<"li">>, 4294967296),
	H_Elem3 = erlang:phash2(<<"manu">>, 4294967296),
    Set1 = new(),
    {ok, DownstreamOp1} = downstream({add, Elem}, Set1),
    ?assertMatch([{H_Elem, Elem, _, _}], DownstreamOp1),
    {ok, DownstreamOp2} = downstream({add_all, Elems}, Set1),
	%% manu and li are exchanged because DownstreamOp2 is sorted according to the hashed element
    ?assertMatch([{H_Elem3, <<"manu">>, _, _}, {H_Elem2, <<"li">>, _, _}], DownstreamOp2),
    {ok, Set2} = update(DownstreamOp1, Set1),
    ?assertEqual([Elem], value(Set2)),
    {ok, Set3} = update(DownstreamOp2, Set1),
    ?assertEqual(lists : sort(Elems), lists: sort(value(Set3))).

add_much_test() ->
    Elems = [<<"a">>, <<"b">>, <<"c">>, <<"d">>, <<"e">>, <<"f">>, <<"g">>, 
			 	<<"h">>, <<"i">>, <<"j">>, <<"k">>, <<"l">>, <<"m">>, <<"n">>, <<"o">>, <<"p">>, <<"q">>],
    Set1 = new(32, 4),
    {ok, DownstreamOp2} = downstream({add_all, Elems}, Set1),
    ?assertMatch([{_, <<"a">>, _, _}, {_, <<"b">>, _, _}, {_, <<"c">>, _, _}, {_, <<"d">>, _, _}, {_, <<"e">>, _, _},
				  {_, <<"f">>, _, _}, {_, <<"g">>, _, _}, {_, <<"h">>, _, _}, {_, <<"i">>, _, _}, {_, <<"j">>, _, _},
				  {_, <<"k">>, _, _}, {_, <<"l">>, _, _}, {_, <<"m">>, _, _}, {_, <<"n">>, _, _}, {_, <<"o">>, _, _},
				  {_, <<"p">>, _, _}, {_, <<"q">>, _, _}], lists : keysort(2,DownstreamOp2)),
    {ok, Set2} = update(DownstreamOp2, Set1),
    ?assertEqual(Elems, lists: sort(value(Set2))),
	Elems2 = lists:delete(<<"f">>, Elems),
	{ok, DownstreamOp3} = downstream({remove_all, Elems2}, Set2),
	{ok, Set3} = update(DownstreamOp3, Set2),
	?assertEqual([<<"f">>], lists: sort(value(Set3))).

add_100_test() ->
    Elems = lists: seq(1,51000),
    Set1 = new(32, 475),
    {ok, DownstreamOp2} = downstream({add_all, Elems}, Set1),
    {ok, Set2} = update(DownstreamOp2, Set1),
	Set3 = Set2,
    ?assertEqual(value(Set2), value(Set3)).
	%{ok, ShardKey} = antidote_crdt_bigset_keytree : get_key(4, Tree),
	%[{_Int, Shard}] = ets:lookup(Table, ShardKey),
	%[{_Int2, Map}] = ets:lookup(Table, "Keyversions"),
	%[Head|_Rest] = maps:keys(Map),
	%List = maps:get(Head, Map),
	%?assertEqual("woah", Shard),

equal_test() ->
    Elems = [<<"a">>, <<"b">>, <<"c">>, <<"d">>, <<"e">>],
    Set1 = new(32, 4),
    {ok, DownstreamOp2} = downstream({add_all, Elems}, Set1),
    ?assertMatch([{_, <<"a">>, _, _}, {_, <<"b">>, _, _}, {_, <<"c">>, _, _}, {_, <<"d">>, _, _}, {_, <<"e">>, _, _}
				  ], lists : keysort(2,DownstreamOp2)),
	%% Set is split in 2 shards because it has 5 elements while a maximum of 4 elements fit into one shard
    {ok, Set2} = update(DownstreamOp2, Set1),
	Elems2 = lists: delete(<<"a">>, Elems),
	{ok, DownstreamOp3} = downstream({remove, <<"a">>}, Set2),
	{ok, Set3} = update(DownstreamOp3, Set2),
	{ok, DownstreamOp4} = downstream({add_all, Elems2}, Set1),
	%% This other set is not split, because only 4 elements are added
	{ok, Set4} = update(DownstreamOp4, Set1),
    ?assertEqual(value(Set4), value(Set3)).

value_test() ->
    Set1 = new(),
    {ok, DownstreamOp1} = downstream({add, <<"foo">>}, Set1),
    ?assertEqual([], value(Set1)),
    {ok, Set2} = update(DownstreamOp1, Set1),
    ?assertEqual([<<"foo">>], value(Set2)),
    {ok, DownstreamOp2} = downstream({add_all, [<<"foo">>, <<"li">>, <<"manu">>]}, Set2),
    {ok, Set3} = update(DownstreamOp2, Set2),
    ?assertEqual([<<"foo">>, <<"li">>, <<"manu">>], lists : sort(value(Set3))).

remove_test() ->
    Set1 = new(),
    %% Add an element then remove it
    {ok, Op1} = downstream({add, <<"foo">>}, Set1),
    {ok, Set2} = update(Op1, Set1),
    ?assertEqual([<<"foo">>], value(Set2)),
    {ok, Op2} = downstream({remove, <<"foo">>}, Set2),
    {ok, Set3} = update(Op2, Set2),
    ?assertEqual([], value(Set3)),

    %% Add many elements then remove part
    {ok, Op3} = downstream({add_all, [<<"foo">>, <<"li">>, <<"manu">>]}, Set1),
    {ok, Set4} = update(Op3, Set1),
    ?assertEqual([<<"foo">>, <<"li">>, <<"manu">>], lists: sort(value(Set4))),

    {ok, Op5} = downstream({remove_all, [<<"foo">>, <<"li">>]}, Set4),
    {ok, Set5} = update(Op5, Set4),
    ?assertEqual([<<"manu">>], value(Set5)),

    %% Remove more than current have
    {ok, Op6} = downstream({add_all, [<<"foo">>, <<"li">>, <<"manu">>]}, Set1),
    {ok, Set6} = update(Op6, Set1),
    {ok, Op7} = downstream({remove_all, [<<"manu">>, <<"test">>]}, Set6),
    {ok, Set7} = update(Op7, Set6),
    ?assertEqual([<<"foo">>, <<"li">>], value(Set7)).


remove2_test() ->
    Set1 = new(),
    %% Add an element then remove it
    {ok, Op1} = downstream({add, <<"foo">>}, Set1),
    {ok, Set2} = update(Op1, Set1),
    ?assertEqual([<<"foo">>], value(Set2)),
    {ok, Op2} = downstream({remove, <<"foo">>}, Set2),
    {ok, Set3} = update(Op2, Set2),
    ?assertEqual([], value(Set3)),

    %% Remove the element again (e.g. on a different replica)
    {ok, Op3} = downstream({remove, <<"foo">>}, Set2),
    {ok, Set4} = update(Op3, Set2),
    ?assertEqual([], value(Set4)),

    %% now execute Op3 on Set3, where the element was already removed locally
    {ok, Set5} = update(Op3, Set3),
    ?assertEqual([], value(Set5)).


concurrent_add_test() ->
    Set1 = new(),
    %% Add an element then remove it
    {ok, Op1} = downstream({add, <<"foo">>}, Set1),
    {ok, Set2} = update(Op1, Set1),
    ?assertEqual([<<"foo">>], value(Set2)),

    %% If remove is concurrent with the second add, will not remove the second added
    {ok, Op2} = downstream({remove, <<"foo">>}, Set2),

    {ok, Op3} = downstream({add, <<"foo">>}, Set1),
    {ok, Set3} = update(Op3, Set2),
    ?assertEqual([<<"foo">>], value(Set3)),

    {ok, Set4} = update(Op2, Set3),
    ?assertEqual([<<"foo">>], value(Set4)),

    %% If remove follows two adds, remove will remove all
    {ok, Op4} = downstream({remove, <<"foo">>}, Set3),
    {ok, Set5} = update(Op4, Set3),
    ?assertEqual([], value(Set5)).

binary_test() ->
    BigSet1 = new(),
    BinaryBigSet1 = to_binary(BigSet1),
    {ok, BigSet2} = from_binary(BinaryBigSet1),
    ?assertEqual(value(BigSet1), value(BigSet2)),

    {ok, Op1} = downstream({add, <<"foo">>}, BigSet1),
    {ok, BigSet3} = update(Op1, BigSet1),
    BinaryBigSet3 = to_binary(BigSet3),
    {ok, BigSet4} = from_binary(BinaryBigSet3),
    ?assertEqual(equal(BigSet3, BigSet4), true).

-endif.
