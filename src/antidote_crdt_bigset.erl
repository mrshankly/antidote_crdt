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
%% @reference Marc Shapiro, Nuno PreguicÌ§a, Carlos Baquero, Marek Zawirski (2011) A comprehensive study of
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
     	  value/1,
          downstream/2,
	 	  contains/2,
          update/2,
          equal/2,
          to_binary/1,
          from_binary/1,
          is_operation/1,
          require_state_downstream/1,
		  delete_old/1,
		  remove_tokens/2,
		  add_tokens/2,
          is_bottom/1
        ]).

%-behaviour(antidote_crdt).

-export_type([bigset/0, binary_bigset/0, bigset_op/0, elem/0, token/0, elem_hash/0]).
 
-type bigset() :: {atom(), integer(), integer(), antidote_crdt_bigset_keytree : tree(), atom(), token(), 
				   		orddict:orddict()}.

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
-type tablekey() :: {integer(), binary(), erlang:system_time()}.
-type elem_hash() :: integer().
-type token() :: binary().
-type tokens() :: [token()].
	
%% Hash_Exponent bust be between 0 and 32
-spec new() -> bigset().
new() ->
	new(20, 475).

%% Hash_Exponent bust be between 0 and 32
-spec new(integer(), integer()) -> bigset().
new(Hash_Exponent, Max_Count) ->
	Hash_Range = exponent_of_2(Hash_Exponent),
	Table = ets:new(erlang:binary_to_atom(unique(), latin1), [set, public, named_table, {keypos,1}, {heir,none}, {write_concurrency,false}, 
		{read_concurrency,true}]),
	Key = Hash_Range div 2,
	Time = erlang:system_time(),
	Value = unique(),
	ID = unique(),
	ets:insert(Table, {"LastGC", 0}),
	ets:insert(Table, {{Key, Value, Time}, 0, antidote_crdt_bigset_shard : new(Key)}),
	{big, Hash_Range, Max_Count, antidote_crdt_bigset_keytree : init(Key, {Value, Time}), Table, ID, [{ID,0}]}.

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
value({_Big, _Hash_Range, _Max_Count, Tree, Table, _ID, _VV}=_BigSet) ->
    lists:usort(value_helper(antidote_crdt_bigset_keytree : get_all(Tree), Table)).
	
-spec value_helper([integer()], atom()) -> [elem()].
value_helper([Key|Rest], Table) ->
	case Rest of
        [] ->
			Shard = ets:lookup_element(Table, Key, 3),
            antidote_crdt_bigset_shard : value(Shard);
        _ ->
			Shard = ets:lookup_element(Table, Key, 3),
            antidote_crdt_bigset_shard : value(Shard) ++ value_helper(Rest, Table)
	end.

%% @doc return true if the bigset contains the element
-spec contains(elem(), bigset()) -> boolean().
contains(Elem, {_Big, Hash_Range, _Max_Count, Tree, Table, _ID, _VV} = _BigSet) ->
	H_Elem = erlang:phash2(Elem, Hash_Range),
	{ok, TableKey} = antidote_crdt_bigset_keytree : get_key(H_Elem, Tree),
	Shard = ets:lookup_element(Table, TableKey, 3),
	antidote_crdt_bigset_shard : contains(H_Elem, Elem, Shard). 

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
%% If the operation is add or add_all, send the own replica ID
%% so every other replica can increment the according entry in its version vector
%% If the operation is remove or remove_all, send the current Version Vector
%% so every other replica can verify whether concurrent adds have been seen at source
-spec downstream(bigset_op(), bigset()) -> {ok, downstream_op()}.
downstream({add, Elem}, BigSet) ->
    downstream({add_all, [Elem]}, BigSet);
downstream({add_all, Elems}, BigSet) ->
    CreateDownstream = fun(H_Elem, Elem, ID, _VV) ->
        {H_Elem , Elem, [ID], []}
    end,
    {ok, create_downstreams(CreateDownstream, lists:usort(Elems), BigSet, [])};
downstream({remove, Elem}, BigSet) ->
    downstream({remove_all, [Elem]}, BigSet);
downstream({remove_all, Elems}, BigSet) ->
    CreateDownstream = fun(H_Elem, Elem, _ID, VV) ->
        {H_Elem, Elem, [], VV}
    end,
    {ok, create_downstreams(CreateDownstream, lists:usort(Elems), BigSet, [])};
downstream({reset, {}}, BigSet) ->
    % reset is like removing all elements
    downstream({remove_all, value(BigSet)}, BigSet).

%% @private generic downstream op creation for adds and removals
- spec create_downstreams(any(), [elem()], bigset(), downstream_op()) -> downstream_op().
create_downstreams(_CreateDownstream, [], _BigSet, DownstreamOps) ->
    lists : keysort(1, DownstreamOps);
create_downstreams(CreateDownstream, [Elem|ElemsRest], {_Big, Hash_Range, _Max_Count, _Tree, _Table, ID, VV} = BigSet, DownstreamOps) ->
	DownstreamOp = CreateDownstream(erlang : phash2(Elem, Hash_Range), Elem, ID, VV),
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
%% remove
apply_downstreams([{H_Elem, _Elem, [], _ToRemove} = Op|OpsRest], {_Big, _Hash_Range, _Max_Count, Tree, Table, _ID, _VV} = BigSet) ->
	{ok, TableKey} = antidote_crdt_bigset_keytree : get_key(H_Elem, Tree),
	[{_, Ref_Count, Shard}] = ets:lookup(Table, TableKey),
	{ok, Shard2} = antidote_crdt_bigset_shard : update_shard(Op, Shard),
	apply_downstreams(OpsRest, pick_action(BigSet, Shard2, TableKey, Ref_Count));
%% add
apply_downstreams([{H_Elem, Elem, [ID2], _ToRemove}|OpsRest], {_Big, Hash_Range, Max_Count, Tree, Table, ID, VV} = BigSet) ->
	VV2 = orddict : update_counter(ID2, 1, VV),
	{ok, TableKey} = antidote_crdt_bigset_keytree : get_key(H_Elem, Tree),
	[{_, Ref_Count, Shard}] = ets:lookup(Table, TableKey),
	{ok, Shard2} = antidote_crdt_bigset_shard : update_shard({H_Elem, Elem, [ID2], VV2}, Shard),
	{Big, Hash_Range, Max_Count, Tree2, Table, ID, VV} = pick_action(BigSet, Shard2, TableKey, Ref_Count),
	apply_downstreams(OpsRest, {Big, Hash_Range, Max_Count, Tree2, Table, ID, VV2}).

-spec pick_action(bigset(), antidote_crdt_bigset_shard : shard(), tablekey(), integer()) -> bigset().
pick_action({Big, Hash_Range, Max_Count, Tree, Table, ID, VV} = BigSet, 
				{Key, Siblings, Content} = Shard, OldTableKey, Ref_Count) ->
	Size = antidote_crdt_bigset_shard : size(Shard),
	if 
		Size < Max_Count div 4 andalso Siblings /= [] -> 
			SiblingKey = lists:last(Siblings),
			{ok, SiblingsTableKey} = antidote_crdt_bigset_keytree : get_key(SiblingKey, Tree),
			[{_, Sibling_Ref_Count, {_SiblingKey, Siblings2, SiblingContent}= _Sibling}] = ets:lookup(Table, SiblingsTableKey),
			SiblingSize = length(SiblingContent),
			Key2 = lists:last(Siblings2),
			if
				Key == Key2 andalso SiblingSize < (Max_Count div 2) ->
					NewKey = (Key + SiblingKey) div 2,
					NewShard = {NewKey, lists : droplast(Siblings), antidote_crdt_bigset_shard : merge_content(Content, SiblingContent)},
					if 
						% intermediate version, can be deleted immediately
						Ref_Count == 0 ->
							ets:delete(Table, OldTableKey);
						% belongs to another snapshot, so mustn't be deleted at this point
						true ->
							ok
					end,
					if 
						% intermediate version, can be deleted immediately
						Sibling_Ref_Count == 0 ->
							ets:delete(Table, SiblingsTableKey);
						% belongs to another snapshot, so mustn't be deleted at this point
						true ->
							ok
					end,
					Time = erlang:system_time(),
					Value = unique(),
					ets:insert(Table, {{NewKey, Value, Time}, 0, NewShard}),
					{Big, Hash_Range, Max_Count, antidote_crdt_bigset_keytree : replace(NewKey, {Value, Time}, Tree), Table, ID, VV};
				true ->
					remove_intermediate(BigSet, OldTableKey, Ref_Count, Shard)
			end;				
		Size > Max_Count ->
			if 
				%% splitting not allowed, maximum tree depth reached
				Key rem 2 == 1 -> 
					remove_intermediate(BigSet, OldTableKey, Ref_Count, Shard);
				%% splitting allowed
				true ->
					{{Upper_Key, _Upper_Siblings, _Upper_Content} = Upper_Shard,{Lower_Key, _Lower_Siblings, _Lower_Content} = Lower_Shard} 
						= antidote_crdt_bigset_shard : split(Shard),
					Time = erlang:system_time(),
					V1 = unique(),
					V2 = unique(),
					if 
						% intermediate version, can be deleted immediately
						Ref_Count == 0 ->
							ets:delete(Table, OldTableKey);
						% belongs to another snapshot, so mustn't be deleted at this point
						true ->
							ok
					end,
					ets:insert(Table, [{{Lower_Key, V1, Time}, 0, Lower_Shard},{{Upper_Key, V2, Time}, 0, Upper_Shard}]),				
					{Big, Hash_Range, Max_Count, 
					 	antidote_crdt_bigset_keytree : insert_two(Lower_Key, Upper_Key, {V1, Time}, {V2, Time}, Tree), Table, ID, VV}
			end;
		true -> 
			remove_intermediate(BigSet, OldTableKey, Ref_Count, Shard)
	end.

% delete intermediate versions
-spec remove_intermediate(bigset(), tablekey(), integer(), antidote_crdt_bigset_shard:shard()) -> bigset().
remove_intermediate({Big, Hash_Range, Max_Count, Tree, Table, ID, VV}=BigSet, {Key, _, _} = TableKey, Ref_Count, Shard)->
	if 
		% intermediate version, can be deleted immediately
		Ref_Count == 0 ->
			ets:update_element(Table, TableKey, {3, Shard}),
			BigSet;
		% belongs to another snapshot, so mustn't be deleted at this point
		true ->
			Value = unique(),
			Time = erlang: system_time(),
			ets:insert(Table, {{Key, Value, Time}, 0, Shard}),
			{Big, Hash_Range, Max_Count, antidote_crdt_bigset_keytree : replace(Key, {Value, Time}, Tree), Table, ID, VV}
	end.

%% snapshot is deleted
%% shards manipulated by that snapshot can be removed from the table because no other
%% snapshot references the same version
-spec remove_tokens(atom(), [{tablekey(), integer()}])->ok.
remove_tokens(_Table, []) ->
	ok;
remove_tokens(Table, [{Key, Inc}|Rest]) ->
	Counter = ets:update_counter(Table, Key, Inc),
	if 
		Counter == 0 ->
			ets:delete(Table, Key);
		true ->
			ok
	end,
	remove_tokens(Table, Rest).

%% is called only when the materializer applies its garbage collection
%% drops each entry without a token that was added before the last GC
%% tokenized entries are removed separately as they may belong to a snapshot
-spec delete_old(atom()) -> ok.
delete_old(Table)->
	ets:safe_fixtable(Table, true),
	LastGC = ets:lookup_element(Table, "LastGC", 2),
	delete_old(Table, ets:first(Table), LastGC+(erlang:system_time()-LastGC)div 2).
-spec delete_old(atom(), tablekey(), erlang:system_time()) -> ok.
delete_old(Table, '$end_of_table', _LastGC)->
	ets:update_element(Table, "LastGC", {2, erlang:system_time()}),
	ets:safe_fixtable(Table, false),
	ok;
delete_old(Table, "LastGC", LastGC) ->
	delete_old(Table, ets:next(Table, "LastGC"), LastGC);
delete_old(Table, {_Key, _Version, Time}=TableKey, LastGC)->
	if
		Time < LastGC ->
			Ref_Count = ets:lookup_element(Table, TableKey, 2),
			if 
				Ref_Count == 0 ->
					ets:delete(Table, TableKey);
				true ->
					ok
			end,
			ok;
		true ->
			ok
	end,
	delete_old(Table, ets:next(Table, TableKey), LastGC).

%% new snapshot created
%% mark all its shards with that snapshot's token
-spec add_tokens(antidote_crdt_bigset_keytree : tree(), atom()) -> ok.
add_tokens(Tree, Table)->
	add_tokens_helper(antidote_crdt_bigset_keytree : get_all(Tree), Table).
-spec add_tokens_helper([tablekey()], atom()) -> ok.
add_tokens_helper([], _Table)->
	ok;
add_tokens_helper([Key|Rest], Table)->
	ets:update_counter(Table, Key, 1),
	add_tokens_helper(Rest, Table).

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
	H_Elem = erlang:phash2(Elem, 1048576),
    Elems = [<<"li">>, <<"manu">>],
	H_Elem2 = erlang:phash2(<<"li">>, 1048576),
	H_Elem3 = erlang:phash2(<<"manu">>, 1048576),
    Set1 = new(),
    {ok, DownstreamOp1} = downstream({add, Elem}, Set1),
    ?assertMatch([{H_Elem, Elem, _, _}], DownstreamOp1),
    {ok, DownstreamOp2} = downstream({add_all, Elems}, Set1),
	%% manu and li are exchanged because DownstreamOp2 is sorted according to the hashed element
    ?assertMatch([{H_Elem3, <<"manu">>, _, _}, {H_Elem2, <<"li">>, _, _}], DownstreamOp2),
    {ok, Set2} = update(DownstreamOp1, Set1),
    ?assertEqual([Elem], value(Set2)),
    {ok, Set3} = update(DownstreamOp2, Set2),
    ?assertEqual([<<"foo">>] ++ lists : sort(Elems), lists: sort(value(Set3))).

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

seq_test() ->
    Elems = lists: seq(1,2000),
    Set1 = new(32, 475),
    {ok, DownstreamOp} = downstream({add_all, Elems}, Set1),
    {ok, Set2} = update(DownstreamOp, Set1),
	{ok, DownstreamOp2} = downstream({remove_all, Elems}, Set2),
	{ok, Set3} = update(DownstreamOp2, Set2),
    ?assertEqual([], value(Set3)).

add_100_test() ->
    Elems = lists: seq(1,23000),
    Set1 = new(32, 475),
    {ok, DownstreamOp2} = downstream({add_all, Elems}, Set1),
    {ok, Set2} = update(DownstreamOp2, Set1),
    ?assertEqual(Elems, value(Set2)).

equal_test() ->
    Elems = [<<"a">>, <<"b">>, <<"c">>, <<"d">>, <<"e">>],
    Set1 = new(32, 4),
	Set5 = new(32, 4),
    {ok, DownstreamOp2} = downstream({add_all, Elems}, Set1),
    ?assertMatch([{_, <<"a">>, _, _}, {_, <<"b">>, _, _}, {_, <<"c">>, _, _}, {_, <<"d">>, _, _}, {_, <<"e">>, _, _}
				  ], lists : keysort(2,DownstreamOp2)),
	%% Set is split in 2 shards because it has 5 elements while a maximum of 4 elements fit into one shard
    {ok, Set2} = update(DownstreamOp2, Set1),
	Elems2 = lists: delete(<<"a">>, Elems),
	{ok, DownstreamOp3} = downstream({remove, <<"a">>}, Set2),
	{ok, Set3} = update(DownstreamOp3, Set2),
	{ok, DownstreamOp4} = downstream({add_all, Elems2}, Set5),
	%% This other set is not split, because only 4 elements are added
	{ok, Set4} = update(DownstreamOp4, Set5),
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
	Set8 = new(),
	Set9 = new(),
    %% Add an element then remove it
    {ok, Op1} = downstream({add, <<"foo">>}, Set1),
    {ok, Set2} = update(Op1, Set1),
    ?assertEqual([<<"foo">>], value(Set2)),
    {ok, Op2} = downstream({remove, <<"foo">>}, Set2),
    {ok, Set3} = update(Op2, Set2),
    ?assertEqual([], value(Set3)),

    %% Add many elements then remove part
    {ok, Op3} = downstream({add_all, [<<"foo">>, <<"li">>, <<"manu">>]}, Set9),
    {ok, Set4} = update(Op3, Set9),
    ?assertEqual([<<"foo">>, <<"li">>, <<"manu">>], lists: sort(value(Set4))),

    {ok, Op5} = downstream({remove_all, [<<"foo">>, <<"li">>]}, Set4),
    {ok, Set5} = update(Op5, Set4),
    ?assertEqual([<<"manu">>], value(Set5)),

    %% Remove more than current have
    {ok, Op6} = downstream({add_all, [<<"foo">>, <<"li">>, <<"manu">>]}, Set8),
    {ok, Set6} = update(Op6, Set8),
    {ok, Op7} = downstream({remove_all, [<<"manu">>, <<"test">>]}, Set6),
    {ok, Set7} = update(Op7, Set6),
    ?assertEqual([<<"foo">>, <<"li">>], value(Set7)).

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

