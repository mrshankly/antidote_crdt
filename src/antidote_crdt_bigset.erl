%% @author Luc Francois, francois.luc93@gmail.com
-module(antidote_crdt_bigset).
-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl"). 
-endif. 
-include("antidote_crdt.hrl").


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

-define(MAX_COUNT, 350).
-define(MIN_COUNT, ?MAX_COUNT div 4).
-define(MIN_SIBLING, ?MAX_COUNT div 2).
-define(ZERO_REFS, 0).
-define(SHARD_POS, 3).
-define(GC_FACTOR, 4/5).

-behaviour(antidote_crdt).

-export_type([bigset/0, binary_bigset/0, bigset_op/0, elem/0, token/0]).
 
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
-type downstream_op() :: [{elem(), tokens(), tokens()}].
-type elem() :: term(). 
-type key() :: {integer(), integer()}.
-type tablekey() :: {{integer(), integer()}, {binary(), erlang:system_time()}}.
-type token() :: binary().
-type tokens() :: [token()].
	
-spec new() -> bigset().
new() ->
	Table = ets:new(erlang:binary_to_atom(unique(), latin1), [set, public, named_table, {keypos,1}, {heir,none}, {write_concurrency,false}, 
		{read_concurrency,true}]),
	Time = erlang:system_time(),
	Value = unique(),
	ID = unique(),
	ets:insert(Table, {"LastGC", 0}),
	ets:insert(Table, {{{min, max}, {Value, Time}}, 0, antidote_crdt_bigset_shard : new()}),
	{big, antidote_crdt_bigset_keytree : init({Value, Time}), Table, ID, [{ID,0}]}.

%% @doc return all existing elements in the bigset
-spec value(bigset()) -> [elem()].
value({_Big, Tree, Table, _ID, _VV}=_BigSet) ->
    lists:usort(value_helper(antidote_crdt_bigset_keytree : get_all(Tree), Table)).
	
-spec value_helper([integer()], atom()) -> [elem()].
value_helper([Key|Rest], Table) ->
	case Rest of
        [] ->
			Shard = ets:lookup_element(Table, Key, ?SHARD_POS),
			case Shard of 
				[] -> 
					[];
				_ ->
					orddict:fetch_keys(Shard)
			end;
        _ ->
			Shard = ets:lookup_element(Table, Key, ?SHARD_POS),
			case Shard of 
				[] -> 
					[] ++ value_helper(Rest, Table);
				_ ->
					orddict:fetch_keys(Shard) ++ value_helper(Rest, Table)
			end
	end.

%% @doc return true if the bigset contains the element
-spec contains(elem(), bigset()) -> boolean().
contains(Elem, {_Big, Tree, Table, _ID, _VV} = _BigSet) ->
	TableKey = antidote_crdt_bigset_keytree : get_key(Elem, Tree),
	orddict : is_key(Elem, ets:lookup_element(Table, TableKey, ?SHARD_POS)). 

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
    crypto:strong_rand_bytes(10).

%% @doc generate downstream operations.
%% If the operation is add or add_all, send the own replica ID
%% so every other replica can increment the according entry in its version vector
%% If the operation is remove or remove_all, send the current Version Vector
%% so every other replica can verify whether concurrent adds have been seen at source
-spec downstream(bigset_op(), bigset()) -> {ok, downstream_op()}.
downstream({add, Elem}, BigSet) ->
    downstream({add_all, [Elem]}, BigSet);
downstream({add_all, Elems}, BigSet) ->
    CreateDownstream = fun(Elem, ID, _VV) ->
        {Elem, [ID], []}
    end,
    {ok, create_downstreams(CreateDownstream, Elems, BigSet, [])};
downstream({remove, Elem}, BigSet) ->
    downstream({remove_all, [Elem]}, BigSet);
downstream({remove_all, Elems}, BigSet) ->
    CreateDownstream = fun(Elem, _ID, VV) ->
        {Elem, [], VV}
    end,
    {ok, create_downstreams(CreateDownstream, Elems, BigSet, [])};
downstream({reset, {}}, BigSet) ->
    % reset is like removing all elements
    downstream({remove_all, value(BigSet)}, BigSet).

%% @private generic downstream op creation for adds and removals
- spec create_downstreams(any(), [elem()], bigset(), downstream_op()) -> downstream_op().
create_downstreams(_CreateDownstream, [], _BigSet, DownstreamOps) ->
    DownstreamOps;
create_downstreams(CreateDownstream, [Elem|ElemsRest], {_Big, _Tree, _Table, ID, VV} = BigSet, DownstreamOps) ->
	DownstreamOp = CreateDownstream(Elem, ID, VV),
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
apply_downstreams([{Elem, [], _ToRemove} = Op|OpsRest], {_Big, Tree, Table, _ID, _VV} = BigSet) ->
	{Key, _} = TableKey = antidote_crdt_bigset_keytree : get_key(Elem, Tree),
	[{_, Ref_Count, Shard}] = ets:lookup(Table, TableKey),
	{ok, Shard2} = antidote_crdt_bigset_shard : update_shard(Op, Shard),
	apply_downstreams(OpsRest, pick_action(BigSet, Shard2, TableKey, Ref_Count, Key, remove));
%% add
apply_downstreams([{Elem, [ID2], _ToRemove}|OpsRest], {_Big, Tree, Table, ID, VV} = BigSet) ->
	VV2 = orddict : update_counter(ID2, 1, VV),
	{Key, _} = TableKey = antidote_crdt_bigset_keytree : get_key(Elem, Tree),
	[{_, Ref_Count, Shard}] = ets:lookup(Table, TableKey),
	{ok, Shard2} = antidote_crdt_bigset_shard : update_shard({Elem, [ID2], VV2}, Shard),
	{Big, Tree2, Table, ID, VV} = pick_action(BigSet, Shard2, TableKey, Ref_Count, Key, add),
	apply_downstreams(OpsRest, {Big, Tree2, Table, ID, VV2}).

-spec smallest_sibling(any(), any(), antidote_crdt_bigset_keytree:tree(), atom()) -> {antidote_crdt_bigset_shard:shard(), integer(), integer(), tablekey()}.
smallest_sibling(min, _Max, Tree, Table)->
	SiblingTableKey = antidote_crdt_bigset_keytree : get_key_right(min, Tree),
	[{_, Sibling_Ref_Count, Sibling}] = ets:lookup(Table, SiblingTableKey),
	{Sibling, orddict:size(Sibling), Sibling_Ref_Count, SiblingTableKey};
smallest_sibling(Min, max, Tree, Table) ->
    SiblingTableKey = antidote_crdt_bigset_keytree : get_key_left(Min, Tree),
	[{_, Sibling_Ref_Count, Sibling}] = ets:lookup(Table, SiblingTableKey),
	{Sibling, orddict:size(Sibling), Sibling_Ref_Count, SiblingTableKey};
smallest_sibling(Min, _Max, Tree, Table) ->
	SiblingTableKey1 = antidote_crdt_bigset_keytree : get_key_left(Min, Tree),
	[{_, Sibling_Ref_Count1, Sibling1}] = ets:lookup(Table, SiblingTableKey1),
	SizeLeft = orddict:size(Sibling1),
	SiblingTableKey2 = antidote_crdt_bigset_keytree : get_key_right(Min, Tree),
	[{_, Sibling_Ref_Count2, Sibling2}] = ets:lookup(Table, SiblingTableKey2),
	SizeRight = orddict:size(Sibling2),
	if
		SizeRight >= SizeLeft ->
			{Sibling2, SizeRight, Sibling_Ref_Count2, SiblingTableKey2};
		true ->
			{Sibling1, SizeLeft, Sibling_Ref_Count1, SiblingTableKey1}
	end.

-spec pick_action(bigset(), antidote_crdt_bigset_shard : shard(), tablekey(), integer(), key(), atom()) -> bigset().
pick_action({Big, Tree, Table, ID, VV} = BigSet, Shard, OldTableKey, Ref_Count, {Min, Max} = Key, Atom) ->
	case orddict:size(Shard) of
		Size when Atom == remove andalso Size < ?MIN_COUNT andalso {Min, Max} /= {min, max} ->  
			{Sibling, SiblingSize, Sibling_Ref_Count, {{SiblingMin, SiblingMax}, _} = SiblingTableKey} = smallest_sibling(Min, Max, Tree, Table),
			case SiblingSize of  
				 SiblingSize when SiblingSize < ?MIN_SIBLING ->
					NewKey = {min_bound(Min, SiblingMin), max_bound(Max, SiblingMax)},
					NewShard = antidote_crdt_bigset_shard : merge(Shard, Sibling),
					case Ref_Count of  
						% intermediate version, can be deleted immediately
						?ZERO_REFS ->
							ets:delete(Table, OldTableKey);
						_ -> ok
					end,
					case Sibling_Ref_Count of  
						% intermediate version, can be deleted immediately
						?ZERO_REFS ->
							ets:delete(Table, SiblingTableKey);
						_ -> ok
					end,
					Time = erlang:system_time(),
					Value = unique(),
					ets:insert(Table, {{NewKey, {Value, Time}}, ?ZERO_REFS, NewShard}),
					Temp = antidote_crdt_bigset_keytree : remove(Key, Tree),		
					{Big, antidote_crdt_bigset_keytree : replace({SiblingMin, SiblingMax}, 
						NewKey, {Value, Time}, Temp), Table, ID, VV};
				SiblingSize when SiblingSize >= ?MIN_SIBLING ->
					remove_intermediate(BigSet, OldTableKey, Ref_Count, Shard)
			end;
		Size when Size > ?MAX_COUNT ->
			{{K1, Lower_Shard}, {K2, Middle_Shard}, {K3, Upper_Shard}} = antidote_crdt_bigset_shard : split(Shard, Key),
			Time = erlang:system_time(),
			{V1, V2, V3} = {unique(), unique(), unique()},
			case Ref_Count of  
				% intermediate version, can be deleted immediately
				?ZERO_REFS ->
					ets:delete(Table, OldTableKey);
				_ -> ok
			end,	
			ets:insert(Table, [{{K1, {V1, Time}}, ?ZERO_REFS, Lower_Shard}, {{K2, {V2, Time}}, ?ZERO_REFS, Middle_Shard},{{K3, {V3, Time}}, ?ZERO_REFS, Upper_Shard}]),
			{Big, antidote_crdt_bigset_keytree : insert_three(K1, K2, K3, {V1, Time}, {V2, Time}, {V3, Time}, Tree), Table, ID, VV};
		_ -> 
			remove_intermediate(BigSet, OldTableKey, Ref_Count, Shard)
	end.

-spec min_bound(term(), term()) -> term().
min_bound(A, B) ->
	if 
		A == min ->
			A;
		B == min ->
			B;
		true ->
			erlang:min(A, B)
	end.

-spec max_bound(term(), term()) -> term().
max_bound(A, B) ->
	if 
		A == max ->
			A;
		B == max ->
			B;
		true ->
			erlang:max(A, B)
	end.

% delete intermediate versions
-spec remove_intermediate(bigset(), tablekey(), integer(), antidote_crdt_bigset_shard:shard()) -> bigset().
remove_intermediate({Big, Tree, Table, ID, VV}=BigSet, {Key, _} = TableKey, Ref_Count, Shard)->
	case Ref_Count of
		% intermediate version, can be deleted immediately
		?ZERO_REFS ->
			ets:update_element(Table, TableKey, {?SHARD_POS, Shard}),
			BigSet;
		% belongs to another snapshot, so mustn't be deleted at this point
		_ ->
			Value = unique(),
			Time = erlang: system_time(),
			ets:insert(Table, {{Key, {Value, Time}}, ?ZERO_REFS, Shard}),
			{Big, antidote_crdt_bigset_keytree : replace(Key, Key, {Value, Time}, Tree), Table, ID, VV}
	end.

%% snapshot is deleted
%% shards manipulated by that snapshot can be removed from the table because no other
%% snapshot references the same version
-spec remove_tokens(atom(), [{tablekey(), integer()}])->ok.
remove_tokens(_Table, []) ->
	ok;
remove_tokens(Table, [{Key, Inc}|Rest]) ->
	case ets:update_counter(Table, Key, Inc) of
		Counter == ?ZERO_REFS ->
			ets:delete(Table, Key);
		_ -> ok
	end,
	remove_tokens(Table, Rest).

%% is called only when the materializer applies its garbage collection
%% drops each entry without a token that was added before the last GC
%% tokenized entries are removed separately as they may belong to a snapshot
-spec delete_old(atom()) -> ok.
delete_old(Table)->
	ets:safe_fixtable(Table, true),
	LastGC = ets:lookup_element(Table, "LastGC", 2),
	delete_old(Table, ets:first(Table), LastGC + ?GC_FACTOR (erlang:system_time()-LastGC)).
-spec delete_old(atom(), tablekey(), erlang:system_time()) -> ok.
delete_old(Table, '$end_of_table', _LastGC)->
	ets:update_element(Table, "LastGC", {2, erlang:system_time()}),
	ets:safe_fixtable(Table, false),
	ok;
delete_old(Table, "LastGC", LastGC) ->
	delete_old(Table, ets:next(Table, "LastGC"), LastGC);
delete_old(Table, {_Key, {_Version, Time}}=TableKey, LastGC)->
	case {Time, ets:lookup_element(Table, TableKey, 2)} of
		{Time, ?ZERO_REFS} when Time < LastGC ->
			ets:delete(Table, TableKey);
		_ -> ok
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
    Elems = [<<"li">>, <<"manu">>],
    Set1 = new(),
    {ok, DownstreamOp1} = downstream({add, Elem}, Set1),
    ?assertMatch([{Elem, _, _}], DownstreamOp1),
    {ok, DownstreamOp2} = downstream({add_all, Elems}, Set1),
	%% manu and li are exchanged because DownstreamOp2 is sorted according to the hashed element
    ?assertMatch([{<<"manu">>, _, _}, {<<"li">>, _, _}], DownstreamOp2),
    {ok, Set2} = update(DownstreamOp1, Set1),
    ?assertEqual([Elem], value(Set2)),
    {ok, Set3} = update(DownstreamOp2, Set2),
    ?assertEqual([<<"foo">>] ++ lists : sort(Elems), lists: sort(value(Set3))).

add_much_test() ->
    Elems = [<<"a">>, <<"b">>, <<"c">>, <<"d">>, <<"e">>, <<"f">>, <<"g">>, 
			 	<<"h">>, <<"i">>, <<"j">>, <<"k">>, <<"l">>, <<"m">>, <<"n">>, <<"o">>, <<"p">>, <<"q">>],
    Set1 = new(),
    {ok, DownstreamOp2} = downstream({add_all, Elems}, Set1),
    ?assertMatch([{<<"a">>, _, _}, {<<"b">>, _, _}, {<<"c">>, _, _}, {<<"d">>, _, _}, {<<"e">>, _, _},
				  {<<"f">>, _, _}, {<<"g">>, _, _}, {<<"h">>, _, _}, {<<"i">>, _, _}, {<<"j">>, _, _},
				  {<<"k">>, _, _}, {<<"l">>, _, _}, {<<"m">>, _, _}, {<<"n">>, _, _}, {<<"o">>, _, _},
				  {<<"p">>, _, _}, {<<"q">>, _, _}], lists : keysort(1,DownstreamOp2)),
    {ok, Set2} = update(DownstreamOp2, Set1),
    ?assertEqual(Elems, lists: sort(value(Set2))),
	Elems2 = lists:delete(<<"f">>, Elems),
	{ok, DownstreamOp3} = downstream({remove_all, Elems2}, Set2),
	{ok, Set3} = update(DownstreamOp3, Set2),
	?assertEqual([<<"f">>], lists: sort(value(Set3))).

seq_test() ->
    Elems = lists: seq(1,1000),
    Set1 = new(),
    {ok, DownstreamOp} = downstream({add_all, Elems}, Set1),
    {ok, Set2} = update(DownstreamOp, Set1),
	{ok, DownstreamOp2} = downstream({remove_all, Elems}, Set2),
	{ok, Set3} = update(DownstreamOp2, Set2),
    ?assertEqual([], value(Set3)).

add_100_test() ->
    Elems = lists: seq(1,5000),
    Set1 = new(),
    {ok, DownstreamOp2} = downstream({add_all, Elems}, Set1),
    {ok, Set2} = update(DownstreamOp2, Set1),
    ?assertEqual(Elems, value(Set2)).

fill(0, List)->
	List;
fill(N, List)->
	fill(N-1, List++[unique()]).
	%fill(N-1, List++[erlang:binary_to_atom(unique(), latin1)]).

add_random_test() ->
    Elems = fill(8000, []),
    Set1 = new(),
    {ok, DownstreamOp2} = downstream({add_all, Elems}, Set1),
    {ok, Set2} = update(DownstreamOp2, Set1),
    ?assertEqual(lists:sort(Elems), value(Set2)),
	{ok, DownstreamOp3} = downstream({remove_all, Elems}, Set2),
    {ok, Set3} = update(DownstreamOp3, Set2),
	?assertEqual([], value(Set3)).

equal_test() ->
    Elems = [<<"a">>, <<"b">>, <<"c">>, <<"d">>, <<"e">>],
    Set1 = new(),
	Set5 = new(),
    {ok, DownstreamOp2} = downstream({add_all, Elems}, Set1),
    ?assertMatch([{<<"a">>, _, _}, {<<"b">>, _, _}, {<<"c">>, _, _}, {<<"d">>, _, _}, {<<"e">>, _, _}], lists : keysort(1,DownstreamOp2)),
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