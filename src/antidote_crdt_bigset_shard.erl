%% @author Luc Francois (francois.luc93@gmail.com)

-module(antidote_crdt_bigset_shard).  
  
%% Callbacks
-export([new/0,
		 update_shard/2,
		 merge/2,
		 split/3
        ]).

-export_type([shard/0]).
-type shard() ::  orddict:orddict(elem(), tokens()).
-type elem() :: term().
-type key() :: {integer(), integer()}.
-type token() :: binary().
-type tokens() :: [token()].
-define(HASH_MIN, 0).

-spec new() -> shard().
new() ->
    orddict:new().

%% @doc apply downstream operations and update a shard().
-spec update_shard({elem(), tokens(), tokens()}, shard()) -> {ok, shard()}.
update_shard(Op, Shard) ->
  	{ok, update_shard_helper(Op, Shard)}.

-spec update_shard_helper({elem(), tokens(), tokens()}, shard()) -> shard().
update_shard_helper({Elem, ToAdd, ToRemove}=_Op, []) ->
    apply_downstream(Elem, [], ToAdd, ToRemove);
update_shard_helper({Elem1, ToAdd, ToRemove}=Op,  [{Elem2, CurrentTokens}|ShardRest]=Shard) ->
    case Elem1 of
        Elem2 ->
            apply_downstream(Elem1, CurrentTokens, ToAdd, ToRemove) ++  ShardRest;
		Elem when Elem > Elem2 ->
            [{Elem2, CurrentTokens} | update_shard_helper(Op, ShardRest)];
        Elem when Elem < Elem2 ->
            apply_downstream(Elem, [], ToAdd, ToRemove) ++ Shard
    end.

%% @private create an orddict entry from a downstream op
- spec apply_downstream(elem(), tokens(), tokens(), tokens())->shard().
%% remove
apply_downstream(Elem, CurrentTokens, [], VV) ->
	case remove_tokens(CurrentTokens, VV) of 
		[] ->
			[];
		Tokens ->
			[{Elem, Tokens}]
	end;
%% add
apply_downstream(Elem, CurrentTokens, [ID], VV) ->
	%% update old entry under that ID or create a new entry
    [{Elem, orddict : store(ID, orddict : fetch(ID, VV), CurrentTokens)}].

remove_tokens([], _VV) ->
	[];
remove_tokens(CurrentTokens, []) ->
	CurrentTokens;
remove_tokens([Head|Rest1]=CurrentTokens, [{Key2, Counter2}|Rest2]=VV) ->
	case Head of
		{Key1, _Counter1} when Key1 > Key2 -> 
			remove_tokens(CurrentTokens, Rest2);
		{Key1, Counter1} when Key1 < Key2 ->
			[{Key1, Counter1}] ++ remove_tokens(Rest1, VV);
		{_Key1, Counter1} when Counter2 >= Counter1 ->
			remove_tokens(Rest1, Rest2);
		{Key1, Counter1} when Counter2 < Counter1->
			[{Key1, Counter1}] ++ remove_tokens(Rest1, Rest2)
	end.

-spec merge(shard(), shard()) -> shard().
merge(Shard1, Shard2) ->
	Fun = fun(_, V1, _) ->
        V1
    end,
	orddict:merge(Fun, Shard1, Shard2).

-spec split(shard(), key(), integer()) -> {shard(), shard(), shard()}.
split(Shard, {Min, Max} = _Key, Hash_Max) ->
	List = orddict:to_list(Shard),
	case Min of
		min -> NewMin = ?HASH_MIN;
		_ -> NewMin = Min
	end,
	case Max of
		max -> NewMax = Hash_Max;
		_ -> NewMax = Max
	end,
	% shard is split in 3
	Interval = (NewMax - NewMin) div 3,
	{Low, Temp} = lists:partition(fun({{A, _}, _}) -> A < NewMin + Interval end, List),
	{Mid, Up} = lists:partition(fun({{A, _}, _}) -> A < NewMin + 2*Interval end, Temp),
	Lower_Shard = orddict:from_list(Low),
	Middle_Shard = orddict:from_list(Mid),
	Upper_Shard = orddict:from_list(Up),
	{{{Min, NewMin + Interval}, Lower_Shard}, {{NewMin + Interval, NewMin + 2*Interval}, Middle_Shard}, {{NewMin + 2*Interval, Max}, Upper_Shard}}.
