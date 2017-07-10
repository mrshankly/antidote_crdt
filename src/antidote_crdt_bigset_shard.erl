%% @author Luc Francois (francois.luc93@gmail.com)

-module(antidote_crdt_bigset_shard).  
  
%% Callbacks
-export([new/0,
		 update_shard/2,
		 merge/2,
		 split/2
        ]).

-export_type([shard/0]).
-type shard() ::  orddict:orddict(elem(), tokens()).
-type elem() :: term().
-type key() :: {integer(), integer()}.
-type token() :: binary().
-type tokens() :: [token()].

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
	Tokens = remove_tokens(CurrentTokens, VV),
	case Tokens of 
		[] ->
			[];
		_ ->
			[{Elem, remove_tokens(CurrentTokens, VV)}]
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
		{Key1, Counter1} when Counter2 =< Counter1->
			[{Key1, Counter1}] ++ remove_tokens(Rest1, Rest2)
	end.

-spec merge(shard(), shard()) -> shard().
merge(Shard1, Shard2) ->
	Fun = fun(_, V1, _) ->
        V1
    end,
	orddict:merge(Fun, Shard1, Shard2).

-spec split(shard(), key()) -> {shard(), shard(), shard()}.
split(Shard, {Min, Max} = _Key) ->
	Third = orddict:size(Shard) div 3,
	List = orddict:to_list(Shard),
	%% Depending on the shard size, Upper_Shard has 0, 1 or 2 elements more than the other two, but that doesn't really matter
	Low = lists:sublist(List, Third),
	[{MidHead, _}|_] = Mid = lists:sublist(List, Third+1, Third),
	[{UpHead,_}|_] = Up = lists:sublist(List, 2*Third+1, Third+2),
	Lower_Shard = orddict:from_list(Low),
	Middle_Shard = orddict:from_list(Mid),
	Upper_Shard = orddict:from_list(Up),
	{{{Min, MidHead}, Lower_Shard}, {{MidHead, UpHead}, Middle_Shard}, {{UpHead, Max}, Upper_Shard}}.
