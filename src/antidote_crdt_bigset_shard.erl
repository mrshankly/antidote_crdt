%% @author Luehk
%% @doc @todo Add description to antidote_crdt_bigset_shard.

-module(antidote_crdt_bigset_shard).  
  
%% Callbacks
-export([value/1,
		 contains/3,
		 new/1,
		 update_shard/2,
		 size/1,
		 merge_content/2,
		 split/1
        ]).

-export_type([shard/0]).
-type shard() ::  {key(), siblings(), orddict:orddict({elem_hash(), elem()}, tokens())}.
-type key() :: integer().
-type siblings() :: [key()].
-type content() :: [{{elem_hash(), elem()}, tokens()}].
-type elem() :: term().
-type elem_hash() :: integer().
-type token() :: binary().
-type tokens() :: [token()].

-spec new(integer()) -> shard().
new(Key) ->
    {Key, [], orddict:new()}.

-spec size(shard()) -> integer().
size({_Key, _Siblings, Content}) ->
	orddict : size(Content).

-spec contains(elem_hash(), elem(), shard()) -> boolean().
contains(H_Elem, Elem, {_Key, _Siblings, Content}) ->
	orddict : is_key({H_Elem, Elem}, Content).

%% @doc return all existing elements in the `shard()'.
-spec value(shard()) -> [elem()].
value({_Key, _Siblings, Content}) ->
    KeysWithHash = orddict:fetch_keys(Content),
	value_helper(KeysWithHash).

%% @doc the keys contain the hashed element and the element, but we want only the latter one
-spec value_helper([{elem_hash(), elem()}]) -> [elem()].
value_helper([]) ->
    [];
value_helper([{_H_Elem, Elem}|Rest]) ->
    [Elem]++value_helper(Rest). 

%% @doc apply downstream operations and update a shard().
-spec update_shard({elem_hash(), elem(), tokens(), tokens()}, shard()) -> {ok, shard()}.
update_shard(Op, {Key, Siblings, Content}) ->
  	{ok, {Key, Siblings, update_shard_helper(Op, Content)}}.

-spec update_shard_helper({elem_hash(), elem(), tokens(), tokens()}, content()) -> content().
update_shard_helper({H_Elem, Elem, ToAdd, ToRemove}=_Op, []) ->
    apply_downstream(H_Elem, Elem, [], ToAdd, ToRemove);
update_shard_helper({H_Elem1, Elem1, ToAdd, ToRemove}=Op,  [{{H_Elem2, Elem2}, CurrentTokens}|ContentRest]=Content) ->
    if
        {H_Elem1, Elem1} == {H_Elem2, Elem2} ->
            apply_downstream(H_Elem1, Elem1, CurrentTokens, ToAdd, ToRemove) ++  ContentRest;
		%% we sorted the element list first and after that performed a keysort on H_Elem, where the keysort is stable,
		%% so for equal H_Elem1 and 2, looking at Elem1 and 2 works
		(H_Elem1 == H_Elem2 andalso Elem1 > Elem2) orelse (H_Elem1 > H_Elem2) ->
            [{{H_Elem2, Elem2}, CurrentTokens} | update_shard_helper(Op, ContentRest)];
        true ->
            apply_downstream(H_Elem1, Elem1, [], ToAdd, ToRemove) ++ Content
    end.

%% @private create an orddict entry from a downstream op
- spec apply_downstream(elem_hash(), elem(), tokens(), tokens(), tokens())->content().
%% remove
apply_downstream(H_Elem, Elem, CurrentTokens, [], VV) ->
	Tokens = remove_tokens(CurrentTokens, VV),
	if 
		Tokens == [] ->
			[];
		true ->
			[{{H_Elem, Elem}, remove_tokens(CurrentTokens, VV)}]
	end;
%% add
apply_downstream(H_Elem, Elem, CurrentTokens, [ID], VV) ->
	%% update old entry under that ID or create a new entry
    [{{H_Elem, Elem}, orddict : store(ID, orddict : fetch(ID, VV), CurrentTokens)}].

remove_tokens([], _VV) ->
	[];
remove_tokens(CurrentTokens, []) ->
	CurrentTokens;
remove_tokens([{Key1, Counter1}|Rest1]=CurrentTokens, [{Key2, Counter2}|Rest2]=VV) ->
	if
		Key1 > Key2 -> 
			remove_tokens(CurrentTokens, Rest2);
		Key1 < Key2 ->
			[Key1, Counter1] ++ remove_tokens(Rest1, VV);
		Counter2 >= Counter1 ->
			remove_tokens(Rest1, Rest2);
		true ->
			[Key1, Counter1] ++ remove_tokens(Rest1, Rest2)
	end.

-spec merge_content(content(), content()) -> content().
merge_content([], []) ->
	[];
merge_content(Content1, []) ->
	Content1;
merge_content([], Content2) ->
	Content2;
merge_content([{{H_Elem1, Elem1}, Tokens1}| ContentRest1]=Content1, [{{H_Elem2, Elem2}, Tokens2}| ContentRest2]= Content2) ->
	if 
		(H_Elem1 == H_Elem2 andalso Elem1 > Elem2) orelse (H_Elem1 > H_Elem2) ->
            [{{H_Elem2, Elem2}, Tokens2} | merge_content(Content1, ContentRest2)];
        true ->
            [{{H_Elem1, Elem1}, Tokens1} | merge_content(ContentRest1, Content2)]
	end.
		
-spec split(shard()) -> {shard(), shard()}.
split({Key, Siblings, Content}) ->
	if 
		Siblings == [] ->
			KeyVal = Key div 2;
		true ->
			KeyVal = abs(Key - lists:last(Siblings)) div 4
	end,
	Upper_Key = Key + KeyVal,
	Lower_Key = Key - KeyVal,
	Upper_Siblings = lists : append(Siblings, [Lower_Key]),
	Lower_Siblings = lists : append(Siblings, [Upper_Key]),
	Lower_Content = lower_half(Key, Content),
	Upper_Content = lists : subtract(Content, Lower_Content), 
	{{Upper_Key, Upper_Siblings, Upper_Content},{Lower_Key, Lower_Siblings, Lower_Content}}.

-spec lower_half(integer(), content()) -> content().
lower_half(_Key, []) -> 
	[];
lower_half(Key, [{{H_Elem, Elem}, Tokens}| ContentRest]=_Content) ->
	if 
		H_Elem > Key -> 
			lower_half(Key, ContentRest);
		true -> 
			[{{H_Elem, Elem}, Tokens}] ++ lower_half(Key, ContentRest)
	end.

