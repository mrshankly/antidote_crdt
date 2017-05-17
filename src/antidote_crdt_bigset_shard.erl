%% @author Luehk
%% @doc @todo Add description to antidote_crdt_bigset_shard.

-module(antidote_crdt_bigset_shard).  
 
-include("antidote_crdt.hrl").
  
%% Callbacks
-export([value/1,
		 contains/3,
		 get_tokens/3,
		 new/2,
		 to_binary/1,
		 from_binary/1,
		 update_shard/2,
		 size/1,
		 is_bottom/1,
		 merge_content/2,
		 split/2
        ]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-endif.

-export_type([shard/0]).
-type shard() ::  {key(), siblings(), orddict:orddict({elem_hash(), elem()}, tokens())}.
-type binary_shard() :: binary(). %% A binary that from_binary/1 will operate on.
-type key() :: integer().
-type siblings() :: [key()].
-type content() :: [{{elem_hash(), elem()}, tokens()}].
-type elem() :: term().
-type elem_hash() :: integer().
-type token() :: binary().
-type tokens() :: [token()].

-spec new(integer(), [integer()]) -> shard().
new(Key, Siblings) ->
    {Key, Siblings, orddict:new()}.

-spec size(shard()) -> integer().
size({_Key, _Siblings, Content}) ->
	orddict : size(Content).

-spec contains(elem_hash(), elem(), shard()) -> boolean().
contains(H_Elem, Elem, {_Key, _Siblings, Content}) ->
	orddict : is_key({H_Elem, Elem}, Content).

-spec get_tokens(elem_hash(), elem(), shard()) -> [token()].
get_tokens(H_Elem, Elem, {_Key, _Siblings, Content}) ->
	get_tokens_helper(orddict : is_key({H_Elem, Elem}, Content), H_Elem, Elem, Content).

-spec get_tokens_helper(boolean(), elem_hash(), elem(), content()) -> [token()].
get_tokens_helper(true, H_Elem, Elem, Content) ->
	orddict : fetch({H_Elem, Elem}, Content);
get_tokens_helper(false, _H_Elem, _Elem, _Content) ->
	[].								  

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

-include("riak_dt_tags.hrl").
-define(TAG, ?DT_BIGSET_SHARD_TAG).
-define(V1_VERS, 1).

-spec to_binary(shard()) -> binary_shard().
to_binary(Shard) ->
    %% @TODO something smarter
    <<?TAG:8/integer, ?V1_VERS:8/integer, (term_to_binary(Shard))/binary>>.

-spec from_binary(<<_:16,_:_*8>>) -> {'ok', shard()}.
from_binary(<<?TAG:8/integer, ?V1_VERS:8/integer, Bin/binary>>) ->
    %% @TODO something smarter
    {ok, binary_to_term(Bin)}.

%% @doc apply downstream operations and update a shard().
-spec update_shard([{elem_hash(), elem(), tokens(), tokens()}], shard()) -> {ok, shard()}.
update_shard([], Shard) ->
    {ok, Shard};
update_shard(Ops, {Key, Siblings, Content}) ->
  	{ok, {Key, Siblings, update_shard_helper(Ops, Content)}}.

-spec update_shard_helper([{elem_hash(), elem(), tokens(), tokens()}], content()) -> content().
update_shard_helper([], Content) ->
		Content;
update_shard_helper(Ops, []) ->
    lists:foldl(
        fun({H_Elem, Elem, ToAdd, ToRemove}, Content) ->
            Content ++ apply_downstream(H_Elem, Elem, [], ToAdd, ToRemove)
        end,
        [],
        Ops
    );
update_shard_helper([{H_Elem1, Elem1, ToAdd, ToRemove}|OpsRest]=Ops,  [{{H_Elem2, Elem2}, CurrentTokens}|ContentRest]=Content) ->
    if
        {H_Elem1, Elem1} == {H_Elem2, Elem2} ->
            apply_downstream(H_Elem1, Elem1, CurrentTokens, ToAdd, ToRemove) ++ update_shard_helper(OpsRest, ContentRest);
		%% we sorted the element list first and after that performed a keysort on H_Elem, where the keysort is stable,
		%% so for equal H_Elem1 and 2, looking at Elem1 and 2 works
		(H_Elem1 == H_Elem2 andalso Elem1 > Elem2) orelse (H_Elem1 > H_Elem2) ->
            [{{H_Elem2, Elem2}, CurrentTokens} | update_shard_helper(Ops, ContentRest)];
        true ->
            apply_downstream(H_Elem1, Elem1, [], ToAdd, ToRemove) ++ update_shard_helper(OpsRest, Content)
    end.

%% @private create an orddict entry from a downstream op
- spec apply_downstream(elem_hash(), elem(), tokens(), tokens(), tokens())->content().
apply_downstream(H_Elem, Elem, CurrentTokens, ToAdd, ToRemove) ->
    Tokens = (CurrentTokens ++ ToAdd) -- ToRemove,
    case Tokens of
        [] ->
            [];
        _ ->
            [{{H_Elem, Elem}, Tokens}]
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
		{H_Elem1, Elem1} == {H_Elem2, Elem2} ->
			[{{H_Elem1, Elem1}, Tokens1 ++ lists : subtract(Tokens2, Tokens1)} | merge_content(ContentRest1, ContentRest2)];
		(H_Elem1 == H_Elem2 andalso Elem1 > Elem2) orelse (H_Elem1 > H_Elem2) ->
            [{H_Elem2, Elem2, Tokens2} | merge_content(Content1, ContentRest2)];
        true ->
            [{H_Elem1, Elem1, Tokens1} | merge_content(ContentRest1, Content2)]
	end.
		
-spec split(shard(), integer()) -> {shard(), shard()}.
split({Key, Siblings, Content}, Hash_Range) ->
	if 
		Siblings == [] ->
			KeyVal = Hash_Range div 4;
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
		H_Elem >= Key -> 
			lower_half(Key, ContentRest);
		true -> 
			[{{H_Elem, Elem}, Tokens}] ++ lower_half(Key, ContentRest)
	end.
		

is_bottom({_Key, _Siblings, Content}) -> 
	{_Key, _Siblings, NewContent} = new(0, []),
	Content == NewContent.

%% ===================================================================
%% EUnit tests
%% ===================================================================
-ifdef(TEST).

-endif.
