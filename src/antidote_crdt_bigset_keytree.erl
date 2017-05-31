%% @author Luehk
%% @doc @todo Add description to antidote_crdt_bigset_shardtree.

-module(antidote_crdt_bigset_keytree).
 
-export([init/2, insert_two/5, get_key/2, get_all/1, replace/3]).
-define(EMPTY_NODE, {node, 'empty'}).
-type tree() :: ?EMPTY_NODE
                          | {node,{integer(), any(), tree(), tree()}}.


%% @doc Initialize the root of the tree
-spec init(integer(), any()) -> tree(). 
init(K, V) ->
  	{node, {K, V, ?EMPTY_NODE, ?EMPTY_NODE}}.

%% @doc Return all the shards in the tree
-spec get_all(tree()) -> [{integer(), integer()}].
get_all(_Tree = ?EMPTY_NODE) ->
  	[];
get_all(_Tree = {node, {NodeK, NodeV, ?EMPTY_NODE, ?EMPTY_NODE}}) ->
  	[{NodeK, NodeV}];
get_all(_Tree = {node, {_NodeK, _V, Left, Right}}) ->
	lists : append(get_all(Left), get_all(Right)).

%% @doc Find the right shard for a given key
%% Shards are stored in leaves, so we go down the tree until we end up in a leaf
%%
-spec get_key(integer(), tree()) -> {ok, {integer(), binary()}}.
get_key(_K, _Tree = {node, {NodeK, NodeV, ?EMPTY_NODE, ?EMPTY_NODE}}) ->
  	{ok, {NodeK, NodeV}};
get_key(K, _Tree = {node, {NodeK, _V, Left, Right}}) ->
  	if  K =<  NodeK -> get_key(K, Left)
  		; K > NodeK -> get_key(K, Right)
  	end.

-spec insert_two(integer(), integer(), any(), any(), tree()) -> tree().
insert_two(K1, K2, V1, V2, _Tree = {node, {NodeK, NodeV, ?EMPTY_NODE, ?EMPTY_NODE}}) ->
	{node, {NodeK, NodeV, {node, {K1, V1, ?EMPTY_NODE, ?EMPTY_NODE}}, {node, {K2, V2, ?EMPTY_NODE, ?EMPTY_NODE}}}};
insert_two(K1, K2, V1, V2, _Tree = {node, {NodeK, NodeV, Left, Right}}) ->
	%% we can take K1 or K2 here
  	if K1 < NodeK ->
      	{node, {NodeK, NodeV, insert_two(K1, K2, V1, V2, Left), Right}}
   	; K1  > NodeK ->
      	{node, {NodeK, NodeV, Left, insert_two(K1, K2, V1, V2, Right)}}
  	end.

%% @doc Replace a key in the tree
%%
-spec replace(integer(), any(), tree()) -> tree().
replace(K, V, _Tree = {node, {NodeK, NodeV, Left, Right}}) ->
  	if K < NodeK ->
      	{node, {NodeK, NodeV, replace(K, V, Left), Right}}
   	; K  > NodeK ->
      	{node, {NodeK, NodeV, Left, replace(K, V, Right)}}
	; K == NodeK ->
		{node, {NodeK, V, ?EMPTY_NODE, ?EMPTY_NODE}}  
  	end.


