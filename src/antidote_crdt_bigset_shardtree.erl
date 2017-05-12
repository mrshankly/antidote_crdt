%% @author Luehk
%% @doc @todo Add description to antidote_crdt_bigset_shardtree.

-module(antidote_crdt_bigset_shardtree).
 
-export([init/0, init/1, insert/3, remove/2, get_shard/2, get_all/1, replace/3]).
-define(EMPTY_NODE, {node, 'empty'}).
-type tree() :: ?EMPTY_NODE
                          | {node,{_K, _V, tree(), tree()}}.
%%-type inner_node() :: {term(), node, node}.
%%-type leaf() :: {term(), term(), shard()}.

%% @doc Initialize an empty binary tree node.
%%      This is how the root of the tree should be established.
%%
-spec init() -> tree().
init() ->
  	?EMPTY_NODE.

%% @doc Initialize the root of the tree
-spec init(antidote_crdt_bigset_shard : shard()) -> tree(). 
init({Key, Siblings, Content}) ->
  	insert(Key, {Key, Siblings, Content}, init()).

%% @doc Return all the shards in the tree
-spec get_all(tree()) -> [antidote_crdt_bigset_shard : shard()].
get_all(_Tree = ?EMPTY_NODE) ->
  	[];
get_all(_Tree = {node, {_NodeK, Shard, ?EMPTY_NODE, ?EMPTY_NODE}}) ->
  	[Shard];
get_all(_Tree = {node, {_NodeK, _V, Left, Right}}) ->
	lists : append(get_all(Left), get_all(Right)).

%% @doc Find the right shard for a given key
%% Shards are stored in leaves, so we go down the tree until we end up in a leaf
%%
-spec get_shard(integer(), tree()) -> {ok, antidote_crdt_bigset_shard : shard()}.
get_shard(_K, _Tree = {node, {_NodeK, Shard, ?EMPTY_NODE, ?EMPTY_NODE}}) ->
  	{ok, Shard};
get_shard(K, _Tree = {node, {NodeK, _V, Left, Right}}) ->
  	if  K <  NodeK -> get_shard(K, Left)
  		; K >=  NodeK -> get_shard(K, Right)
  	end.

%% @doc Insert a new Key into the Tree.
%%
-spec insert(integer(), antidote_crdt_bigset_shard : shard(), tree()) -> tree().
insert(K, V, _Tree = ?EMPTY_NODE) ->
  	{node, {K, V, init(), init()}};
insert(K, V, _Tree = {node, {NodeK, NodeV, Left, Right}}) ->
  	if K < NodeK ->
      	{node, {NodeK, NodeV, insert(K, V, Left), Right}}
   	; K  >= NodeK ->
      	{node, {NodeK, NodeV, Left, insert(K, V, Right)}}
  	end.

-spec remove(integer(), tree()) -> tree().
remove(_, _Tree = {node, {_, _, ?EMPTY_NODE, ?EMPTY_NODE}}) ->
 	?EMPTY_NODE;
remove(K, _Tree = {node, {NodeK, NodeV, Left, Right}}) ->
 	if K  < NodeK ->
  		{node, {NodeK, NodeV, remove(K, Left), Right}}
	; K  >= NodeK ->
		{node, {NodeK, NodeV, Left, remove(K, Right)}}
	end.

%% @doc Replace a key in the tree
%%
-spec replace(integer(), antidote_crdt_bigset_shard : shard(), tree()) -> tree().
replace(_K, V, _Tree = {node ,{K, _V, ?EMPTY_NODE, ?EMPTY_NODE}}) ->
 	{node, {K, V, ?EMPTY_NODE, ?EMPTY_NODE}};
replace(K, V, _Tree = {node, {NodeK, NodeV, Left, Right}}) ->
  	if K < NodeK ->
      	{node, {NodeK, NodeV, replace(K, V, Left), Right}}
   	; K  >= NodeK ->
      	{node, {NodeK, NodeV, Left, replace(K, V, Right)}}
  	end.
