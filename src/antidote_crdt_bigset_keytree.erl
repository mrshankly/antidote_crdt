%% @author Luc Francois, francois.luc93@gmail.com

-module(antidote_crdt_bigset_keytree).
-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl"). 
%-include_lib("C:/Users/Luehk/workspace/Bigset/include/eunit/include/eunit.hrl"). 
-endif. 
-export([init/2, insert_three/7, get_key/2, get_key_left/2, get_key_right/2, get_all/1, replace/4, remove/2]).
-define(EMPTY_NODE, {'empty'}).
-type tree() :: {integer(), treenode()}.
-type treenode() :: [{integer(), any(), treenode()}]|?EMPTY_NODE.
-type key() :: {integer(), integer()}.

%% @doc Initialize the root of the tree
-spec init(integer(), any()) -> tree(). 
init(T, V) ->
	{T, [{{min, max}, V, ?EMPTY_NODE}, {-1, ok, ?EMPTY_NODE}]}.

-spec insert_three(key(), key(), key(), any(), any(), any(), tree())->tree().
insert_three(K1, K2, K3, V1, V2, V3, {Max_Keys, Root}=_Tree) ->
	NewNode = insert_keys(K1, K2, K3, V1, V2, V3, Root, Max_Keys),
	case NewNode of
		{Node1, Node2, NewKey, NewValue} ->
			New = [{NewKey, NewValue, Node1}, {-1, ok, Node2}];
		_ ->
			New = NewNode
	end,
	{Max_Keys, New}.

% shard was splitted, so search for the old shard and replace that key, so while 2 keys are added, one is also removed
-spec insert_keys(key(), key(), key(), any(), any(), any(), treenode(), integer()) -> treenode()|{treenode(), treenode(), {key(), any()}}.
insert_keys(K1, K2, K3, V1, V2, V3, [{-1, ok, Child}]=_Node, Max_Keys) ->
	% go into rightmost child
	NewChild = insert_keys(K1, K2, K3, V1, V2, V3, Child, Max_Keys),
	case NewChild of
		%% adding keys to the child resulted in splitting
		{Node1, Node2, NewKey, NewValue} ->
			[{NewKey, NewValue, Node1}, {-1, ok, Node2}];
		_ ->
			[{-1, ok, NewChild}]
	end;
insert_keys({Min, _} = K1, K2, {_, Max} = K3, V1, V2, V3, [{{OldMin, OldMax} = OldKey, Value, Child}|Rest]=_Node, Max_Keys) ->
	if 
		% we found the shard that was splitted and replace it by the two new shards
		% also we are in a leaf, so we just add these two to the leaf
		% last condition makes sure to split only when in the leftmost key
		% this case matches only when inserting into the root
		Min == OldMin andalso Child == ?EMPTY_NODE andalso Min == min ->
			try_split([{K1, V1, ?EMPTY_NODE}, {K2, V2, ?EMPTY_NODE}, {K3, V3, ?EMPTY_NODE}] ++ Rest, Max_Keys);
		Min == OldMin andalso Child == ?EMPTY_NODE ->
			[{K1, V1, ?EMPTY_NODE}, {K2, V2, ?EMPTY_NODE}, {K3, V3, ?EMPTY_NODE}] ++ Rest;
		% we found the shard that was splitted and replace it by the two new shards
		% also we are not in a leaf, so send the smaller new shard to the node left to the key
		Min == OldMin andalso Child /= ?EMPTY_NODE ->
			NewChild = insert_rest(K1, K2, V1, V2, Child, Max_Keys),
			case NewChild of
				%% adding one key to the child resulted in splitting
				{Node1, Node2, NewKey, NewValue} ->
					try_split([{NewKey, NewValue, Node1}, {K3, V3, Node2}] ++ Rest, Max_Keys);
				_ ->
					try_split([{K3, V3, NewChild}] ++ Rest, Max_Keys)
			end;			
		% go into left child if smaller. Atom min denotes a value smaller than all other values, thus the additional condition, similar for Atom max
		% there is a child, because otherwise Max2 could not be inferior to OldMin
		Min < OldMin orelse Min == min ->
			NewChild = insert_keys(K1, K2, K3, V1, V2, V3, Child, Max_Keys),
			case NewChild of
				{Node1, Node2, NewKey, NewValue} ->
					try_split([{NewKey, NewValue, Node1}, {OldKey, Value, Node2}] ++ Rest, Max_Keys);
				_ ->
					try_split([{OldKey, Value, NewChild}] ++ Rest, Max_Keys)
			end;
		% larger than the current key, go one key to the right
		(OldMax =< Min andalso Child == ?EMPTY_NODE) orelse Max == max ->
			if 
				Min == min ->
					try_split([{OldKey, Value, Child}] ++ insert_keys(K1, K2, K3, V1, V2, V3, Rest, Max_Keys), Max_Keys);
				true ->
					[{OldKey, Value, Child}] ++ insert_keys(K1, K2, K3, V1, V2, V3, Rest, Max_Keys)
			end;			
		OldMax =< Min orelse Max == max ->
			try_split([{OldKey, Value, Child}] ++ insert_keys(K1, K2, K3, V1, V2, V3, Rest, Max_Keys), Max_Keys) 
	end.

-spec try_split(treenode(), integer())-> treenode()|{treenode(), treenode(), key(), any()}.
try_split(Node, Max_Keys)->
	Length = length(Node),
	if 
		Length > Max_Keys + 1 ->
			% split
			Half = Length div 2,
			{Key, Value, Temp} = lists:nth(Half + 1, Node),
			Node1 = lists:sublist(Node, Half)++[{-1, ok, Temp}],
			Node2 = lists:sublist(Node, Half + 2, Half),
			{Node1, Node2, Key, Value};
		true ->
			Node
	end.

-spec insert_rest(key(), key(), any(), any(), treenode(), integer()) -> treenode()|{treenode(), treenode(), {key(), any()}}.
insert_rest(K1, K2, V1, V2, {-1, ok, ?EMPTY_NODE}, _Max_Keys) ->
	[{K1, V1, ?EMPTY_NODE}, {K2, V2, ?EMPTY_NODE}, {-1, ok, ?EMPTY_NODE}];
insert_rest(K1, K2, V1, V2, {-1, ok, Child}, Max_Keys) ->
	% go into rightmost child
	NewChild = insert_rest(K1, K2, V1, V2, Child, Max_Keys),
	case NewChild of
		%% adding keys to the child resulted in splitting
		{Node1, Node2, NewKey, NewValue} ->
			[{NewKey, NewValue, Node1},{-1, ok, Node2}];
		_ ->
			[{-1, ok, NewChild}]
	end;
insert_rest(K1, K2, V1, V2, Node, Max_Keys) ->
	Last = lists:last(Node),
	New = lists:droplast(Node),
	try_split(New ++ insert_rest(K1, K2, V1, V2, Last, Max_Keys), Max_Keys).

-spec get_all(tree()) -> [{key(), any()}].
get_all({_Max_Keys, Root}=_Tree) ->
	get_all_helper(Root).
-spec get_all_helper(treenode()) -> [{key(), any()}].
get_all_helper(?EMPTY_NODE) ->
	[];
get_all_helper([{-1, ok, Child}]) ->
	get_all_helper(Child);
get_all_helper([{Key, NodeV, Child}|Rest]) ->
	get_all_helper(Child) ++ [{Key, NodeV}] ++ get_all_helper(Rest).
			
%% @doc Find the right shard for a given key
%% Shards are stored in leaves, so we go down the tree until we end up in a leaf
%%
-spec get_key(integer(), tree()) -> {key(), any()}.
get_key(Elem, {_Max_Keys, Root} = _Tree)->
		get_key_helper(Elem, Root).
-spec get_key_helper(integer(), treenode()) -> {key(), any()}.
get_key_helper(Elem, [{-1, ok, Child}])->
	get_key_helper(Elem, Child);
get_key_helper(Elem, [{{Min, Max}, NodeV, Child}|Rest] = _Node)->
	if 
		Elem < Min andalso Min /= min ->
			get_key_helper(Elem, Child);
		% Max is in the next shard
		Elem >= Max andalso Max /= max->
			get_key_helper(Elem, Rest);
		true ->
			{{Min, Max}, NodeV}
	end.

-spec get_key_left(integer(), tree()) -> {key(), any()}.
get_key_left(Elem, {_Max_Keys, Root} = _Tree)->
	get_key_left_helper(Elem, Root).
-spec get_key_left_helper(integer(), treenode()) -> {key(), any()}.
get_key_left_helper(Elem, [{-1, ok, Child}])->
	case get_key_left_helper(Elem, Child) of
		ok ->
			left;
		Return ->
			Return
	end;
get_key_left_helper(Elem, [{{Min, Max}, NodeV, Child}|Rest] = _Node)->
	if 
		Elem < Min andalso Min /= min ->
			case get_key_left_helper(Elem, Child) of
				ok ->
					left;
				Return ->
					Return
			end;
		Elem >= Max andalso Max /= max->
			case get_key_left_helper(Elem, Rest) of
				left ->
					{{Min, Max}, NodeV};
				ok ->
					{{Min, Max}, NodeV};
				Return ->
					Return
			end;
		true ->
			if 
				% last call is the searched one
				Child == ?EMPTY_NODE ->
					ok;
				true ->
					get_left(Child)
			end			 
	end.

%% @doc Find the right shard for a given key
%% Shards are stored in leaves, so we go down the tree until we end up in a leaf
%%
-spec get_key_right(integer(), tree()) -> {key(), any()}.
get_key_right(Elem, {_Max_Keys, Root} = _Tree)->
		get_key_right_helper(Elem, Root).
-spec get_key_right_helper(integer(), treenode()) -> {key(), any()}.
get_key_right_helper(Elem, [{-1, ok, Child}])->
	get_key_right_helper(Elem, Child);
get_key_right_helper(Elem, [{{Min, Max}, NodeV, Child}|Rest] = _Node)->
	if 
		Elem < Min andalso Min /= min ->
			case get_key_right_helper(Elem, Child) of
				parent ->
					{{Min, Max}, NodeV};
				Result ->
					Result
			end;
		% Max is in the next shard
		Elem >= Max andalso Max /= max->
			get_key_right_helper(Elem, Rest);
		true ->
			if 
				Child == ?EMPTY_NODE ->
					[{Key, Value, _}|_] = Rest,
					if 
						Key == -1 ->
							parent;
						true ->
							{Key, Value}
					end;
				true ->
					[{_, _, Next_Child}|_] = Rest,
					get_right(Next_Child)
			end
	end.

%% @doc Replace a key and value in the tree
%%
-spec replace(key(), key(), any(), tree()) -> tree().
replace(K, NewKey, NewV, {Max_Keys, Root} = _Tree) ->
	{Max_Keys, replace_helper(K, NewKey, NewV, Root)}.
-spec replace_helper(key(), key(), any(), any()) -> tree().
replace_helper(K, NewKey, NewV, [{-1, ok, Child}]) ->
	[{-1, ok, replace_helper(K, NewKey, NewV, Child)}];
replace_helper({KeyMin, KeyMax}= K, NewKey, NewV, [{{OldMin, OldMax}, NodeV, Child}|Rest]=_Node) ->
	if 
		KeyMin == OldMin andalso KeyMax == OldMax ->
			[{NewKey, NewV, Child}|Rest];
		(KeyMin < OldMin andalso OldMin /= min) orelse KeyMin == min ->
			[{{OldMin, OldMax}, NodeV, replace_helper(K, NewKey, NewV, Child)}|Rest];
		true ->
			[{{OldMin, OldMax}, NodeV, Child}] ++ replace_helper(K, NewKey, NewV, Rest)
	end.

-spec remove(key(), tree()) -> tree().
remove(K, {Max_Keys, Root} = _Tree) ->
	Rem = remove(K, Root, 1 + Max_Keys / 2, 1),
	case Rem of
		{rotate, [{-1, ok, Rem_Rest}]} -> 
			{Max_Keys, Rem_Rest};
		{rotate, Rem_Rest} -> 
			{Max_Keys, Rem_Rest};
		Rem_Rest ->
			{Max_Keys, Rem_Rest}
	end.
-spec remove(key(), treenode(), integer(), integer()) -> tree().
remove({KeyMin, KeyMax} = K, [{{OldMin, OldMax}, V, Child}, {Next_K, Next_V, Next_Child} = Next|Rest]=Node, Min_Keys, Pos) ->
	if 
		K == {OldMin, OldMax} andalso Child == ?EMPTY_NODE ->
			Key_Count = length(Node) + Pos - 1,
			if 
				Key_Count > Min_Keys ->
					[Next|Rest];
				true ->
					%% rotate or merge
					{rotate, [Next|Rest]}
			end;
		K == {OldMin, OldMax} andalso Child /= ?EMPTY_NODE ->
			%% first get the next key to the current position, then delete it in leaf
			{Succ_In_Child_K, Succ_In_Child_V} = get_left(Child),
			Rem = remove(Succ_In_Child_K, Child, Min_Keys, 1),
			case Rem of 
				{rotate, Rem_Rest} ->
					case try_rotate(Rem_Rest, Next_Child, Succ_In_Child_K, Succ_In_Child_V, Min_Keys) of
						merge ->
							Key_Count = length(Node) + Pos - 1,
							if 
								Key_Count > Min_Keys ->
									[{Next_K, Next_V, merge(Rem_Rest, Next_Child, Succ_In_Child_K, Succ_In_Child_V)}|Rest];
								true ->
									%% rotate or merge
									{rotate, [{Next_K, Next_V, merge(Rem_Rest, Next_Child, Succ_In_Child_K, Succ_In_Child_V)}|Rest]}
							end;
						{ChildA, ChildB, New_K, New_V} ->
							[{New_K, New_V, ChildA}, {Next_K, Next_V, ChildB}] ++ Rest
					end;
				Rem_Rest ->
					[{Succ_In_Child_K, Succ_In_Child_V, Rem_Rest}, Next] ++ Rest
			end;
		(KeyMin =< OldMin andalso OldMin /= min) orelse KeyMin == min ->
			Rem = remove(K, Child, Min_Keys, 1),
			case Rem of 
				{rotate, Rem_Rest} ->
					case try_rotate(Rem_Rest, Next_Child, {OldMin, OldMax}, V, Min_Keys) of
						merge ->
							Key_Count = length(Node) + Pos - 1,
							if 
								Key_Count > Min_Keys ->
									[{Next_K, Next_V, merge(Rem_Rest, Next_Child, {OldMin, OldMax}, V)}|Rest];
								true ->
									%% rotate or merge
									{rotate, [{Next_K, Next_V, merge(Rem_Rest, Next_Child, {OldMin, OldMax}, V)}|Rest]}
							end;
						{ChildA, ChildB, New_K, New_V} ->
							[{New_K, New_V, ChildA}, {Next_K, Next_V, ChildB}] ++ Rest
					end;
				Rem_Rest ->
					[{{OldMin, OldMax}, V, Rem_Rest}, Next] ++ Rest
			end;
		KeyMax >= OldMax orelse KeyMax == max ->
			case Next of
				{-1, ok, Next_Child} ->
					Rem = remove(K, Next_Child, Min_Keys, 1),
					case Rem of 
						{rotate, Rem_Rest} ->
							%% rotate the other way because there is no right neighbour
							case try_rotate2(Child, Rem_Rest, {OldMin, OldMax}, V, Min_Keys) of
								merge ->
									Key_Count = length(Node) + Pos - 1,
									if 
										Key_Count > Min_Keys ->
											[{-1, ok, merge(Child, Rem_Rest, {OldMin, OldMax}, V)}];
										true ->
											%% rotate or merge
											{rotate, [{-1, ok, merge(Child, Rem_Rest, {OldMin, OldMax}, V)}]}
									end;	
								{ChildA, ChildB, New_K, New_V} ->
									[{New_K, New_V, ChildA}, {-1, ok, ChildB}]
							end;
						Rem_Rest ->
							[{{OldMin, OldMax}, V, Child}, {-1, ok, Rem_Rest}]
					end;
				_ ->
					Rem = remove(K, [Next|Rest], Min_Keys, Pos + 1),
					case Rem of 
						%% hand over the rotate information to the left
						{rotate, Rem_Rest} ->
							{rotate, [{{OldMin, OldMax}, V, Child}] ++ Rem_Rest};
						Rem_Rest ->
							[{{OldMin, OldMax}, V, Child}] ++ Rem_Rest
					end
			end
	end.

-spec merge(treenode(), treenode(), key(), any()) -> treenode().
merge(ChildA, ChildB, K2, V2) ->
	{-1, ok, Child} = lists:last(ChildA),
	lists:droplast(ChildA) ++ [{K2, V2, Child}] ++ ChildB.

-spec try_rotate2(treenode(), treenode(), key(), any(), integer()) -> {treenode(), treenode(), key(), any()}|atom().
try_rotate2(ChildA, ChildB, K2, V2, Min_Keys) ->
	Length = length(ChildA),
	if 
		Length < Min_Keys + 0.5 ->
			merge;
		true ->
			{K, V, Node} = lists:nth(Length-1, ChildA),
			{-1, ok, Node2} = lists:last(ChildA),
			NewA = lists:droplast(lists:droplast(ChildA)),
			{NewA ++ [{-1, ok, Node}], [{K2, V2, Node2}] ++ ChildB, K, V}
	end.

-spec try_rotate(treenode(), treenode(), key(), any(), integer()) -> {treenode(), treenode(), key(), any()}|atom().
try_rotate(ChildA, [{K, V, Node}|Rest]=ChildB, K2, V2, Min_Keys) ->
	Length = length(ChildB),
	if 
		Length < Min_Keys + 0.5 ->
			merge;
		true ->
			{-1, ok, Child} = lists:last(ChildA),
			NewA = lists:droplast(ChildA),
			{NewA ++ [{K2, V2, Child}] ++ [{-1, ok, Node}], Rest, K, V}
	end.

-spec get_left(treenode()) -> {key(), any()}.
get_left([{_K, _V, ?EMPTY_NODE}|_Rest]= Node) ->
	Pos = length(Node),
	{K, V, ?EMPTY_NODE} = lists:nth(Pos-1, Node),
	{K, V};
get_left(Node) ->
	{_K, _V, Right} = lists:last(Node),
	get_left(Right).

-spec get_right(treenode()) -> {key(), any()}.
get_right([{K, V, ?EMPTY_NODE}|_]) ->
	{K, V};
get_right([{_K, _V, Head}|_]) ->
	get_right(Head).

-ifdef(TEST).
remove_helper(Tree, []) ->
	Tree;
remove_helper(Tree, [K1|Rest]) ->
	remove_helper(remove(K1, Tree), Rest).

insert_helper(Tree, []) ->
	Tree;
insert_helper(Tree, [K1, K2, K3|Rest]) ->
	insert_helper(insert_three(K1, K2, K3, "haii", "haii", "haii", Tree), Rest).

add_test()->
	Tree = init(3, "haii"),
	List = [{min, 27}, {27,54}, {54,max},
			{min, 9}, {9,18}, {18,27},
			{min, 3}, {3,6}, {6,9},
			{min, 1}, {1,2}, {2,3},
			{3, 4}, {4,5}, {5,6},
			{6, 7}, {7,8}, {8,9},
			{9, 12}, {12,15}, {15,18},
			{9, 10}, {10,11}, {11,12},
			{12, 13}, {13,14}, {14,15},
			{15, 16}, {16,17}, {17,18}
		   ],
	List2 = [{27,54}, {54,max},
			{min, 1}, {1,2}, {2,3},
			{3, 4}, {4,5}, {5,6},
			{6, 7}, {7,8}, {8,9},
			{18,27},
			{9, 10}, {10,11}, {11,12},
			{12, 13}, {13,14}, {14,15},
			{15, 16}, {16,17}, {17,18}
			],
	Tree2 = insert_helper(Tree, List),
	Tree3 = remove_helper(Tree2, List2),
	Tree3 = {3, ?EMPTY_NODE}.
	
-endif.

