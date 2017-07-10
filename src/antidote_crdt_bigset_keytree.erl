%% @author Luc Francois, francois.luc93@gmail.com

-module(antidote_crdt_bigset_keytree).
-export([init/1, insert_three/7, get_key/2, get_key_left/2, get_key_right/2, get_all/1, replace/4, remove/2]).
-define(EMPTY_NODE, empty).
-define(EMPTY_KEY, -1).
-define(EMPTY_VALUE, ok).
-define(MAX_KEYS, 3).
-define(MIN_KEYS, 1+ ?MAX_KEYS / 2).
-type tree() :: [{integer(), any(), tree()}]|?EMPTY_NODE.
-type key() :: {integer(), integer()}.

%% @doc Initialize the root of the tree
-spec init(any()) -> tree(). 
init(V) ->
	[{{min, max}, V, ?EMPTY_NODE}, {?EMPTY_KEY, ?EMPTY_VALUE, ?EMPTY_NODE}].

-spec insert_three(key(), key(), key(), any(), any(), any(), tree())->tree().
insert_three(K1, K2, K3, V1, V2, V3, Tree) ->
	NewNode = insert_keys(K1, K2, K3, V1, V2, V3, Tree, 1),
	case NewNode of
		{Node1, Node2, NewKey, NewValue} ->
			[{NewKey, NewValue, Node1}, {?EMPTY_KEY, ?EMPTY_VALUE, Node2}];
		_ ->
			NewNode
	end.

% shard was splitted, so search for the old shard and replace that key, so while 2 keys are added, one is also removed
-spec insert_keys(key(), key(), key(), any(), any(), any(), tree(), integer()) -> tree()|{tree(), tree(), {key(), any()}}.
insert_keys(K1, K2, K3, V1, V2, V3, [{?EMPTY_KEY, ?EMPTY_VALUE, Child}]=_Node, _Pos) ->
	% go into rightmost child
	NewChild = insert_keys(K1, K2, K3, V1, V2, V3, Child, 1),
	case NewChild of
		%% adding keys to the child resulted in splitting
		{Node1, Node2, NewKey, NewValue} ->
			[{NewKey, NewValue, Node1}, {?EMPTY_KEY, ?EMPTY_VALUE, Node2}];
		_ ->
			[{?EMPTY_KEY, ?EMPTY_VALUE, NewChild}]
	end;
insert_keys(K1, K2, K3, V1, V2, V3, [{{OldMin, OldMax} = OldKey, Value, Child}|Rest]=_Node, Pos) ->
	case K1 of 
		% we found the shard that was splitted and replace it by the new shards
		% also we are in a leaf, so we just add these two to the leaf
		% last condition makes sure to split only when in the leftmost key
		% this case matches only when inserting into the root
		{OldMin, _Max} when Child == ?EMPTY_NODE andalso Pos == 1 ->
			try_split([{K1, V1, ?EMPTY_NODE}, {K2, V2, ?EMPTY_NODE}, {K3, V3, ?EMPTY_NODE}] ++ Rest);
		{OldMin, _Max} when Child == ?EMPTY_NODE andalso Pos > 1 ->
			[{K1, V1, ?EMPTY_NODE}, {K2, V2, ?EMPTY_NODE}, {K3, V3, ?EMPTY_NODE}] ++ Rest;
		% we found the shard that was splitted and replace it by the two new shards
		% also we are not in a leaf, so send the smaller new shard to the node left to the key
		{OldMin, _Max} when Child /= ?EMPTY_NODE ->
			NewChild = insert_rest(K1, K2, V1, V2, Child),
			case NewChild of
				%% adding one key to the child resulted in splitting
				{Node1, Node2, NewKey, NewValue} ->
					try_split([{NewKey, NewValue, Node1}, {K3, V3, Node2}] ++ Rest);
				_ ->
					try_split([{K3, V3, NewChild}] ++ Rest)
			end;			
		% go into left child if smaller. Atom min denotes a value smaller than all other values, thus the additional condition, similar for Atom max
		% there is a child, because otherwise Max2 could not be inferior to OldMin
		{Min, _Max} when (Min < OldMin andalso OldMin /= min) orelse Min == min  ->
			NewChild = insert_keys(K1, K2, K3, V1, V2, V3, Child, 1),
			case NewChild of
				{Node1, Node2, NewKey, NewValue} ->
					try_split([{NewKey, NewValue, Node1}, {OldKey, Value, Node2}] ++ Rest);
				_ ->
					try_split([{OldKey, Value, NewChild}] ++ Rest)
			end;
		% larger than the current key, go one key to the right
		{Min, _Max} when (OldMax =< Min orelse OldMin == min) andalso Child == ?EMPTY_NODE ->
			case Pos of
				1 ->
					try_split([{OldKey, Value, Child}] ++ insert_keys(K1, K2, K3, V1, V2, V3, Rest, Pos + 1));
				_ ->
					[{OldKey, Value, Child}] ++ insert_keys(K1, K2, K3, V1, V2, V3, Rest, Pos + 1)
			end;			
		{Min, _Max} when (OldMax =< Min orelse OldMin == min) andalso Child /= ?EMPTY_NODE ->
			try_split([{OldKey, Value, Child}] ++ insert_keys(K1, K2, K3, V1, V2, V3, Rest, Pos + 1)) 
	end.

-spec try_split(tree())-> tree()|{tree(), tree(), key(), any()}.
try_split(Node)->
	case length(Node) of
		Length when Length > ?MAX_KEYS + 1 ->
			% split
			Half = Length div 2,
			{Key, Value, Temp} = lists:nth(Half + 1, Node),
			Node1 = lists:sublist(Node, Half)++[{?EMPTY_KEY, ?EMPTY_VALUE, Temp}],
			Node2 = lists:sublist(Node, Half + 2, Half),
			{Node1, Node2, Key, Value};
		Length when Length =< ?MAX_KEYS + 1 ->
			Node
	end.

-spec insert_rest(key(), key(), any(), any(), tree()) -> tree()|{tree(), tree(), {key(), any()}}.
insert_rest(K1, K2, V1, V2, {?EMPTY_KEY, ?EMPTY_VALUE, ?EMPTY_NODE}) ->
	[{K1, V1, ?EMPTY_NODE}, {K2, V2, ?EMPTY_NODE}, {?EMPTY_KEY, ?EMPTY_VALUE, ?EMPTY_NODE}];
insert_rest(K1, K2, V1, V2, {?EMPTY_KEY, ?EMPTY_VALUE, Child}) ->
	% go into rightmost child
	NewChild = insert_rest(K1, K2, V1, V2, Child),
	case NewChild of
		%% adding keys to the child resulted in splitting
		{Node1, Node2, NewKey, NewValue} ->
			[{NewKey, NewValue, Node1},{?EMPTY_KEY, ?EMPTY_VALUE, Node2}];
		_ ->
			[{?EMPTY_KEY, ?EMPTY_VALUE, NewChild}]
	end;
insert_rest(K1, K2, V1, V2, Node) ->
	Last = lists:last(Node),
	New = lists:droplast(Node),
	try_split(New ++ insert_rest(K1, K2, V1, V2, Last)).

-spec get_all(tree()) -> [{key(), any()}].
get_all(?EMPTY_NODE) ->
	[];
get_all([{?EMPTY_KEY, ?EMPTY_VALUE, Child}]) ->
	get_all(Child);
get_all([{Key, NodeV, Child}|Rest]) ->
	get_all(Child) ++ [{Key, NodeV}] ++ get_all(Rest).
			
%% @doc Find the right shard for a given key
%% Shards are stored in leaves, so we go down the tree until we end up in a leaf
%%
-spec get_key(integer(), tree()) -> {key(), any()}.
get_key(Elem, [{?EMPTY_KEY, ?EMPTY_VALUE, Child}])->
	get_key(Elem, Child);
get_key(Elem, [{{Min, Max}, NodeV, Child}|Rest] = _Node)->
	if 
		Elem < Min andalso Min /= min ->
			get_key(Elem, Child);
		% Max is in the next shard
		Elem >= Max andalso Max /= max->
			get_key(Elem, Rest);
		true ->
			{{Min, Max}, NodeV}
	end.

-spec get_key_left(integer(), tree()) -> {key(), any()}.
get_key_left(Elem, [{?EMPTY_KEY, ?EMPTY_VALUE, Child}])->
	case get_key_left(Elem, Child) of
		?EMPTY_VALUE ->
			left;
		Return ->
			Return
	end;
get_key_left(Elem, [{{Min, Max}, NodeV, Child}|Rest] = _Node)->
	if 
		(Elem < Min orelse Elem == min) andalso Min /= min ->
			case get_key_left(Elem, Child) of
				?EMPTY_VALUE ->
					left;
				Return ->
					Return
			end;
		(Elem >= Max andalso Max /= max andalso Elem /= min) orelse (Min == min andalso Elem /= min) ->
			case get_key_left(Elem, Rest) of
				left ->
					{{Min, Max}, NodeV};
				?EMPTY_VALUE ->
					{{Min, Max}, NodeV};
				Return ->
					Return
			end;
		true ->
			case Child of 
				% last call is the searched one
				?EMPTY_NODE ->
					?EMPTY_VALUE;
				[_V | _Rest] ->
					get_left(Child)
			end			 
	end.

%% @doc Find the right shard for a given key
%% Shards are stored in leaves, so we go down the tree until we end up in a leaf
%%
-spec get_key_right(integer(), tree()) -> {key(), any()}.
get_key_right(Elem, [{?EMPTY_KEY, ?EMPTY_VALUE, Child}])->
	get_key_right(Elem, Child);
get_key_right(Elem, [{{Min, Max}, NodeV, Child}|Rest] = _Node)->
	if 
		(Elem < Min orelse Elem == min) andalso Min /= min ->
			case get_key_right(Elem, Child) of
				parent ->
					{{Min, Max}, NodeV};
				Result ->
					Result
			end;
		% Max is in the next shard
		(Elem >= Max andalso Max /= max andalso Elem /= min) orelse (Min == min andalso Elem /= min) ->
			get_key_right(Elem, Rest);
		true ->
			case Child of 
				?EMPTY_NODE ->
					[{Key, Value, _}|_] = Rest,
					case Key of 
						?EMPTY_KEY ->
							parent;
						_Value ->
							{Key, Value}
					end;
				[_V | _Rest] ->
					[{_, _, Next_Child}|_] = Rest,
					get_right(Next_Child)
			end
	end.

%% @doc Replace a key and value in the tree
%%
-spec replace(key(), key(), any(), tree()) -> tree().
replace(K, NewKey, NewV, [{?EMPTY_KEY, ?EMPTY_VALUE, Child}]) ->
	[{?EMPTY_KEY, ?EMPTY_VALUE, replace(K, NewKey, NewV, Child)}];
replace({KeyMin, KeyMax}= K, NewKey, NewV, [{{OldMin, OldMax}, NodeV, Child}|Rest]=_Node) ->
	if 
		KeyMin == OldMin andalso KeyMax == OldMax ->
			[{NewKey, NewV, Child}|Rest];
		(KeyMin < OldMin andalso OldMin /= min) orelse KeyMin == min ->
			[{{OldMin, OldMax}, NodeV, replace(K, NewKey, NewV, Child)}|Rest];
		true ->
			[{{OldMin, OldMax}, NodeV, Child}] ++ replace(K, NewKey, NewV, Rest)
	end.

-spec remove(key(), tree()) -> tree().
remove(K, Tree) ->
	Rem = remove(K, Tree, 1),
	case Rem of
		{rotate, [{?EMPTY_KEY, ?EMPTY_VALUE, Rem_Rest}]} -> 
			Rem_Rest;
		{rotate, Rem_Rest} -> 
			Rem_Rest;
		Rem_Rest ->
			Rem_Rest
	end.
-spec remove(key(), tree(), integer()) -> tree().
remove(K, [{{OldMin, OldMax}, V, Child}, {Next_K, Next_V, Next_Child} = Next|Rest]=Node, Pos) ->
	case K of 
		{OldMin, OldMax} when Child == ?EMPTY_NODE ->
			case  length(Node) + Pos - 1 of
				Key_Count when Key_Count > ?MIN_KEYS ->
					[Next|Rest];
				Key_Count when Key_Count =< ?MIN_KEYS ->
					%% rotate or merge
					{rotate, [Next|Rest]}
			end;
		{OldMin, OldMax} when Child /= ?EMPTY_NODE ->
			%% first get the next key to the current position, then delete it in leaf
			{Succ_In_Child_K, Succ_In_Child_V} = get_left(Child),
			Rem = remove(Succ_In_Child_K, Child, 1),
			case Rem of 
				{rotate, Rem_Rest} ->
					case try_rotate(Rem_Rest, Next_Child, Succ_In_Child_K, Succ_In_Child_V) of
						merge ->
							case length(Node) + Pos - 1 of
								Key_Count when Key_Count > ?MIN_KEYS ->
									[{Next_K, Next_V, merge(Rem_Rest, Next_Child, Succ_In_Child_K, Succ_In_Child_V)}|Rest];
								Key_Count when Key_Count =< ?MIN_KEYS ->
									%% rotate or merge
									{rotate, [{Next_K, Next_V, merge(Rem_Rest, Next_Child, Succ_In_Child_K, Succ_In_Child_V)}|Rest]}
							end;
						{ChildA, ChildB, New_K, New_V} ->
							[{New_K, New_V, ChildA}, {Next_K, Next_V, ChildB}] ++ Rest
					end;
				Rem_Rest ->
					[{Succ_In_Child_K, Succ_In_Child_V, Rem_Rest}, Next] ++ Rest
			end;
		{KeyMin, _KeyMax} when (KeyMin =< OldMin andalso OldMin /= min) orelse KeyMin == min ->
			Rem = remove(K, Child, 1),
			case Rem of 
				{rotate, Rem_Rest} ->
					case try_rotate(Rem_Rest, Next_Child, {OldMin, OldMax}, V) of
						merge ->
							case  length(Node) + Pos - 1 of
								Key_Count when Key_Count > ?MIN_KEYS ->
									[{Next_K, Next_V, merge(Rem_Rest, Next_Child, {OldMin, OldMax}, V)}|Rest];
								Key_Count when Key_Count =< ?MIN_KEYS ->
									%% rotate or merge
									{rotate, [{Next_K, Next_V, merge(Rem_Rest, Next_Child, {OldMin, OldMax}, V)}|Rest]}
							end;
						{ChildA, ChildB, New_K, New_V} ->
							[{New_K, New_V, ChildA}, {Next_K, Next_V, ChildB}] ++ Rest
					end;
				Rem_Rest ->
					[{{OldMin, OldMax}, V, Rem_Rest}, Next] ++ Rest
			end;
		{_KeyMin, KeyMax} when KeyMax > OldMax orelse KeyMax == max ->
			case Next of
				{?EMPTY_KEY, ?EMPTY_VALUE, Next_Child} ->
					Rem = remove(K, Next_Child, 1),
					case Rem of 
						{rotate, Rem_Rest} ->
							%% rotate the other way because there is no right neighbour
							case try_rotate2(Child, Rem_Rest, {OldMin, OldMax}, V) of
								merge ->
									case length(Node) + Pos - 1 of
										Key_Count when Key_Count > ?MIN_KEYS ->
											[{?EMPTY_KEY, ?EMPTY_VALUE, merge(Child, Rem_Rest, {OldMin, OldMax}, V)}];
										Key_Count when Key_Count =< ?MIN_KEYS ->
											%% rotate or merge
											{rotate, [{?EMPTY_KEY, ?EMPTY_VALUE, merge(Child, Rem_Rest, {OldMin, OldMax}, V)}]}
									end;	
								{ChildA, ChildB, New_K, New_V} ->
									[{New_K, New_V, ChildA}, {?EMPTY_KEY, ?EMPTY_VALUE, ChildB}]
							end;
						Rem_Rest ->
							[{{OldMin, OldMax}, V, Child}, {?EMPTY_KEY, ?EMPTY_VALUE, Rem_Rest}]
					end;
				_ ->
					Rem = remove(K, [Next|Rest], Pos + 1),
					case Rem of 
						%% hand over the rotate information to the left
						{rotate, Rem_Rest} ->
							{rotate, [{{OldMin, OldMax}, V, Child}] ++ Rem_Rest};
						Rem_Rest ->
							[{{OldMin, OldMax}, V, Child}] ++ Rem_Rest
					end
			end
	end.

-spec merge(tree(), tree(), key(), any()) -> tree().
merge(ChildA, ChildB, K2, V2) ->
	{?EMPTY_KEY, ?EMPTY_VALUE, Child} = lists:last(ChildA),
	lists:droplast(ChildA) ++ [{K2, V2, Child}] ++ ChildB.

-spec try_rotate2(tree(), tree(), key(), any()) -> {tree(), tree(), key(), any()}|atom().
try_rotate2(ChildA, ChildB, K2, V2) ->
	case length(ChildA) of
		Length when Length < ?MIN_KEYS + 0.5 ->
			merge;
		Length when Length >= ?MIN_KEYS + 0.5 ->
			{K, V, Node} = lists:nth(Length-1, ChildA),
			{?EMPTY_KEY, ?EMPTY_VALUE, Node2} = lists:last(ChildA),
			NewA = lists:droplast(lists:droplast(ChildA)),
			{NewA ++ [{?EMPTY_KEY, ?EMPTY_VALUE, Node}], [{K2, V2, Node2}] ++ ChildB, K, V}
	end.

-spec try_rotate(tree(), tree(), key(), any()) -> {tree(), tree(), key(), any()}|atom().
try_rotate(ChildA, [{K, V, Node}|Rest]=ChildB, K2, V2) ->
	case length(ChildB) of 
		Length when Length < ?MIN_KEYS + 0.5 ->
			merge;
		Length when Length >= ?MIN_KEYS + 0.5 ->
			{?EMPTY_KEY, ?EMPTY_VALUE, Child} = lists:last(ChildA),
			NewA = lists:droplast(ChildA),
			{NewA ++ [{K2, V2, Child}] ++ [{?EMPTY_KEY, ?EMPTY_VALUE, Node}], Rest, K, V}
	end.

-spec get_left(tree()) -> {key(), any()}.
get_left([{_K, _V, ?EMPTY_NODE}|_Rest]= Node) ->
	Pos = length(Node),
	{K, V, ?EMPTY_NODE} = lists:nth(Pos-1, Node),
	{K, V};
get_left(Node) ->
	{_K, _V, Right} = lists:last(Node),
	get_left(Right).

-spec get_right(tree()) -> {key(), any()}.
get_right([{K, V, ?EMPTY_NODE}|_]) ->
	{K, V};
get_right([{_K, _V, Head}|_]) ->
	get_right(Head).