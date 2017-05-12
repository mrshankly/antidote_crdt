# Antidote CRDT library

CRDT implementations to use with Antidote.

# BigSets

The BigSet is inspired by the already existing OR-Set, only that it spreads its elements over multiple shards. This approach is different from Riak's BigSet, but it relies on the same principle: Divide the set in smaller parts, so it is not necessary to manipulate the whole thing when writing. 

Each element is hashed by using Erlang's phash2/2 with range 0-2^X. X can be set by the user upon creation of the Bigset by giving or is just set to 16 if no parameter is given. If more than Y (also set by the user or set to 30 if no parameter given) elements are added to a shard, it is split in two new shards, which both have exactly half the range of the old shard.

The shards are organized in a tree, as can be seen in antidote_crdt_bigset_shardtree, where the inner nodes are for navigation only (hash value of the element and key of the node are compared), and the leaves contain the current shards. When adding or removing an element, the tree is searched for the fitting shard. Removing enough elements from a shard can lead to that shard merging with its sibling, if that one is also a leaf. In that case, both shards are merged, the leaves are dropped and their parent is replaced with the merged shard.

The tree is local to each replica and can have a different structure on one replica than on another one. Imagine a situation where adding another element would result in a shard being splitted. Now there are a concurrent add and remove of an element in that shard. Those replicas who receive the remove first won't split, while others will.

# Development

Use the following `make` targets to build and test the CRDT library:


	# compile
	make compile
	# run unit tests:
	make test
	# check types:
	make dialyzer
	# check code style:
	make lint


## PropEr tests

To run the property based tests in the test directory install the [rebar3 PropEr plugin](https://www.rebar3.org/docs/using-available-plugins#proper) by adding the following line to `~/.config/rebar3/rebar.config`:

	{plugins, [rebar3_proper]}.

Then execute the tests with:

	make proper

For more control, you can run PropEr manually and specify parameters like the tested module or the number of generated tests:

	rebar3 proper -n 1000 -m prop_crdt_orset
