# BigSets

The BigSet offers the same semantics than the already existing OR-Set, but aims at higher scalability: We partition it in shards, which are stored in an ets table. The table keys of the different shards are stored in a B-Tree we call key tree. If we wish to add/remove an element, we traverse the tree with that element and search for the correct table key. The keys of the tree represent intervals, so we don't search for an exact match.

Beside splitting when a shard contains too many elements, they are merged with their neighbour when removing an element if both the neighbour and the current shard have enough free space.

As for the materializer's snapshots, these share the same ets table, so we must be careful not to delete table entries that are still needed and to remove those that are no longer used. In order to do so, we use a reference counting strategy.

The BigSet may have a different structure on two different replicas, while its content is the same. We can illustrate this by a simple example: There are two replicas of the same BigSet with one shard and maximum element count for that shard. Two operations add(e1) and remove(e2) are applied, where e2 is in that shard and e1 is not. If the first replica sees the add before the remove, it needs to split, and removing e2 is not sufficient to make it merge again. The other way around, removing e2 first leaves enough space to add e1, so both replicas end up having the same content, but one of them has split in two.
