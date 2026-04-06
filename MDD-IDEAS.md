# MDD Optimization Ideas

Ideas for pushing gen_mdd to higher k values. The bottleneck is memory:
the memoization HashMap and node storage grow exponentially with k.

## Current baselines (2026-04-06)

| k | Build time | 16-way nodes | Total time |
|---|-----------|-------------|------------|
| 7 | ~4s | 168K (10 MB) | 4.7s |
| 8 | ~40s | 1.6M (100 MB) | 46.6s |
| 9 | >2min | >2.8M (timeout) | OOM/timeout |

Scaling: ~10x per k step in both time and memory.

## Untested Ideas

### 1. Pack sums into u64/u128 instead of Vec<i8>
**Status**: Untested
The memo StateKey is `(Vec<i8>, u64)`. Every memo check clones a heap-allocated Vec.
For k <= 8, pack 8 x i8 into one u64. For k <= 16, use u128. Eliminates all heap
allocation in the hot path.

### 2. Switch gen_mdd to use ZW-first builder
**Status**: Untested
The current gen_mdd uses the 16-way interleaved builder (mdd.rs) then reorders.
The ZW-first builder (mdd_zw_first.rs) builds directly as 4-way, which should
have dramatically smaller memo tables (4^L states vs 16^L).

### 3. Tighter interval pruning at every level
**Status**: Untested
Currently, lag constraints are only checked at "completion" levels. But we can
compute range bounds on partial sums at every level and prune branches whose
partial sums are already out of achievable range.

### 4. Disk-backed memo with redb or sled
**Status**: Untested
Move the memo HashMap to disk using an embedded key-value store (redb, sled,
or rocksdb). Trades speed for virtually unlimited memory.

### 5. Level-by-level BFS construction
**Status**: Untested
Instead of DFS (which keeps all levels in memory), process one level at a time.
Enumerate all reachable states at level L, write to disk, then process level L+1.
Only two levels need to be in memory at once.

### 6. Compress memo keys further
**Status**: Untested
The packed_active u64 uses 4 bits per position (16-way) or 2 bits (4-way).
For the ZW-first builder, pack more tightly. Also consider hashing the full
state to a u128 and using that as the key (with collision detection).

### 7. Clear completed level memos during DFS
**Status**: Untested
After all branches at level 0 complete, memo[0] is never needed again.
Similarly for subsequent levels. Track which levels are "closed" and free
their memo entries. Won't help peak usage but reduces sustained memory.

### 8. Memory-mapped node storage
**Status**: Untested
Use mmap'd files for the nodes Vec instead of heap allocation. The OS
manages paging to/from disk transparently.

### 9. Parallel construction with rayon
**Status**: Untested
The 16 (or 4) branches at each level are independent. Use rayon to process
them in parallel with thread-local memo tables, then merge.

### 10. Better variable ordering
**Status**: Untested
The bouncing order (0, 2k-1, 1, 2k-2, ...) may not minimize state space.
Try different orderings: linear, reverse, or dynamically chosen based on
constraint density.

### 11. Partial-lag range pruning
**Status**: Untested
Before a lag is fully complete, we know partial contributions. If the partial
sum is already outside [-remaining_max, +remaining_max], prune immediately.
This is more aggressive than checking only at completion.

### 12. Port MDD to bex
**Status**: Untested
The bex library has multi-threaded swarm reordering. Port MDD node types to
bex and use its infrastructure for the reorder phase. Won't help construction
but could dramatically speed up reordering at large k.

## Rejected Ideas

(none yet)
