# MDD Optimization Ideas

Ideas for pushing gen_mdd to higher k values. The bottleneck is memory:
the memoization HashMap and node storage grow exponentially with k.

## Current state (2026-04-06)

| k | ZW-first time | Nodes | Memory |
|---|--------------|-------|--------|
| 7 | 0.3s | 69K | 1 MB |
| 8 | 7.3s | 433K | 6.6 MB |
| 9 | 1m17s | 2.6M | 40 MB |
| 10 | ~15min (est) | ~26M | ~400 MB |

Original baselines (before optimization):
k=7: 4.7s, k=8: 46.6s, k=9: OOM/timeout

## Implemented

### 1. Pack sums into u128 instead of Vec<i8>
**Status**: Implemented. ~3% speedup, eliminates heap allocs in hot path.

### 2. Switch gen_mdd to use ZW-first builder (default)
**Status**: Implemented. 4-way nodes (16 bytes) vs 16-way (64 bytes) = 4x less memory.
Per-call XY memo clearing prevents XY memo explosion.

### 3. Partial-lag range pruning (both builders)
**Status**: Implemented. **-40% build time.** Prunes branches where partial sums
exceed remaining event budget.

### 4. FxHashMap for all memo/unique tables
**Status**: Implemented. **-53% build time.** FxHash ~4x faster than SipHash for u128/u64 keys.

### 5. Hash-based unique table (u64 key)
**Status**: Implemented. Reduces unique table from ~80B/entry to ~20B/entry.

### 6. Periodic GC during reorder
**Status**: Implemented. 3x peak memory reduction during reorder phase.

## Untested Ideas

### 7. Disk-backed memo with redb
**Status**: redb dependency added; not yet implemented.
Move the zw_memo HashMap to disk using redb. For k=11, zw_memo needs ~50GB
in memory. On disk, it would be manageable. Trades speed for memory.

### 8. Level-by-level BFS construction
**Status**: Untested.
Instead of DFS (all levels in memory), process one level at a time.
States at level L generate states at level L+1. Only 2 levels in memory.
Enables streaming to disk.

### 9. Bounded/LRU memo cache
**Status**: Untested.
Cap memo at N entries (e.g., 100M = ~3GB). When full, evict old entries.
Trades re-computation for memory. Risk: thrashing if working set > cache.

### 10. Parallel XY sub-MDD construction
**Status**: Untested.
In ZW-first builder, each build_xy call for a different zw_sums is independent.
Use rayon/threads to process them in parallel. Could speed up XY phase ~4x.

### 11. Better variable ordering
**Status**: Untested.
The bouncing order (0, 2k-1, 1, 2k-2, ...) may not minimize state space.
Try different orderings: linear, reverse, or constraint-density ordered.

### 12. Memory-mapped node storage
**Status**: Untested.
Use mmap'd files for the nodes Vec. OS manages paging transparently.

### 13. Port MDD to bex
**Status**: bex cloned to /home/user/bex; basic MDD module created.
Bex has multi-threaded swarm reordering and concurrent data structures.
Most useful for: parallel XY construction, reorder phase (if we go back to it).

### 14. BFS-by-level construction
**Status**: Prototype implemented (ZW half only).
Two-pass approach: enumerate states top-down, build nodes bottom-up.
Peak memory = max states per level (not total). For k=8: peak 2.1M vs 6.4M total.
Needs: XY integration, disk spill for huge levels, parallelism per level.

### 15. Deeper parallelism (16+ subtrees)
**Status**: Implemented.
build_parallel_depth() supports arbitrary depth: depth=1 (4 subtrees),
depth=2 (16 subtrees for 16 cores), depth=3 (64 subtrees).
Awaiting benchmark on 16-core machine.

### 16. Arc consistency / constraint propagation
**Status**: Considered, deferred.
Precompute per-position domain restrictions before DFS/BFS.
Complex to implement correctly and may not add much beyond range pruning.
Forward checking during DFS would help but is hard to combine with memoization.

## New Ideas (2026-04-07 profiling round)

Profiling k=9 sequential: 93.8s total, 70.3s (75%) in XY builds.
5.3M XY sub-MDD builds, XY memo hit rate only 8% (cleared per ZW boundary).
ZW memo hit rate 65%. Goal: make k=15 feasible.

### 17. Full BFS-by-level construction (replace DFS)
**Status**: Untested.
Process one level at a time: expand all states at level L to get level L+1.
Natural dedup via HashMap key. Peak memory = max(states per level).
Two passes: enumerate states top-down, build nodes bottom-up.
Enables disk spill for huge levels. This is the path to k=15.

### 18. ZW-only BFS + batch XY builds
**Status**: Untested.
BFS the ZW half only (2k levels). Collect all distinct zw_sums at the
boundary. Then batch-build XY sub-MDDs, sharing node storage. Avoids
5.3M separate XY rebuilds — many zw_sums may share XY sub-MDD structure.

### 19. Tighter per-event pruning
**Status**: Untested.
Currently range pruning only fires at lag checkpoints. Add lightweight
range checks after every event: if any lag's partial sum is already
impossible given remaining budget, prune immediately. May cut 10-30% of
branches in the XY half where pruning is weakest.

### 20. Inline fixed-size state arrays
**Status**: Untested.
Replace Vec<i8> sums and Vec<u8> active_bits with fixed-size arrays
(e.g., [i8; 32] and [u8; 32]). Eliminates heap allocation on every
recursive call. Should give 5-15% speedup in hot path.

### 21. Better variable ordering for BFS
**Status**: Untested.
Try orderings that minimize peak states per level in BFS. Candidates:
constraint-density ordering (most-constrained-first), or reverse bounce.
Can dramatically reduce peak memory and total states enumerated.

### 22. Compressed node storage (file size)
**Status**: Untested.
Delta-encode or LZ4-compress the node array before writing. The 4-way
children arrays have lots of DEAD entries and sequential IDs. Could cut
file size 50-80% for easier transfer between machines.

### 23. Parallel BFS level expansion
**Status**: Untested.
Parallelize state expansion within each BFS level using rayon.
Each state's 4 children are independent. Shard the HashMap by key prefix.
Expected 3-4x speedup on 4 cores.

### 24. Streaming two-level BFS with disk spill
**Status**: Untested.
In BFS, only keep the current and next level in RAM. Write completed
levels to disk (redb or raw file). Read back during bottom-up node build.
Reduces peak memory from O(total_states) to O(max_states_per_level).

### 25. XY sub-MDD caching by zw_sums signature
**Status**: Untested.
Many of the 5.3M ZW boundaries produce identical or similar XY sub-MDDs.
Cache completed XY sub-MDD roots keyed by zw_sums. If the same zw_sums
appears twice, reuse the XY root. Eliminates redundant XY builds entirely.

### 26. Batch XY builds with shared memo
**Status**: Untested.
Group ZW boundaries by compatible zw_sums patterns. Build XY sub-MDDs
in batches, keeping the XY memo warm across the batch. Increases XY memo
hit rate from 8% to potentially 50%+.

## Rejected Ideas

### 7 (old). Clear completed level memos during DFS
**Status**: Rejected.
Analysis shows DFS memo entries are needed across all levels simultaneously.
Can't clear a level's memo until the entire build completes. Useless.

### XY memo with zw_sums in key (shared across calls)
**Status**: Rejected (OOM).
Including zw_sums in the XY memo key causes 30M+ entries for k=8.
Per-call clearing with range pruning is much better.
