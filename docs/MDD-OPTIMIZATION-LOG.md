# MDD Optimization Log

Tracks measured before/after for MDD generation and search optimizations.

## MDD Search Pipeline Optimization (n=56 throughput)

Benchmark: `target/release/turyn --n=56 --mdd --mdd-k=10 --sat-secs=30`

| Date | Change | n=56 xy/s | Cumulative | Notes |
|------|--------|-----------|------------|-------|
| PR#54 baseline | Single-thread Phase B | 7 | 1x | Phase B bottleneck |
| 2026-04-08 | Adaptive B/C threading | 56 | 8x | Multi-thread, dispatch complexity |
| 2026-04-08 | Z SAT moved to Phase C | 137 | 20x | Z distributed to workers |
| 2026-04-08 | Unified priority queue (MDD→W→Z→XY) | 327 | 47x | One queue, stage priority |
| 2026-04-08 | Pull-based MDD (LCG paths, no partition) | 473 | 68x | Monitor feeds on demand |
| 2026-04-08 | Dual queue (gold + work) | ~680 avg | 97x | Spectral ranking for XY |
| 2026-04-08 | Spectral pair check (Idea 5) | ~680 | 97x | Fixed n=18-22 solution finding |
| 2026-04-08 | Brute-force W for small n (Idea 8) | ~680 | 97x | +10% throughput, n=22 found |

Solution finding (with --mdd pipeline):

| n | k | Status | Time |
|---|---|--------|------|
| 12 | 4 | found | 40ms |
| 14 | 4 | found | <1s |
| 16 | 4-5 | found | <1s |
| 18 | 5 | found | <1s |
| 20 | 5 | found | <20s |
| 22 | 5 | found | <60s |
| 24+ | | not found in 120s | needs more search time |
| 56 | 10 | ~680 xy/s throughput | searching |

## MDD Generation Optimization

## Benchmark protocol

```bash
# Primary benchmark: gen_mdd build time for k=8
time target/release/gen_mdd 8 /dev/null

# Extended benchmark: gen_mdd build time for k=9
time target/release/gen_mdd 9 /dev/null

# Stress test: gen_mdd for k=10+
time target/release/gen_mdd 10 /dev/null
```

## Current baseline (ZW-first builder, all optimizations, parallel)

| k | Full (par) | ZW-only (par) | Full Nodes | ZW-only Nodes | Full Size | ZW-only Size |
|---|-----------|--------------|-----------|--------------|----------|-------------|
| 7 | 0.3s | 0.1s | 69K | ~5K | 1.0 MB | ~0.1 MB |
| 8 | 0.8s | 0.3s | 433K | ~30K | 6.6 MB | ~0.5 MB |
| 9 | 7.1s | 3.0s | 2.6M | 175K | 39.6 MB | 2.7 MB |
| 10 | 104s | 50s | 17.2M | 803K | 262 MB | 12.2 MB |
| 11 | ~2h (est) | TBD | ~170M (est) | TBD | ~2.6 GB | TBD |

Original baselines: k=7: 4.7s, k=8: 46.6s, k=9: OOM/timeout

## Optimization history

| Date (UTC) | Change | Why it helps | Measured effect |
|---|---|---|---|
| | (baseline) | | k=7: 4.7s, k=8: 46.6s, k=9: >120s |
| 2026-04-06 | Pack sums u128 + periodic GC in reorder | Eliminates Vec<i8> heap allocs; GC reduces reorder peak memory 3x | k=8: 46.6→39.5s (-15%); k=9: timeout→7m56s (works!) |
| 2026-04-06 | Partial lag range pruning | Prunes branches where partial sums exceed remaining event budget | k=8: 39.5→25.4s (-36%); k=9: 7m56→4m43 (-40%) |
| 2026-04-06 | FxHashMap (rustc-hash) for all memo/unique tables | FxHash ~4x faster than SipHash for u128/u64 keys | k=8: 25.4→11.1s (-56%); k=9: 4m43→2m12 (-53%) |
| 2026-04-06 | Hash-based unique table (u64 key) | Reduces unique table from ~80B/entry to ~20B/entry | ~5% speedup, major memory reduction |
| 2026-04-06 | ZW-first with range pruning as default | Range pruning makes per-call XY memo viable; 4-way nodes = 4x less memory | k=8: 11.1→7.3s (-34%); k=9: 2m12→1m17 (-40%); k=10: OOM→21m33s! |
| 2026-04-06 | Smart memo eviction (50M cap) | Clear deepest level when memo budget exceeded; keeps shallow-level cache warm | k=10: OOM→21m33s, peak 4.4GB RAM |
| 2026-04-06 | Parallel level-1 branches (rayon) + post-merge dedup | 4 branches run independently, then dedup removes duplicates (40% reduction) | k=8: 7→3.9s; k=9: 79→47s; k=10: 21m33→10m30 (2x faster) |
| 2026-04-07 | XY sub-MDD caching by zw_sums (u128 key) | 74% of ZW boundary visits have duplicate sums; skip rebuilding XY sub-MDD | k=8 seq: 7.7→3.1s (-60%); k=9 seq: 93.8→37.8s (-60%); k=9 par: 40→28.1s (-30%) |
| 2026-04-07 | Flat Vec<usize> active_indices + stack arrays | Replace HashMap→flat array for pos→index lookup; [u8;32] stack arrays | k=9 seq: 37.8→28s (-26%); k=9 par: 28.1→10.2s (-64%) |
| 2026-04-07 | BFS builder with optimized Pass 2 | Complete ZW+XY BFS builder; stores children indices to avoid re-expansion | BFS k=9: 144→57s; DFS still faster for k≤10 |
| 2026-04-07 | Configurable memo cap (default 80M) | MDD_MEMO_CAP env var; default increased from 50M to 80M | k=10 par: 191s (was ~10min before all opts); k=11 seq: in progress |
| 2026-04-07 | Pre-resolve event indices + delta lookup tables | Precompute active index lookups and 4x4 delta tables at build time | k=10: 144→128s (-11%) |
| 2026-04-07 | Delta-subtract restore (no pack/unpack) | Subtract same deltas instead of packing to u128 and unpacking | k=9: 9.6→6.8s (-29%); k=10: 128→104s (-19%) |
| 2026-04-07 | ZW-only mode (--zw-only) | Skip XY sub-MDD building; LEAF at ZW boundary with range check | k=9: 7.4→3.0s (2.5x); k=10: 103→50s (2x); file 15-21x smaller |
