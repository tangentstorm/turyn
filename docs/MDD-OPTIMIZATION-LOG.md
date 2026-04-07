# MDD Optimization Log

Tracks measured before/after for MDD generation optimizations.

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

| k | Time (par) | Time (seq) | Nodes | File size |
|---|-----------|-----------|-------|-----------|
| 7 | 0.3s | 0.3s | 69K | 1.0 MB |
| 8 | 1.6s | 3.1s | 433K | 6.6 MB |
| 9 | 28.1s | 37.8s | 2.6M | 39.6 MB |
| 10 | ~7min | ~15min | 17.2M | 262 MB |
| 11 | ~2h (est) | ~5h (est) | ~170M (est) | ~2.6 GB (est) |

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
