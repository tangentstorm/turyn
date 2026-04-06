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

## Current baseline

| k | Time | Notes |
|---|------|-------|
| 7 | 4.7s | 168K 16-way nodes, 69K 4-way after reorder |
| 8 | 46.6s | 1.6M 16-way nodes, 433K 4-way after reorder |
| 9 | >120s | Timeout (only 1/4 of level 1 done) |

## Optimization history

| Date (UTC) | Change | Why it helps | Measured effect |
|---|---|---|---|
| | (baseline) | | k=7: 4.7s, k=8: 46.6s, k=9: >120s |
| 2026-04-06 | Pack sums u128 + periodic GC in reorder | Eliminates Vec<i8> heap allocs; GC reduces reorder peak memory 3x | k=8: 46.6→39.5s (-15%); k=9: timeout→7m56s (works!) |
| 2026-04-06 | Partial lag range pruning | Prunes branches where partial sums exceed remaining event budget | k=8: 39.5→25.4s (-36%); k=9: 7m56→4m43 (-40%) |
| 2026-04-06 | FxHashMap (rustc-hash) for all memo/unique tables | FxHash ~4x faster than SipHash for u128/u64 keys | k=8: 25.4→11.1s (-56%); k=9: 4m43→2m12 (-53%) |
