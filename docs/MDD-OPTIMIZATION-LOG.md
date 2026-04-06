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
