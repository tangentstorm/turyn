# Turyn Search Optimization Log

This file tracks performance-oriented changes and their measured impact.

## Benchmark protocol (use this for apples-to-apples comparison)

- Build once in release mode.
- Run exactly:

```bash
cargo build --release
target/release/turyn --n=22 --theta=192 --max-z=200000 --max-w=200000 --max-pairs=2000 --benchmark=3
```

- Compare `benchmark,summary,mean_ms=...` and `median_ms=...`.
- Keep all benchmark parameters fixed when comparing two versions.

## Smallest benchmark profile that currently finds a solution (under 10s)

- Command:
  `target/release/turyn --n=4 --theta=64 --max-z=200000 --max-w=200000 --max-pairs=2000 --benchmark=1`
- Result:
  - `warmup found_solution=true`
  - `run found_solution=true`
  - `mean_ms=0.052`

## Current baseline (latest)

- Command:
  `target/release/turyn --n=22 --theta=192 --max-z=200000 --max-w=200000 --max-pairs=2000 --benchmark=3`
- Result:
  - `mean_ms=11222.901`
  - `median_ms=11148.973`



## Grok-idea experiment audit (2026-03-30 follow-up)

To verify the user-reported concern, I reran the profile used by `IDEAS.md` with more repeats and compared the commit just before the Grok bundle against the bundle commit itself.

- Command:
  `target/release/turyn --n=16 --theta=256 --max-z=50000 --max-w=50000 --max-pairs=2000 --benchmark=15`
- Before (`6eac0c5`): `mean_ms=44.160`, `median_ms=39.546`
- After (`7b0894c`): `mean_ms=45.723`, `median_ms=42.237`
- Net: **regression** (~3.5% mean, ~6.8% median).

Note: the previous per-idea claims in `IDEAS.md` were not backed by a step-by-step optimization log in this file. This follow-up entry corrects that gap with a direct before/after audit and explicit benchmark command.

## Profiling

- See `docs/PROFILING.md` for the currently working profiling workflow in this container (gprof fallback), plus why `perf`/Cargo-based profiler installs are currently blocked by repository/network 403 errors.

## Optimization history

| Date (UTC) | Change | Why it helps | Measured effect |
|---|---|---|---|
| 2026-03-30 | Audited Grok optimization bundle as a single before/after comparison (`6eac0c5` -> `7b0894c`) on the IDEA profile. | Verifies whether the combined set of changes actually improved runtime under the documented benchmark command. | Regression on this profile: mean `44.160 -> 45.723` ms (~3.5% slower), median `39.546 -> 42.237` ms (~6.8% slower). |
| 2026-03-30 | Replaced linear-search removal from `XYState.assigned_positions` with O(1) slot-tracked swap-remove bookkeeping (`assigned_position_slot`). | Eliminates repeated vector scans in the hottest XY backtracking set/unset path while preserving fast iteration over assigned indices for lag updates. | ~22.25% mean improvement and ~22.91% median improvement on the long benchmark (`14434.113 -> 11222.901` mean, `14462.829 -> 11148.973` median). |
| 2026-03-30 | Switched boundary bucket keys from heap-allocated `Vec<i8>` signatures to packed-bit signatures for small `k`, and rewired XY lag updates to iterate currently assigned positions instead of scanning all lags per set/unset. | Removes per-sequence key allocation/hashing overhead in Phase B and trims redundant lag-loop work in XY state updates. | ~5.83% mean improvement and ~6.17% median improvement on the new longer-chain benchmark (`11663.583 -> 10984.050` mean, `11676.437 -> 10955.741` median). |
| 2026-03-28 | Added explicit warmup run in benchmark mode before measured repeats. | Removes cold-start noise from reported benchmark summary and makes comparisons more stable. | New baseline from warm runs: `mean_ms=5.195`, `median_ms=5.291` (`--benchmark=7`). |
| 2026-03-28 | Hoisted i8→f64 conversion out of inner spectral loops (build `values_f64` once per generated sequence, then use it across all theta samples in `spectrum_if_ok`). | Removes repeated per-sample scalar casts in the hottest spectral loop. | ~34.12% mean improvement and ~31.42% median improvement vs immediate prior run (`19.094 -> 12.579` mean, `18.071 -> 12.392` median). |
| 2026-03-28 | Streamed sequence generation via callback (`generate_sequences_with_sum_visit`) and processed raw `&[i8]` values directly in Phase B (`spectrum_if_ok`, `autocorrs_from_values`, boundary signature). Only materialize `PackedSeq` for retained candidates. | Removed repeated pack/unpack and temporary object churn in candidate generation. | ~31.44% mean improvement and ~28.03% median improvement vs prior baseline (`8.984 -> 6.159` mean, `8.394 -> 6.041` median). |
| 2026-03-28 | Adaptive non-verbose parallel tuple processing with `available_parallelism()` and small-workload sequential fallback. | Uses multicore where useful while avoiding overhead on tiny workloads. | ~24.00% mean improvement and ~19.01% median improvement (`12.618 -> 9.592` mean, `11.978 -> 9.701` median). |
| 2026-03-28 | Tightened DFS feasibility bounds with forced-tail contribution in sequence generation. | Earlier pruning of impossible branches in generator DFS. | ~14.62% mean improvement and ~15.56% median improvement (`14.778 -> 12.618` mean, `14.185 -> 11.978` median). |

## How to update this file going forward

For each optimization PR/commit:

1. Add one row to **Optimization history** with:
   - UTC date,
   - concise change summary,
   - one-sentence explanation,
   - before/after benchmark numbers.
2. Update **Current baseline (latest)** to the newest measured values.
3. Keep benchmark command unchanged unless intentionally creating a *new benchmark profile*.

If a new benchmark profile is needed (e.g., TT(56) stress profile), add a separate section with explicit command and keep historical comparisons within the same profile.
