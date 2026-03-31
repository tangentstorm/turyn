# Turyn Search Optimization Log

This file tracks performance-oriented changes and their measured impact.

## Benchmark protocol (use this for apples-to-apples comparison)

Build once in release mode. Run both benchmarks. Each should take ~6–10s per run, long enough to avoid system noise.

### Primary: Exhaustive search (Phase B throughput)

```bash
cargo build --release
target/release/turyn --n=16 --theta=20000 --max-z=50000 --max-w=50000 --max-pairs=2000 --benchmark=3
```

- Compare `benchmark,summary,mean_ms=...` and `median_ms=...`.
- Exercises Phase B: DFS sequence generation + FFT spectral filtering.
- Phase C (XY backtracking) is never entered at this n/θ — `xy_nodes=0`.
- Each run takes ~6s. Deterministic (same work units each run).
- Does not find a solution (spectral pair filter rejects all Z/W pairs at n=16).

### Secondary: Stochastic search (SA throughput)

```bash
target/release/turyn --n=16 --stochastic-secs=10 --benchmark=3
```

- Compare `benchmark,summary,mean_flips_per_sec=...` and `median_flips_per_sec=...`.
- Exercises the simulated annealing inner loop: pair swap + O(n) incremental defect update.
- Each run is time-limited to 10s. Measures **flips/sec** (SA move evaluations per second).
- May or may not find a solution within the time window (TT(16) SA typically solves in 1–9s).
- When a solution is found, the run stops early but flips/sec is still valid.
- Stretch goal: once stochastic improvements push TT(18) into range, switch to `--n=18`.

### Rules

- Keep all benchmark parameters fixed when comparing two versions.
- Run both benchmarks for each optimization; an idea may help one and hurt the other.
- Benchmark runs should target 6–60s each. Under 6s is too noisy; over 60s wastes iteration time.

## Current baseline (latest)

- Exhaustive search (n=16, theta=20000):
  - Command: `target/release/turyn --n=16 --theta=20000 --max-z=50000 --max-w=50000 --max-pairs=2000 --benchmark=3`
  - Result: `mean_ms=6092, median_ms=6160`

- Stochastic search (n=16, 10s time limit):
  - Command: `target/release/turyn --n=16 --stochastic-secs=10 --benchmark=3`
  - Result: `mean_flips_per_sec=41_650_115, median_flips_per_sec=41_608_236`

### Legacy baselines (for reference)

- Exhaustive search (n=14, theta=128):
  - `mean_ms=5.70, median_ms=5.69`
- Exhaustive search (n=16, theta=256):
  - `mean_ms=20.20, median_ms=20.17`
- Previous n=22 exhaustive baseline (different machine):
  `mean_ms=11222.901`, `median_ms=11148.973`
- Stochastic search (time-to-solution, no time limit):
  - TT(6): ~0.6ms, TT(8): ~0.8ms, TT(14): ~4.5s, TT(16): ~1.5–8.5s
  - TT(18): converges in ~580s (slow), TT(22): does not converge



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
| 2026-03-30 | Pre-build per-sequence value-grouped index lists for O(1) SA partner selection. Eliminates random-probe loop (up to seq_len retries per flip). | Partner finding was the main per-flip overhead beyond delta computation: random probing hit wrong-value or same-position indices frequently, wasting iterations. Grouped lists give O(1) valid partner every time. | Stochastic: `34.13M → 41.65M flips/sec` (**+22.0%**). Exhaustive: neutral. |
| 2026-03-30 | Simplified SA delta-corr from multiple multiply-accumulate pairs to single `-2*vi*nb*weight` formula per lag. | Same-value swaps have a clean delta: `-2v * (sum of non-overlapping neighbors)`. Fewer multiplies, cleaner branches, better codegen. | Stochastic: `32.03M → 34.13M flips/sec` (**+6.6%**). Exhaustive: neutral. |
| 2026-03-31 | Flat clause storage in radical: replace `Vec<Clause>` (each with `Vec<Lit>`) with flat `Vec<Lit>` + `Vec<ClauseMeta>` indexed by start/len. | Solver clone becomes a single memcpy of two flat arrays instead of thousands of individual Vec heap allocations. Dominant cost at ~1ms/clone with 5K clauses. | Hybrid n=14: `11.9s → 9.2s` (**-23%**). |
| 2026-03-31 | Feasibility pre-filter for SAT X/Y: check target parity and counter range before cloning solver. Skip infeasible Z/W pairs without clone overhead. | Avoids cloning and solving for Z/W pairs whose autocorrelation targets are out of range or have wrong parity — detected in O(n) without touching the solver. | Hybrid n=14: `18.2s → 11.9s` (**-34%**). |
| 2026-03-31 | CaDiCaL SAT solver integration (`--sat` mode). Encodes TT constraints as CNF with XNOR agree variables, sequential counters for sums, selector-based weighted cardinality for autocorrelation. | SAT/CDCL solvers use conflict-driven clause learning and restarts, which can prune the search space far more effectively than custom DFS for highly constrained combinatorial problems. | TT(4): <1ms, TT(8): 1.6ms, TT(10): 91ms, TT(12): 552ms, TT(14): 554ms, TT(16): 4.6s, **TT(18): 89s** (vs SA 580s, **6.5x faster**). |
| 2026-03-30 | SA early termination: in cold phase (temp < 1.0), stop delta-defect computation when partial sum exceeds current defect. | Most SA moves in the cold phase are bad; early termination skips remaining lag computations for clearly-rejected moves, saving O(n) work per rejected flip. | Stochastic: `29.36M → 32.03M flips/sec` (**+9.1%**). Exhaustive: neutral. |
| 2026-03-30 | Replaced manual O(θ×n) DFT in `spectrum_if_ok` with `rustfft` crate FFT using zero-padded sequences. FFT size = max(4n, 2θ) rounded to power of 2, with reusable buffer. | FFT computes full power spectrum in O(M log M) vs manual DFT's O(θ×n). For θ=256, n=16: FFT(512) does ~4.6K ops vs manual 4096 multiply-accumulates, with better SIMD utilization from optimized FFT library. | ~47-49% improvement: n=14 θ=128 mean `11.09 → 5.70` ms (**-48.6%**), n=16 θ=256 mean `38.25 → 20.20` ms (**-47.2%**). |
| 2026-03-30 | Added multi-threaded stochastic local search (`--stochastic`) using simulated annealing with O(n) incremental defect updates. | Enables finding Turyn sequences at sizes where exhaustive DFS is infeasible. Sum-preserving pair swaps, adaptive cooling, one SA worker per core. | TT(6): 0.6ms, TT(8): 0.8ms, TT(14): 175ms. |
| 2026-03-30 | Disabled FFT spectral path and DFS parity pruning from Grok bundle (both regressions). Kept XY dynamic variable ordering and bucket capping. | FFT path caused regression even when inactive (branch overhead, icache). DFS parity pruning was redundant with existing per-branch sum checks. | n=14: Grok 23ms → 21ms, n=16: Grok 80ms → 77ms. Recovers pre-Grok baseline while keeping beneficial Grok changes. |
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
