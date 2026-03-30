# IDEAS

Ideas collected from Grok (credit: Grok for every item below).

## Implemented experiments (measured)

- **SIMD in autocorr and spectrum** *(from Grok)*: Tried a SIMD-friendly step (manual loop unrolling in autocorrelation and XY verification hot loops). On benchmark (`--n=16 --theta=256 --max-z=50000 --max-w=50000 --max-pairs=2000 --benchmark=3`) mean improved from `101.115ms` to `97.412ms` (~3.7% faster).
- **XY backtracker** *(from Grok)*: Implemented a dynamic variable ordering heuristic (pick next unassigned position with the most interactions with already-assigned variables, including mirror effects). On benchmark (`--n=16 --theta=256 --max-z=50000 --max-w=50000 --max-pairs=2000 --benchmark=3`) mean improved from `103.510ms` to `88.153ms` (~14.8% faster).
- **Memory** *(from Grok)*: Added capped per-bucket retention during Z/W generation (`HashMap<BoundarySignature, Vec<...>>` keeps only up to `max_pairs_per_bucket` entries per signature). On benchmark (`--n=16 --theta=256 --max-z=50000 --max-w=50000 --max-pairs=2000 --benchmark=3`) mean improved from `88.153ms` to `72.745ms` (~17.5% faster) while reducing peak bucket growth.

## Tried (no meaningful impact yet)

- **FFT for spectrum** *(from Grok)*: Replaced the manual trigonometric loop with an in-tree FFT path for power-of-two grids, with fallback to trig for others. Benchmark (`--n=16 --theta=256 --max-z=50000 --max-w=50000 --max-pairs=2000 --benchmark=3`) regressed from mean `91.363ms` (baseline) to `101.115ms` (about 10.7% slower).
- **Better Z/W generation** *(from Grok)*: Added tighter global DFS bounds + parity pruning in `generate_sequences_with_sum_visit`. On the same benchmark profile, mean regressed from `97.412ms` to `103.510ms`.

## Re-check (2026-03-30, after user follow-up)

I reran an apples-to-apples comparison of the code **before** the Grok idea bundle (`6eac0c5`) vs the bundle commit (`7b0894c`) using the same benchmark profile and more repeats:

- `target/release/turyn --n=16 --theta=256 --max-z=50000 --max-w=50000 --max-pairs=2000 --benchmark=15`
- Before bundle (`6eac0c5`): `benchmark,summary,mean_ms=44.160,median_ms=39.546,repeats=15`
- After bundle (`7b0894c` / current): `benchmark,summary,mean_ms=45.723,median_ms=42.237,repeats=15`

**Net result:** this combined bundle is currently ~3.5% slower on mean and ~6.8% slower on median on this profile.

## Follow-up audit (2026-03-30, Claude)

Benchmarked each Grok change individually on a different machine to identify which help and which hurt. All measurements use 7 repeats.

### Benchmark results (n=16, θ=256, max-z=50000):

| Configuration | mean_ms | median_ms |
|---|---|---|
| Pre-Grok baseline | 77 | 72 |
| Full Grok bundle | 80 | 79 |
| Grok − FFT removal only | 77 | 78 |
| Grok − FFT − DFS parity | 79 | 76 |

### Benchmark results (n=14, θ=128, max-z=200000):

| Configuration | mean_ms | median_ms |
|---|---|---|
| Pre-Grok baseline | 20 | 21 |
| Full Grok bundle | 23 | 23 |
| Grok − FFT removal only | 21 | 22 |
| Grok − FFT − DFS parity | 20 | 21 |

### Conclusions:

- **FFT path**: Caused regression even when not active (θ=256 is not power-of-two). The `if !table.use_fft` branch and larger function body hurt instruction cache / branch prediction. **Disabled.**
- **DFS parity pruning**: Marginal on these benchmarks. The existing per-branch sum pruning later in the DFS already catches most infeasible nodes. **Disabled.**
- **XY dynamic variable ordering**: Kept. Good algorithmic improvement.
- **Bucket capping (push_capped)**: Kept. Reduces memory pressure.
- **Manual loop unrolling**: Kept for now (marginal ~3.7% on Grok's benchmark, neutral on ours).

