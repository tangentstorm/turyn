# IDEAS

Ideas collected from Grok (credit: Grok for every item below).

## Implemented experiments (measured)

- **SIMD in autocorr and spectrum** *(from Grok)*: Tried a SIMD-friendly step (manual loop unrolling in autocorrelation and XY verification hot loops). On benchmark (`--n=16 --theta=256 --max-z=50000 --max-w=50000 --max-pairs=2000 --benchmark=3`) mean improved from `101.115ms` to `97.412ms` (~3.7% faster).
- **XY backtracker** *(from Grok)*: Implemented a dynamic variable ordering heuristic (pick next unassigned position with the most interactions with already-assigned variables, including mirror effects). On benchmark (`--n=16 --theta=256 --max-z=50000 --max-w=50000 --max-pairs=2000 --benchmark=3`) mean improved from `103.510ms` to `88.153ms` (~14.8% faster).
- **Memory** *(from Grok)*: Added capped per-bucket retention during Z/W generation (`HashMap<BoundarySignature, Vec<...>>` keeps only up to `max_pairs_per_bucket` entries per signature). On benchmark (`--n=16 --theta=256 --max-z=50000 --max-w=50000 --max-pairs=2000 --benchmark=3`) mean improved from `88.153ms` to `72.745ms` (~17.5% faster) while reducing peak bucket growth.

## Tried (no meaningful impact yet)

- **FFT for spectrum** *(from Grok)*: Replaced the manual trigonometric loop with an in-tree FFT path for power-of-two grids, with fallback to trig for others. Benchmark (`--n=16 --theta=256 --max-z=50000 --max-w=50000 --max-pairs=2000 --benchmark=3`) regressed from mean `91.363ms` (baseline) to `101.115ms` (about 10.7% slower).
  - **Revisited (2026-03-30)**: Replaced manual DFT with `rustfft` crate (proper dependency). FFT size = max(4n, 2*theta_samples) rounded to power of 2, with reusable buffer. Result: n=14 θ=128 mean 11.09→5.70ms (**-48.6%**), n=16 θ=256 mean 38.25→20.20ms (**-47.2%**). Previous in-tree FFT regressed due to branch overhead; proper `rustfft` avoids this entirely. **Implemented.**
- **Better Z/W generation** *(from Grok)*: Added tighter global DFS bounds + parity pruning in `generate_sequences_with_sum_visit`. On the same benchmark profile, mean regressed from `97.412ms` to `103.510ms`.

## Ideas from Gemini (credit: Gemini for every item below)

- **Incremental Spectral Pruning in XY backtracker** *(from Gemini)*: Track running DFT sums (re_x, im_x, re_y, im_y) in XYState. Pre-calculate a spectral budget per frequency for each (Z,W) pair: `budget_k = (4n-2) - 2|DFT_Z(ω_k)|² - 2|DFT_W(ω_k)|²`. On each set_pair, update complex sums using SpectralTable. Prune if `|DFT_X_partial|² + |DFT_Y_partial|² > budget_k + ε` at any frequency.
  - **Tried (2026-03-30)**: Implemented full incremental DFT tracking in XYState with spectral budget pruning. Regression: n=14 10.93→12.15ms (+11%), n=16 37.63→43.26ms (+15%). The standard benchmarks have xy_nodes=0 (backtracking never entered), so pruning adds only overhead. Would only help when Phase C is the bottleneck.

- **SIMD-Accelerated Autocorrelation** *(from Gemini)*: Replace manual 4x loop unrolling in autocorrelation hot loops with explicit SIMD (std::simd or `wide` crate). Store sequences as aligned i8 slices. Use 256-bit vector multiply-and-add to process 32 elements per cycle.
  - **Tried (2026-03-30)**: Replaced branching in `spectrum_if_ok` with branchless multiply (`v as f64 * cos`) and pre-computed i32/f64 values. On heavy spectral benchmark (n=16, θ=49152, ~8s/run): baseline mean=7820ms, branchless mean=8244ms (**5.4% regression**). The branch predictor handles {±1} sequences well; conditional add/sub avoids multiply latency. Stable Rust lacks `std::simd`; the `wide` crate would add a dependency. Reverted.

- **Douglas-Rachford (DR) Projection Heuristic** *(from Gemini)*: Before expensive backtrack_xy, run a few DR iterations to check if a valid (X,Y) pair is likely. Start with random X,Y in [-1,1]^n, project onto frequency constraints (rescale magnitudes so |X_k|²+|Y_k|²=budget_k via FFT/IFFT), project onto time-domain cube (clamp/signum). If no convergence after ~100 iterations, discard the (Z,W) pair.
  - **Skipped (2026-03-30)**: Two blockers: (1) Requires FFT/IFFT for the frequency-domain projection, but this project has zero external dependencies and the in-tree FFT path was already tried and reverted (10.7% regression). (2) DR is a pre-filter for backtrack_xy, but in all current benchmark profiles `pair_spec_ok=0` — backtracking is never entered, so DR would never execute. Would only help at large n where many Z/W pairs pass spectral filtering AND backtracking is the bottleneck.

- **Symmetry Breaking** *(from Gemini)*: Force X to be symmetric (x_i = x_{n-1-i}) and Y to be skew-symmetric (y_i = -y_{n-1-i}). Modify backtrack_xy to assign pairs of bits simultaneously, reducing search space from 2^{2n} to ~2^n.
  - **Rejected (2026-03-30)**: Mathematically invalid for Turyn-type binary sequences. The known TT(6) solution X=[-1,-1,-1,-1,1,-1] is NOT palindromic; Y=[-1,-1,-1,1,-1,-1] is NOT skew-symmetric. Enforcing this would miss valid solutions. The symmetry result applies to continuous-valued sequences, not binary {±1}.

## Why backtracking (Phase C) is never triggered on standard benchmarks

On all standard benchmark profiles (n=14 θ=128, n=16 θ=256, n=22 θ=192), `pair_spec_ok=0` — the combined spectral pair filter rejects every Z/W pair, so `backtrack_xy` is never called (`xy_nodes=0`). Here's why:

**The pipeline funnel (n=16 θ=256 example):**
```
z_generated = 4732  →  z_spec_ok = 1288   (individual: |Z(ω)|² ≤ 47 ∀ω)
w_generated = 8008  →  w_spec_ok = 2871   (individual: |W(ω)|² ≤ 47 ∀ω)
                           ↓ boundary bucketing + pairing
                      pair_attempts = 692
                           ↓ spectral_pair_ok: |Z(ω)|² + |W(ω)|² ≤ 47
                      pair_spec_ok = 0      ← everything dies here
                           ↓
                      xy_nodes = 0
```

**Mathematical explanation:** Parseval's identity for Turyn sequences requires at every frequency ω:

    |X(ω)|² + |Y(ω)|² + 2|Z(ω)|² + 2|W(ω)|² = 6n − 2

Since |X|², |Y|² ≥ 0, the Z+W budget is `|Z(ω)|² + |W(ω)|² ≤ (6n−2)/2`. The individual filter allows each Z or W up to the full budget (47 for n=16), but the *pair* filter requires their **sum** ≤ 47 at every frequency simultaneously. A Z with power 30 at some ω can only pair with W having power ≤ 17 at that ω.

Most generated Z/W candidates have high power (close to the bound) at overlapping frequencies. When paired, they exceed the budget. The individual bound is intentionally loose — tightening it would reject Z sequences that could pair with low-power W sequences.

**Implications for optimization ideas:**
- Any optimization targeting Phase C (backtracking) — including Gemini's incremental spectral pruning, symmetry breaking, and Douglas-Rachford — cannot improve benchmarks where Phase C is never entered.
- The actual bottleneck is Phase B: DFS sequence generation + spectral filtering of individual Z/W candidates.
- To trigger backtracking, either increase search limits dramatically or use smaller n where spectrally complementary Z/W pairs are more common.

## Ideas from Grok: SAT/CP hybrids and cross-field approaches (credit: Grok)

### SAT / CP hybrids (Bright–Kotsireas–Ganesh style)
- **SAT encoding of TT constraints**: Encode the four sequences as Boolean vars (±1 as true/false). The autocorrelation conditions `N_A(k) + N_B(k) + 2*N_C(k) + 2*N_D(k) = 0` become cardinality constraints on agreeing/disagreeing pairs at each lag (linearizable with auxiliaries). Hard-code canonical form as symmetry-breaking clauses. Use existing sum-tuple enumeration to split into cases (fix sums first), then SAT-solve within each. Modern CDCL solvers (CaDiCaL, Kissat) with learned clauses often beat custom backtrack.
- **Incremental SAT + custom backtracker**: Solve prefixes with SAT, then switch to Rust incremental autocorr engine for verification or mid-search.
- **CP/MILP alternative**: OR-Tools or Gecode with table constraints or MDDs for autocorrelation sums; PuLP/Gurobi for integer program (quadratic nature needs linearization).
- **Practical first step**: Prototype SAT export — dump partial instances (with canonical breaking) to DIMACS/PB format and test Kissat/CaDiCaL on n=38–40.

### Geometric / matrix-completion (Kline 2019 style)
- **Suffix completion via relaxation**: Generate partial (A,B,C,D) up to position m << n using current backtracker or random/spectral-guided. Treat missing suffix as unknowns. Remaining autocorrelation equations form quadratic constraints on suffix. Solve real relaxation (ignore ±1), round to nearest ±1, project back via iterative refinement or gradient descent on merit factor.
- **Partial → repair loop**: Backtrack a bit → geometric repair attempt → if promising, continue exact search or verify. Inconsistencies show early; good partials complete dramatically.
- **Upper-level completion**: Once have candidate TT quadruple, build partial Goethals–Seidel array and apply Kline-style completion/repair directly on the big matrix.

### Composition / multiplicative
- **Base sequence lifting**: TT(n) produce base sequences of lengths (2n-1, 2n-1, n, n). Base sequences have recursive/product constructions (Cooper–Wallis, etc.). Hunt for ways to lift/combine known TT-derived bases into larger ones, reverse-engineer TT quadruple.
- **Algebraic starters**: Seed C and D (shorter ones) with quadratic residues, Legendre symbols, or characters over finite fields/rings, then solve for A/B. Energy equation `A(1)^2 + B(1)^2 + 2*C(1)^2 + 2*D(1)^2 = 6n-2` suggests factorizations in cyclotomic/quaternion settings.
- **Block-Kronecker inflation**: Take two smaller TT(a), TT(b), try interleave or tensor partial correlations, then repair with geometric method.

### Cross-field analogies
- **Radar/comms (merit factor)**: TT are perfect aperiodic complementary quadruples. SA, PSO, or genetic algorithms (used on Golay pairs) can generate high-merit partials to seed exact searcher.
- **Coding theory**: Equivalent to certain constant-weight codes or difference sets. Column generation or branch-and-price techniques apply.
- **QUBO / quantum annealing**: QUBO formulations exist for smaller Turyn/Williamson (Suksmono 2022); hybrid classical-quantum for subproblems.
- **SDP relaxations**: Frequency-domain view (power spectra summing) relaxes to semidefinite programs; dual gives bounds or good continuous approximations to round + repair.
- **ML-guided search**: Train policy network (AlphaZero-style) on small-n solutions for variable ordering or promising partials. NeuroSAT-like for learning clause importance.

### Tried from Grok SAT/CP ideas

- **Z-aware per-frequency W spectral tightening** *(from Grok, "tighter spectral bounds")*: After generating all Z candidates, compute min Z power at each frequency across retained Z. Use `spectral_bound - min_z_power[k]` as tighter per-frequency bound when filtering W. At θ=256 (n=16): reduced w_spec_ok from 2871 to 2668 (**7.1% fewer W candidates**). But at the primary benchmark (θ=20000): w_spec_ok=2662 in both cases — zero additional rejections. The high spectral resolution at large θ already provides tight individual bounds. Exhaustive benchmark: `6092ms → 6325ms` (**3.8% regression** from per-frequency bound overhead). **Reverted.**

- **Legendre/QR seeding for stochastic search** *(from Grok, "algebraic starters")*: On 50% of SA restarts, seed Z/W with Legendre-symbol sequences (quadratic residues mod nearest prime) with random circular shift and negation, instead of fully random. These have good autocorrelation properties. Stochastic benchmark: flips/sec `29.36M → 27.21M` (**7.3% regression**). The fix_sum step to adjust Legendre sequences to target sums adds per-restart overhead that outweighs any benefit from better starting autocorrelation. Time-to-solution occasionally faster (194ms vs 1.4s best) but median similar. **Reverted.**

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

