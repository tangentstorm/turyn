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

### Implemented from Grok SAT/CP ideas

- **CaDiCaL SAT solver integration** *(from Grok, "SAT/CP hybrids")*: Added `--sat` mode using the `cadical` crate (CaDiCaL v1.9.5 with Rust bindings). Encodes TT(n) as a SAT instance with: Boolean variables for ±1 sequence positions, XNOR auxiliary variables for agree/disagree at each lag, sequential counter (Sinz 2005) for exact cardinality on sums, and selector-based weighted cardinality for the autocorrelation constraints (separate XY/ZW counters with enumerated valid splits). Iterates over all distinct sum-tuples with x[0]=+1 symmetry breaking. Results: TT(4)–TT(18) all found. TT(18) in 89s vs SA's 580s (**6.5x faster**). **Implemented.**

### Tried from Grok SAT/CP ideas

- **Z-aware per-frequency W spectral tightening** *(from Grok, "tighter spectral bounds")*: After generating all Z candidates, compute min Z power at each frequency across retained Z. Use `spectral_bound - min_z_power[k]` as tighter per-frequency bound when filtering W. At θ=256 (n=16): reduced w_spec_ok from 2871 to 2668 (**7.1% fewer W candidates**). But at the primary benchmark (θ=20000): w_spec_ok=2662 in both cases — zero additional rejections. The high spectral resolution at large θ already provides tight individual bounds. Exhaustive benchmark: `6092ms → 6325ms` (**3.8% regression** from per-frequency bound overhead). **Reverted.**

- **Greedy repair near solution** *(from Grok, "geometric repair / Kline 2019")*: When SA defect drops below 4*n, switch to exhaustive steepest-descent: try all O(n²) same-value pair swaps across all 4 sequences, take the best improving one, repeat until stuck. At n=16: flips/sec `32.03M → 30.06M` (**6.1% regression**) because each greedy evaluation is O(n³) total. All runs found solutions (benefit in convergence), but at n=18 defect still stuck at ~40-56 (greedy can't escape local minima deeper than pair swaps). The quadratic constraint structure means nearby solutions aren't reachable by pair swaps alone. **Reverted.**

- **Simplified delta-corr computation** *(from Grok, "merit factor optimization")*: Refactored SA inner loop delta computation from multiple multiply-accumulate pairs to a single `-2*vi*nb*weight` formula. Since seq[p]=seq[q]=v (same-value swap), the delta at each lag reduces to `-2v * (sum of 4 non-overlapping neighbors)`. Fewer multiplies and cleaner branch structure. Stochastic benchmark: `32.03M → 34.13M flips/sec` (**+6.6%**). Exhaustive: neutral. **Implemented.**

- **Pre-grouped value indices for O(1) SA partner selection** *(from Grok, "efficient search data structures")*: Pre-build per-sequence lists of indices with value +1 and -1. Partner selection becomes O(1) random index from the matching group, eliminating the random-probe loop (up to seq_len retries). Updates on accept: O(n/2) retain + push. Stochastic benchmark: `34.13M → 41.65M flips/sec` (**+22.0%**). Exhaustive: neutral. **Implemented.**

- **Lag-targeted SA move selection** *(from Grok, "radar/comms merit factor")*: On 25% of SA flips, find the worst lag s* (max |corr[s]|), then pick positions p, q at distance s* for the swap. This ensures swaps directly affect the highest-defect lag. Stochastic benchmark: `32.03M → 29.52M flips/sec` (**7.8% regression**). The O(n) worst-lag scan on 25% of flips plus extra branch overhead and same-value fallback costs more than any convergence benefit. SA's existing random exploration with temperature scheduling already handles lag targeting implicitly through the accept/reject criterion. **Reverted.**

- **Legendre/QR seeding for stochastic search** *(from Grok, "algebraic starters")*: On 50% of SA restarts, seed Z/W with Legendre-symbol sequences (quadratic residues mod nearest prime) with random circular shift and negation, instead of fully random. These have good autocorrelation properties. Stochastic benchmark: flips/sec `29.36M → 27.21M` (**7.3% regression**). The fix_sum step to adjust Legendre sequences to target sums adds per-restart overhead that outweighs any benefit from better starting autocorrelation. Time-to-solution occasionally faster (194ms vs 1.4s best) but median similar. **Reverted.**

## Ideas from London thesis (credit: Stephen London, PhD thesis "Constructing New Turyn Type Sequences, T-Sequences and Hadamard Matrices", UIC 2013)

London holds the record for longest known Turyn type sequences (TT(40)). His thesis describes an optimized version of Kharaghani's algorithm with several key optimizations (§3.3–3.4, §5.1):

1. **Integer spectral storage** *(London §3.4, item 1)*: Store ⌊f_Z(θ)/2⌋ and ⌊f_W(θ)/2⌋ as 1–2 byte integers instead of 8-byte f64. Saves 4–8× memory per spectrum and speeds up pair comparisons. London's pair filter checks `⌊f_Z(θ_k)/2⌋ + ⌊f_W(θ_k)/2⌋ ≤ M` using integer arithmetic.

2. **Precomputed cosine lookup arrays** *(London §3.4, item 2)*: Precompute at most 10,000 distinct cosine values in arrays. Our FFT-based approach already handles this differently, but for non-FFT paths this could help.

3. **Difference arrays for cycling variables** *(London §3.4, item 3)*: Store the difference between k-th and (k+1)-st spectral value when iterating. Enables O(1) incremental spectral updates during DFS rather than recomputing from scratch.

4. **Pair-based tuple searching** *(London §3.4, item 4)*: Enter a (σ_Z, σ_W) pair rather than individual sum tuples, allowing multiple quadruples to be checked in a single run. Our code currently iterates individual sum tuples; grouping by pair could reduce redundant Z/W generation.

5. **Distance arrays for DFS pruning** *(London §3.4, item 5)*: Create (σ_Z, σ_W)-indexed arrays of distances to the nearest feasible solution. Allows early pruning in DFS when partial sums are too far from any feasible target.

6. **Optimal theta ≈ 100** *(London §3.4, item 6)*: London found 100 equally spaced θ values approximately minimizes total running time (balancing spectral resolution vs computation cost). Our default is 256.

7. **Outside-in X,Y construction with Turyn's theorem** *(London §3.3, Step 6)*: Build X,Y from position 6 inward toward the middle. At each step k, try all 8 possibilities for (x_k, y_k, x_{ℓ+1-k}), then use σ_X = σ_Y = 0 (Turyn's theorem) to derive y_{ℓ+1-k}. Reduces branching factor from 16 to 8 per step.

8. **Prefix/suffix pre-enumeration** *(London §3.3, Step 1)*: Pre-enumerate all valid first/last 6 elements of X, Y, Z (1,911,620 possibilities). These are filtered by normalization, sum constraints, and spectral feasibility. For each (Z,W) pair, look up matching boundary prefixes/suffixes for X,Y instead of generating from scratch.

9. **Spectral budget restriction** *(London §5.1)*: For longer sequences where full enumeration is infeasible, restrict ⌊f_Z(θ_k)/2⌋ + ⌊f_W(θ_k)/2⌋ ≤ M for some M < spectral_bound. Table V shows M values needed: e.g., M=66 finds first TT(32), M=84 finds first TT(40). A `--max-spectral` CLI parameter would enable this.

10. **4-profile equivalence checking** *(London §3.4, item 7, §2.7)*: Check Hadamard matrix equivalence via 4-profiles (count 4-row inner products). ~10 minutes per matrix. Not directly relevant to search speed but useful for verifying uniqueness of results.

### Implemented from London thesis

- **Spectral budget restriction (`--max-spectral`)** *(London §5.1)*: Added `--max-spectral=M` CLI parameter. Restricts spectral pair filter to `|Z(ω)|² + |W(ω)|² ≤ M` at every frequency. Individual filtering still uses full spectral_bound. Trades completeness for dramatically reduced search space at larger n. London used M=66 for first TT(32), M=84 for first TT(40). No regression on existing benchmarks (pair filter already rejects everything at n=16). **Implemented.**

- **Early sum feasibility pruning in XY backtracker** *(London §3.3, Step 6)*: Restructured backtrack_xy to set pos first, then pre-check sum feasibility for the mirror position BEFORE the expensive set_pair(mirror) call. Also checks x and y sum bounds independently for xq and yq. Additionally fixed a latent bug where the backtracker would corrupt state when the mirror position was already assigned. Phase C benchmark (n=16, θ=100): xy_nodes `901,772 → 10,368` (**87× reduction**), runtime `1903ms → 17.5ms` (**-99.1%**). Primary exhaustive benchmark (θ=20000): neutral (Phase C not triggered). **Implemented.**

### Tried from London thesis (no improvement on current benchmarks)

- **Integer spectral storage** *(London §3.4, item 1)*: Tried storing ⌈power/2⌉ as i16 (1-2 bytes) instead of f64 (8 bytes) for spectrum values. Individual filtering still uses f64; integer storage only for pair comparisons. Exhaustive (θ=20000): `5957 → 6209ms` (**+4.2% regression**). Light (θ=256): `20.9 → 26.5ms` (**+27% regression**). The `(p/2.0).ceil() as i16` conversion in the hot FFT post-processing loop adds overhead without benefit since pair_spec_ok=0 at these benchmark sizes. Memory savings would only matter with millions of stored spectra at larger n. **Reverted.**

- **Pair-based tuple searching** *(London §3.4, item 4)*: Checked whether normalized tuples share (|z|, |w|) sums, which would allow reusing Z/W candidates across tuples. For n=16: all 4 tuples have unique (|z|, |w|) pairs. For n=22: all 10 tuples have unique (|z|, |w|) pairs. No savings possible at current benchmark sizes. **Not implemented.**

- **Optimal theta ≈ 100** *(London §3.4, item 6)*: Tested theta values 50–20000 on both exhaustive and solution-finding benchmarks. Results are configuration-dependent: theta=100 is fastest for Phase B (FFT cost scales with theta) but lets more Z/W pairs through, triggering expensive Phase C at n=16 (1622ms). theta=200+ rejects all pairs at n=16, giving 22ms. London's theta=100 is optimal for his non-FFT spectral computation; for our FFT-based approach, theta=200–256 is the sweet spot for n=16. **Configuration finding, not code change.**

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

## Ideas from Claude: radical SAT solver improvements (credit: Claude)

The Phase C SAT solver (radical) is the bottleneck at n=22, consuming ~96% of compute. CaDiCaL has several techniques that radical lacks. Prioritized by expected impact:

1. **Learnt clause minimization** *(from Claude)*: After 1-UIP conflict analysis, recursively remove redundant literals from the learnt clause. A literal is redundant if its reason clause is entirely subsumed by other literals already in the learnt clause (or at decision level 0). CaDiCaL's `minimize` pass typically shrinks learnt clauses 20-30%, improving propagation efficiency and reducing clause database bloat.

2. **EMA-based restarts** *(from Claude)*: Replace the fixed Luby restart schedule with glucose-style EMA (exponential moving average) tracking of recent vs. global LBD quality. Restart when recent LBD average exceeds global average by a margin. More adaptive than Luby — restarts aggressively when the solver is exploring unproductive regions, and holds steady when making progress.

3. **Failed literal probing** *(from Claude)*: At the start of solving (or periodically), probe each unassigned literal: assume it true, propagate, and if a conflict arises, the literal must be false. Also detects equivalent/implied literals. Particularly effective on structured/combinatorial instances with many binary implications, like the cardinality encodings used here.

4. **On-the-fly self-subsumption** *(from Claude)*: During conflict analysis, when resolving with a reason clause, check if the resolvent subsumes the reason clause. If so, strengthen the reason clause by removing the resolved literal. This is essentially free (check during existing analysis loop) and produces stronger propagation in future conflicts.

5. **Blocker literal in watch lists** *(from Claude)*: Store a "blocker" literal (the other watched literal) alongside each clause index in watch lists. Before accessing clause memory during BCP, check if the blocker is already true — if so, skip entirely. Avoids cache-miss-heavy clause access for satisfied clauses.

6. **Assumptions-based incremental solving** *(from Claude)*: Instead of cloning the solver template for each Z/W pair, use `solve_with_assumptions()` to pass per-pair cardinality targets as temporary assumptions. Avoids clone overhead and lets learnt clauses persist across candidates.

7. **CaDiCaL backend via feature flag** *(from Claude)*: Optional `--features cadical` compile-time flag that swaps radical for CaDiCaL (v1.9.5). Useful as a performance reference and for larger instances where CaDiCaL's preprocessing (BVE, subsumption, probing) pays off.

### Implemented from Claude SAT ideas

- **Assumptions-based incremental solving** *(from Claude, idea 6)*: Switched `SatXYTemplate::solve_for()` from cloning the solver to using `solve_with_assumptions()`. Learnt clauses now persist across Z/W pairs for the same tuple. Benchmark n=22: `21.3s → 19.7s` (**-7.5%**). **Implemented.**

- **Blocker literal in watch lists** *(from Claude, idea 5)*: Changed watch lists from `Vec<u32>` to `Vec<(u32, Lit)>`, storing the other watched literal as a blocker. The blocker check in `propagate_lit` skips satisfied clauses before accessing clause memory. Benchmark n=22: `19.7s → 15.5s` (**-21.3%**). **Implemented.**

- **Learnt clause minimization** *(from Claude, idea 1)*: Added recursive minimization (MiniSat-style) after 1-UIP analysis. Removes literals whose reason chains are entirely covered by the learnt clause. Initially regressed +5% on the original baseline, but after the blocker literal optimization made propagation cheaper, the balance shifted. Benchmark n=22: `15.5s → 14.7s` (**-5.1%**). **Implemented.**

- **CaDiCaL backend** *(from Claude, idea 7)*: Added `SatSolver` trait abstracting over radical and CaDiCaL. Compile with `--features cadical` to use CaDiCaL. Benchmark n=22: CaDiCaL `11.8s` vs radical `14.7s`. CaDiCaL is ~20% faster, likely due to BVE preprocessing. **Implemented.**

### Tried from Claude SAT ideas (rejected)

- **EMA-based restarts** *(from Claude, idea 2)*: Replaced Luby restarts with glucose-style EMA tracking (fast α=1/32, slow α=1/4096, margin=1.25, blocking by trail size). First attempt on original baseline: `21.1s → 21.6s` (+2.3% regression). Second attempt after blocker+minimization: `14.7s → 25.8s` (**+75% regression**). The EMA strategy restarts too aggressively for these instances, undoing productive search. Luby's geometric backoff is a better fit. **Reverted.**

- **Failed literal probing** *(from Claude, idea 3)*: Probed up to 500 most-active unassigned variables before each solve. Negligible impact: `21.1s → 21.2s` (+0.6%, within noise). The cardinality-encoded instances don't have cheap implications to discover via unit propagation alone. May help at larger n with more complex implication graphs. **Reverted.**

- **On-the-fly self-subsumption** *(from Claude, idea 4)*: During conflict analysis, checked if all non-resolvent literals of the reason clause were already `seen`, and if so, strengthened the reason clause by removing the resolved literal. Caused correctness issues (4 test failures on first attempt, 1 on second) due to watch list invariant corruption when strengthening clauses mid-analysis. CaDiCaL handles this via lazy/deferred strengthening. **Reverted.**

### Combined results summary (n=22 hybrid search)

| Configuration | Mean time | Delta vs baseline |
|---|---|---|
| Original (clone-based radical, Luby) | 21.3s | — |
| + Assumptions-based solving | 19.7s | -7.5% |
| + Blocker literal optimization | 15.5s | -27.2% |
| + Learnt clause minimization | **14.7s** | **-31.0%** |
| CaDiCaL backend (for reference) | 11.8s | -44.6% |
| + Native PB constraints (replace totalizers) | ~14.7s | neutral (fewer vars/clauses, same speed) |

### Tried: Native XNOR propagation (CryptoMiniSat-style)

- **Native XNOR constraints** *(from Claude)*: Replaced the 4-clause XNOR encoding (`aux ↔ (a ↔ b)`) with a native `XnorConstraint` struct that propagates directly. When 2 of the 3 variables are assigned, the third is forced. Watched via per-variable index (static, no updates needed). Benchmark n=22: `12.9s → 17.5s` (**+35% regression**). The 2WL clause encoding with blocker literals is more efficient because the blocker short-circuits most checks without accessing clause memory. The native XNOR adds a second propagation pass on a separate data structure for every enqueued literal. **Reverted.**

- **CryptoMiniSat-style Gauss-Jordan elimination** *(idea)*: The XNOR constraints form a system of XOR equations (`aux ⊕ a ⊕ b = 0`). GJ elimination could discover implied variable equalities and reduce the constraint count. However, the XNOR aux variables appear in PB cardinality constraints (agree counts), not directly in clauses, so eliminating them requires rewriting PBs — a non-trivial transformation. The agree count `sum(x_i XNOR x_{i+s})` is quadratic in the original variables, so direct elimination without aux vars isn't possible in the PB framework. **Not implemented.**

## CaDiCaL vs radical feature comparison

| Feature | CaDiCaL | radical |
|---|---|---|
| **Core CDCL** | | |
| Two-watched-literal BCP | ✅ | ✅ |
| Blocker literals in watch lists | ✅ | ✅ |
| 1-UIP conflict analysis | ✅ | ✅ |
| Non-chronological backjumping | ✅ | ✅ |
| VSIDS with activity decay | ✅ | ✅ |
| Phase saving | ✅ | ✅ |
| Learnt clause minimization | ✅ | ✅ |
| LBD-based clause deletion | ✅ | ✅ |
| **Restarts** | | |
| Luby restarts | ✅ | ✅ |
| EMA-based (glucose-style) restarts | ✅ | ❌ (tested, +75% regression) |
| Rephasing / target phases | ✅ | ❌ |
| Stabilization mode | ✅ | ❌ |
| **Preprocessing / Inprocessing** | | |
| Bounded Variable Elimination (BVE) | ✅ | ❌ |
| Subsumption / self-subsumption | ✅ | ❌ |
| Failed literal probing | ✅ | ❌ (tested, neutral) |
| Vivification | ✅ | ❌ |
| Equivalent literal substitution | ✅ | ❌ |
| **Clause management** | | |
| Flat clause storage | ✅ | ✅ |
| Tier-based retention (glue ≤ 2/6) | ✅ | ❌ (glue ≤ 3 only) |
| Binary clause special-casing | ✅ | ❌ |
| Clause compaction / GC | ✅ | ❌ (soft delete only) |
| **Incremental solving** | | |
| Assumptions API | ✅ | ✅ |
| Incremental clause addition | ✅ | ✅ |
| **Extensions (radical only)** | | |
| Native PB constraints (`sum >= k`) | ❌ | ✅ |
| Solver cloning (for templates) | ❌ (C++ object) | ✅ (flat storage) |
| Pure Rust, zero C deps | ❌ | ✅ |

**Key gap**: CaDiCaL's ~20% speed advantage over radical (11.8s vs 14.7s at n=22) is likely from BVE preprocessing eliminating auxiliary variables introduced by the totalizer/XNOR encoding. With native PB constraints, radical has fewer auxiliary variables to eliminate, potentially narrowing this gap at larger n.

