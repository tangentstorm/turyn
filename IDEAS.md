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

- **Z/W-indexed boundary table** *(London §3.3, Step 1)*: Pre-enumerate all valid X/Y boundary configurations (prefix+suffix of length k) and index them by Z/W boundary bits. At runtime, given a Z/W candidate, extract its boundary bits, do a single O(1) array lookup, and get all compatible (x_bits, y_bits) pairs. The precomputation checks autocorrelation constraints for boundary-only lags (lags where all position pairs fall within the boundary). Deduplicated format: many Z/W configs share the same X/Y signature, so unique (x,y) lists are stored once with indices pointing to shared lists. For k=6: 27K distinct signatures, 4.2M unique X/Y entries, 131MB table. For k=7: table generation is feasible but table is much larger. **Implemented.**

- **Spectral budget restriction (`--max-spectral`)** *(London §5.1)*: Added `--max-spectral=M` CLI parameter. Restricts spectral pair filter to `|Z(ω)|² + |W(ω)|² ≤ M` at every frequency. Individual filtering still uses full spectral_bound. Trades completeness for dramatically reduced search space at larger n. London used M=66 for first TT(32), M=84 for first TT(40). No regression on existing benchmarks (pair filter already rejects everything at n=16). **Implemented.**

- **Early sum feasibility pruning in XY backtracker** *(London §3.3, Step 6)*: Restructured backtrack_xy to set pos first, then pre-check sum feasibility for the mirror position BEFORE the expensive set_pair(mirror) call. Also checks x and y sum bounds independently for xq and yq. Additionally fixed a latent bug where the backtracker would corrupt state when the mirror position was already assigned. Phase C benchmark (n=16, θ=100): xy_nodes `901,772 → 10,368` (**87× reduction**), runtime `1903ms → 17.5ms` (**-99.1%**). Primary exhaustive benchmark (θ=20000): neutral (Phase C not triggered). **Implemented.**

### Tried from London thesis (no improvement on current benchmarks)

- **Integer spectral storage** *(London §3.4, item 1)*: Tried storing ⌈power/2⌉ as i16 (1-2 bytes) instead of f64 (8 bytes) for spectrum values. Individual filtering still uses f64; integer storage only for pair comparisons. Exhaustive (θ=20000): `5957 → 6209ms` (**+4.2% regression**). Light (θ=256): `20.9 → 26.5ms` (**+27% regression**). The `(p/2.0).ceil() as i16` conversion in the hot FFT post-processing loop adds overhead without benefit since pair_spec_ok=0 at these benchmark sizes. Memory savings would only matter with millions of stored spectra at larger n. **Reverted.**

- **Pair-based tuple searching** *(London §3.4, item 4)*: Checked whether normalized tuples share (|z|, |w|) sums, which would allow reusing Z/W candidates across tuples. For n=16: all 4 tuples have unique (|z|, |w|) pairs. For n=22: all 10 tuples have unique (|z|, |w|) pairs. No savings possible at current benchmark sizes. **Not implemented.**

- **Optimal theta ≈ 100** *(London §3.4, item 6)*: Tested theta values 50–20000 on both exhaustive and solution-finding benchmarks. Results are configuration-dependent: theta=100 is fastest for Phase B (FFT cost scales with theta) but lets more Z/W pairs through, triggering expensive Phase C at n=16 (1622ms). theta=200+ rejects all pairs at n=16, giving 22ms. London's theta=100 is optimal for his non-FFT spectral computation; for our FFT-based approach, theta=200–256 is the sweet spot for n=16. **Configuration finding, not code change.**

### Table refinement ideas (not yet implemented)

The Z/W-indexed boundary table with deduplication is 131MB at k=6 (27K signatures, 4.2M X/Y entries). Several refinements could further shrink the table and enable larger k:

1. **Sum-tuple filtering in gen_table**: Only store (x,y) configs where the boundary sums are compatible with at least one valid sum tuple for the given n. Currently the table stores ALL autocorrelation-compatible configs regardless of sum feasibility. Since sum tuples are sparse (e.g. 192 tuples for n=26), this could cut the table size dramatically.

2. **Partial-lag autocorrelation filtering**: In addition to exact lags (all pairs in boundary), also check partial lags where most but not all pairs are in the boundary. The boundary-only portion of a partial lag constrains the allowed range for the middle portion. Filtering configs that exceed this range at gen_table time would reduce stored matches.

3. **GJ equality pre-filtering**: Some GJ equalities (e.g. x[i] = ±y[j] for boundary positions i,j) hold for ALL Z/W candidates at certain lags. Pre-filtering these in gen_table would further reduce stored configs.

4. **Sub-indexing by sum pair**: Within each Z/W bucket, sort (x,y) entries by (x_bnd_sum, y_bnd_sum). At runtime, binary-search to the sum-matching sub-range instead of scanning all entries. Cuts the per-candidate scan from ~264 to ~20-30 entries.

5. **Compressed storage**: ~~Many Z/W configs map to the same set of (x,y) pairs. Store unique (x,y) lists once.~~ **Done** — the deduplicated format already implements this (131MB for k=6, down from ~3.6GB non-deduplicated).

6. **Lazy mmap with real file-backed mapping**: For k≥8 tables (16GB+), use actual OS mmap instead of read-to-vec. Only the pages touched during a run get loaded into RAM. The OS handles paging automatically.

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

See README.md for the full CaDiCaL vs radical feature comparison matrix.

## Next optimization candidates (credit: Claude)

### 1. Quadratic PB constraints (eliminate XNOR aux vars entirely)

Eliminate all 462 XNOR auxiliary variables by extending radical with quadratic PB constraints: `sum(a_i * b_i) = target`. The agree count `agree(x_i, x_{i+s}) = x_i*x_{i+s} + ¬x_i*¬x_{i+s}` is expressed as product terms directly on primary X/Y variables.

**Implemented.** Propagation generates minimal explanation clauses on-the-fly for CDCL conflict analysis. Problem shrinks from ~506 vars / ~1850 clauses to 44 vars / 2 clauses + PB + quad PB constraints. Benchmark n=22: **~15.3s (neutral)**. The on-the-fly clause generation overhead roughly equals the saved XNOR clause cost. Two rounds of optimization (minimal explanation clauses, removing per-propagation allocations) did not change the picture.

### 2. BVE preprocessing (bounded variable elimination)

CaDiCaL's main advantage is BVE — resolving away variables that appear in few clauses before search begins. With the quadratic PB approach, there are very few clauses left (just symmetry breaking), so BVE has little to work with. **Skipped** — the quad PB approach made this less relevant.

### 3. Tier-based clause retention

CaDiCaL uses 3 tiers: glue ≤ 2 (never delete), glue ≤ 6 (delete 25%), rest (delete 50%). **Tried** with multiple configurations. Benchmark n=22: **~15.8s (+3% regression)**. The original flat glue ≤ 3 threshold was already well-tuned for these instance sizes. **Reverted.**

### 4. Expand GJ to partial agree targets (parity constraints)

For each lag s with agree target T, the parity constraint `sum(x_i XOR x_{i+s}) mod 2 = (T+k) mod 2` gives a GF(2) equation over primary variables — valid for ALL lags, not just extreme ones. Full GJ elimination on this system discovers additional variable equivalences.

**Implemented.** Benchmark n=22: **~15.4s (neutral)**. At n=22, the parity equations involve many variables each, so GJ produces few 2-variable rows after elimination. May help more at larger n with denser equation systems.

### 5. Rephasing / target phases *(from Claude)*

Periodically reset phase saving to the best-known assignment or random polarities. **Tried** with multiple configurations: every 500/1000/2000 conflicts, every 4th/8th restart, alternating best/random. Benchmark n=22: **neutral to +2% regression** across all configs. Two optimization passes (frequency tuning, save-at-restart-only). Phase saving alone is sufficient for these structured short-solve instances. **Reverted.**

### 6. Clause compaction / GC *(from Claude)*

Compact `clause_lits` after `reduce_db` by removing deleted entries and remapping indices. **Tried**: full compaction with remap of watches, trail reasons, and variable reasons. Benchmark n=22: **neutral (~15.2s)**. With the quad PB encoding, the template has almost no clauses to fragment. The clone+short-solve pattern means clause databases are fresh each invocation. **Reverted.**

### 7. Subsumption / self-subsumption *(from Claude)*

Check learnt clauses for subsumption. **Skipped**: same reasoning as compaction. The clone+short-solve pattern means clause databases are small and fresh. The O(n_clauses * clause_len) subsumption check cost would exceed any BCP savings.

### 8. BVE preprocessing *(from Claude)*

Resolve away variables appearing in few clauses. **Skipped**: with quad PB, there are only 44 primary variables and 2 permanent clauses. Explanation clauses are generated during search and discarded with the solver. No preprocessing opportunity.

### Why remaining CaDiCaL features don't help

All four features (rephasing, compaction, subsumption, BVE) address problems in **long-running solves with large clause databases**. Our usage pattern is fundamentally different: **clone template → add per-candidate PB constraints → short solve → discard**. Each solve starts fresh with a small clause database. The remaining ~25% gap to CaDiCaL is likely from CaDiCaL's optimized C++ implementation (tighter inner loops, SIMD, cache-aligned data structures) rather than missing algorithmic features.


### 9. Incremental slack tracking for quad PB *(from Claude)*

Currently `propagate_quad_pb` recomputes `sum_true` and `sum_maybe` from scratch on every call by scanning all ~80 terms. With ~21 constraints checked per variable assignment, this is O(21 * 80) = ~1680 term evaluations per assignment. Incremental tracking would store `sum_true` and `sum_maybe` per constraint and update them delta-style when a variable changes (+/- one term's coefficient). This requires careful bookkeeping during backtrack (restore old values). Expected to reduce the per-assignment cost from O(terms) to O(1) amortized.

## Performance interventions — April 2026 profile-guided round (credit: Claude)

Profiling n=26 with callgrind (tuple 8,8,2,3, 26 Z/W pairs, 78s):
- `propagate` 13%, `backtrack` 10%, `propagate_quad_pb` 8%, `compute_quad_pb_explanation` 8%
- `solve_inner` 7%, `propagate_pb` 3%, malloc/free/realloc 6%
- `clear_learnt` 0.5%, `reset_quad_pb_state` 0.6%

Phase C (SAT) dominates >90% of runtime. The 10 interventions below target allocation reduction, hot loop efficiency, and unnecessary work elimination.

### P1. Reuse `seen` and `stack` allocations in conflict analysis

`analyze()` allocates `vec![false; num_vars]` on every conflict. `lit_removable()` allocates `visited` and `stack` on every call. Move these to solver-level reusable buffers (clear between uses). At n=26 with ~44 vars and hundreds of conflicts per solve, this eliminates thousands of heap allocations. Target: reduce malloc/free from 6% by ~1-2%.

**Result (v1):** Phase C n=26: 18.99s → 18.79s (-1.1%, within noise). Reverted — not a decisive win.
**Result (v2, iterated):** Extended to cover `compute_quad_pb_explanation` (16.67% of runtime returning `Vec<Lit>`), `lit_removable`, and all conflict analysis paths. Uses `mem::take` pattern for borrow-checker-safe buffer reuse. Phase C n=26: 18.88s → 16.99s (**-10.0%**). malloc/free dropped from 8.5% to ~2%. **Accepted.**

### P2. Avoid Vec allocation for `reason_lits` in `analyze()`

`analyze()` creates a `Vec<Lit>` for `reason_lits` on every resolution step (Clause, Pb, QuadPb). For Clause reasons, this is a needless `.to_vec()` copy. Switch to iterating the clause slice directly via an enum/index approach, avoiding allocation entirely for the clause case. The QuadPb and Pb paths still need allocation but are less frequent.

**Result:** Folded into P1 — the Clause path now iterates `clause_lits[cstart..cstart+clen]` directly with index-based access, no `.to_vec()`. PB and QuadPb paths reuse `analyze_reason_buf`.

### P3. Batch `clear_learnt` — don't call after every single config

In `solve_xy_with_sat`, line 2764: `configs_tested % 1 == 0` always evaluates true, meaning `clear_learnt` is called after every single boundary config SAT solve. This is wasteful — `clear_learnt` iterates all clause metadata + all watch lists. Batch to every N configs (e.g., 64 or 128) or skip entirely and rely on `reduce_db` in the solve loop.

### P4. Skip `propagate_pb` for already-satisfied constraints

`propagate_pb` does a full scan of all literals in the constraint on every trigger. For PB constraints with large slack (many true literals), the scan is wasted work. Add a `satisfied` flag or slack cache that short-circuits when the constraint is trivially satisfied.

### P5. Eliminate `configs_tested % 1 == 0` dead code and reduce `clear_learnt` overhead

`clear_learnt()` iterates all `clause_meta` to mark learnt clauses deleted, then iterates all watch lists to retain. With incremental solving, learnt clauses from previous configs may actually help future configs. Try removing `clear_learnt` entirely from the table path — the solve loop's `reduce_db` already manages clause database size.

### P6. Pre-size `quad_pb_seen_buf` at solver construction

`compute_quad_pb_explanation` checks `quad_pb_seen_buf.len() < num_vars` and resizes on first call per solve. Move the resize to `solve_with_assumptions` entry point so it's done once per solve, not checked on every explanation computation.

**Result:** Pre-sized both `quad_pb_seen_buf` and `analyze_seen` at solve entry. Removed per-call resize checks. Phase C n=26: neutral (18.44 → 18.86s, within noise). The buffers are tiny (44 elements) so the branch-removal savings are negligible. **Accepted** as code cleanup.

### P7. Skip DEAD/TRUE terms in `propagate_quad_pb` using state field

The `propagate_quad_pb` inner loop checks `assigns[var_a]` and `assigns[var_b]` for every term to determine if it's a propagation candidate. But the precomputed `state` field (maintained by `update_quad_pb_term_hint`) already encodes whether a term is DEAD (0), MAYBE (1), or TRUE (2). Add `if t.state != 1 { continue; }` to skip non-MAYBE terms with a single byte compare instead of two memory loads + branching.

**Result:** Phase C n=26: 16.99s → 16.41s (**-3.4%**). Phase B neutral. All tests pass. **Accepted.**

### P8. Use `SmallVec` or inline storage for learnt clauses

Learnt clauses in `analyze()` and `add_learnt_clause()` use `Vec<Lit>` which heap-allocates. Most learnt clauses at n=26 are short (2-5 literals). Use `SmallVec<[Lit; 8]>` or a stack-allocated buffer to avoid heap allocation for typical clause sizes. Target: reduce malloc overhead for the analysis path.

**Result:** Superseded by P1v2 which eliminated nearly all per-conflict allocations. The learnt clause Vec is the only remaining allocation per conflict, but `analyze` now returns it and `add_learnt_clause` takes ownership — one alloc per conflict is cheap. malloc dropped from 8.5% → 0.2%. **Skipped.**

### P9. Skip quad PB propagation for constraints with large slack

In `propagate_quad_pb`, when both `slack_up` and `slack_down` are large (> max_coeff), no propagation is possible. Currently we still iterate all terms looking for propagation candidates. Add a `max_coeff` field to `QuadPbConstraint` and early-exit when both slacks exceed it.

**Result:** Already implemented! Line 904: `if slack_up > 0 && slack_down > 0 { return None; }`. Since all coefficients are 1, this is equivalent to `max_coeff <= min(slack_up, slack_down)`. The term scan only runs when one slack is exactly 0 (propagation required). No improvement possible. **Skipped.**

### P10. Avoid `HashSet::insert` allocation in `stream_zw_candidates_to_channel` dedup

The `seen` HashSet in `stream_zw_candidates_to_channel` allocates a `Vec<i32>` clone for every `zw_autocorr` on insert. Switch to a hash of the autocorrelation vector (e.g., FxHash of the raw bytes) stored in a `HashSet<u64>`, avoiding the Vec clone. This reduces Phase B allocation pressure.

**Result:** Skipped �� Phase B is <0.2% of runtime at n=26 (32ms out of 16s). The dedup HashSet handles at most ~573 entries per tuple. Not worth optimizing for the SAT-heavy benchmark. **Skipped.**

## Round 2 performance interventions — April 2026 (credit: Claude)

Re-profiled after round 1 (5 accepted changes, n=26: 869s -> 577s). New baseline: 14.0s on SAT-heavy microbenchmark.
Excluding coordinator overhead (51%), the SAT-only profile:
- `recompute_quad_pb` 12.3%, `propagate` 10.3%, `compute_quad_pb_explanation_into` 8.1%
- `solve_with_assumptions` 7.4%, `propagate_quad_pb` 3.2%, `propagate_pb` 1.8%, `backtrack` 1.4%

### R1. Fuse recompute with propagation: single-pass recompute+check

`recompute_quad_pb` (12.3%) scans all ~80 terms to rebuild sums, then `propagate_quad_pb` loads sums and often returns immediately (slack > 0). When the constraint is stale, fuse both into one pass: compute states, accumulate sums, AND check propagation in a single traversal. Saves the redundant sums load and the second function call for the majority case (no propagation needed).

### R2. Avoid redundant `recompute_quad_pb` calls by tracking stale set

Currently when any stale constraint is encountered, ALL stale constraints are recomputed (batch recompute). But the subsequent per-variable propagation loop may trigger recompute again for constraints that were already recomputed in the batch. Track a "recompute generation" to skip re-recomputing constraints that were just refreshed in this propagation round.

### R3. Skip forward `update_quad_pb_term_hint` when constraint was just recomputed

In `propagate()`, we first recompute stale constraints, then call `update_quad_pb_term_hint` for all terms involving the current variable. If a constraint was just recomputed (including the current variable's assignment), the term state is already correct -- the `update_quad_pb_term_hint` is redundant. Skip the update for constraints that were recomputed in the same propagation step.

### R4. Reduce `compute_quad_pb_explanation_into` cost by using state-based filtering

At 8.1%, the explanation function scans all ~80 terms. But terms with state DEAD have at least one false variable (the one that kills the term). If both variables were assigned before the propagated variable, the state is accurate and we can use it to skip the `trail_pos` check. For MAYBE terms with both variables Undef, they can't contribute to the explanation. Pre-filter using the term state byte before loading assigns/trail_pos.

### R5. Pre-compute `propagate_pb` slack incrementally

`propagate_pb` (1.8%) scans all ~26 literals to compute slack on every trigger. With unit coefficients, slack = count(non-false) - bound. Track `count_false` per PB constraint incrementally: increment on assign-false, decrement on backtrack. Compute slack as `n - count_false - bound` in O(1).

### R6. Move `propagate_lit` deleted-clause check after blocker check

In `propagate_lit` (10.3%), the deleted-clause check happens BEFORE the blocker check. But the blocker check (line 753) is cheaper and more likely to short-circuit (most watched clauses are satisfied). Swap the order: check blocker first, then deleted. Saves a `clause_meta[ci]` load for satisfied clauses.

### R7. Compact `quad_pb_var_terms` and `quad_pb_var_watches` into contiguous arrays

Currently `quad_pb_var_terms[v]` and `quad_pb_var_watches[v]` are `Vec<Vec<...>>` -- each variable's entry is a separate heap-allocated Vec. Replace with flat arrays + offset indices for cache-contiguous access during propagation. Eliminates pointer chasing.

### R8. Eliminate `propagate_pb` by converting sum constraints to clauses + quad PB

PB constraints encode `sum(x_i) = k`. With 44 vars and unit coefficients, the at-least-k and at-most-k constraints can be handled purely by quad PB (which already tracks cardinality via agree counts) or by exhaustive clause encoding for small sums. Eliminating the separate PB propagation pass saves 1.8%.

### R9. Avoid `std::mem::take` in `propagate_lit` by using raw pointer swap

`propagate_lit` does `std::mem::take(&mut self.watches[watch_idx])` which zeroes the Vec and later restores it. At 10.3% of runtime, even micro-overhead matters. Replace with unsafe raw pointer swap or manual index management to avoid the zeroing cost.

### R10. Reduce recompute cost by sorting terms by variable index

In `recompute_quad_pb`, the inner loop loads `assigns[var_a()]` and `assigns[var_b()]` for each term. With ~80 terms accessing ~44 variables, many accesses hit the same cache line. Sorting terms by `(var_a, var_b)` at constraint creation time maximizes sequential access patterns and reduces L1 misses.

## Ideas from CryptoMiniSat and other advanced SAT solvers (credit: Claude, April 2026)

These target the SAT solver (radical), which dominates runtime at n >= 22. Sourced from CryptoMiniSat, CaDiCaL, Kissat, Lingeling, and MapleSAT.

### CMS1. Gauss-Jordan elimination for XOR propagation (CryptoMiniSat)

CryptoMiniSat's signature feature: full GF(2) Gaussian elimination interleaved with BCP. Our XOR constraints currently only propagate when `num_unknown == 1` (unit propagation). GJ maintains an echeloned GF(2) matrix and deduces implications when multiple XORs interact — e.g., if XOR₁ and XOR₂ share variables, their sum may force a variable that neither alone could. For Turyn sequences, the autocorrelation parity constraints produce heavily overlapping XOR systems.

**Implementation plan:** In `propagate()`, after BCP, run a GJ elimination pass on the XOR constraint matrix. Maintain the matrix in row-echelon form incrementally (add/remove rows on assign/backtrack). When a row reduces to a single variable, enqueue it as a unit propagation. Expected high impact due to dense, interdependent XOR structure.

### CMS2. Vivification / clause strengthening (CaDiCaL / Kissat)

Take an existing clause, tentatively assume each literal is false in order, and propagate. If a conflict arises before exhausting the clause, the clause can be shortened. Unlike self-subsumption (tried, had correctness issues with watch invariants), vivification works on a temporary propagation that gets fully undone — no watch list corruption risk. Apply periodically to learnt clauses during restarts.

**Implementation plan:** After each restart, pick the top N learnt clauses by LBD. For each clause, save trail state, assume negations of literals left-to-right, propagate. If conflict at literal k, shorten clause to first k literals. Restore trail. Our glue clauses (LBD ≤ 3) are kept forever — vivifying them to be tighter compounds their value.

### CMS3. Equivalent literal substitution via SCC (Lingeling / CryptoMiniSat)

Build the binary implication graph from 2-literal clauses and implications derived from PB/XOR constraints. Run Tarjan's SCC to find equivalent literal pairs (if `a → b` and `b → a`, they're equivalent). Replace one with the other throughout the formula. Shrinks variable count and simplifies all constraints.

**Implementation plan:** At solver construction (or periodically), extract binary implications from watch lists and XOR/PB constraints. Run Tarjan SCC. For each equivalence class, pick a representative and substitute throughout all clause, PB, and quad PB data structures. The autocorrelation structure likely creates equivalences, especially in the XOR system.

### CMS4. Bounded variable elimination (BVE) as inprocessing (MiniSat / CaDiCaL)

Resolve out variables that don't increase clause count: for variable x, compute all resolvents of clauses containing x with clauses containing ¬x. If the resolvent set is no larger than the original, eliminate x. Apply during preprocessing and periodically during search.

**Implementation plan:** Before first `solve()`, scan for variables appearing in few clauses. For each candidate, compute resolvents. If resolvent count ≤ original clause count, apply elimination: remove old clauses, add resolvents, mark variable as eliminated. Especially effective for auxiliary variables from sequential counter / totalizer encodings. Note: with quad PB encoding we have very few clauses, so focus on any remaining CNF clauses (symmetry breaking, learnt).

### CMS5. Warm-start learnt clause and phase transfer across SAT calls

We solve many SAT instances across different Z/W pairs, each time starting mostly fresh. Keep a pool of high-quality learnt clauses (low LBD) and saved phases from previous solves, and seed new instances with them. The structural similarity between Z/W pairs means clauses about X/Y variable interactions are highly reusable.

**Implementation plan:** After each `solve_with_assumptions()` call, extract learnt clauses with LBD ≤ 2 that don't mention assumption variables. Store in a shared pool (cap at ~100 clauses). Before the next solve, inject pool clauses into the solver. Also save the phase vector from SAT results and use as initial phase for the next call. More aggressive than current assumptions-based incremental solving — transfers learned knowledge across structurally similar instances.

### CMS6. Local search integration / phase advising (CryptoMiniSat 5.x / Kissat)

Use our existing simulated annealing engine as a phase advisor: when the CDCL solver restarts, run a short burst of local search (a few thousand flips) on the current partial assignment to find a good assignment, then import that as the saved phase vector. Combines completeness of CDCL with local search's ability to find good regions quickly.

**Implementation plan:** On every Nth restart (e.g., every 4th), extract current partial assignment as a starting point for SA. Run ~5000 flips targeting the X/Y autocorrelation defect. Import the resulting assignment as the phase[] vector. The SA engine already achieves 41M flips/sec, so 5000 flips costs ~0.1ms. Key question: whether the SA-guided phases actually lead to better CDCL decisions or just add overhead.

### CMS7. Lucky phases (Kissat)

Before starting the main CDCL search, try a handful of "lucky" complete assignments: all-positive, all-negative, Jeroslow-Wang heuristic, and a few random ones. Just propagate each to completion — if any yields a solution or gets very far, win cheaply. For Turyn sequences, add domain-specific lucky phases: phases from previously found solutions at nearby n.

**Implementation plan:** Before the main `solve_inner()` loop, try 4-8 candidate phase vectors. For each: set all variables according to the phase, propagate, check if consistent. If a conflict arises, record the depth reached. If any reaches a solution, return immediately. Cost: ~8 propagation passes, essentially free per SAT call. Over thousands of SAT calls, catching even 1-2% trivially saves meaningful time.

### CMS8. Chronological backtracking (CaDiCaL / MapleSAT)

Our solver always does non-chronological backjumping. The 2018 insight (Nadel & Ryvchin) is that sometimes backtracking just one level (chronological) is better — it avoids re-deriving implications already on the trail. Heuristic: if the backjump level is "close" to the current level (within some threshold), backtrack chronologically instead.

**Implementation plan:** In `analyze()`, after computing the backjump level, check `current_level - backjump_level < threshold` (e.g., threshold=3). If so, backtrack to `current_level - 1` instead. Requires handling "re-propagated" literals (literals on the trail above the backjump level that are still valid). The mix of PB/QuadPB/XOR constraints likely creates many shallow conflicts where this helps.

### CMS9. Clause distillation / inprocessing simplification (Lingeling / CaDiCaL)

Periodically during search (e.g., every N restarts), pause and run a simplification pass: subsumption (remove clauses subsumed by others), self-subsuming resolution (strengthen clauses), and strengthening via unit propagation. Different from vivification — focuses on inter-clause relationships.

**Implementation plan:** Every 100 restarts, at decision level 0: (1) sort all clauses by length, (2) for each clause, check if any shorter clause subsumes it (mark subsumed for deletion), (3) for pairs differing by one literal, check if self-subsuming resolution applies (strengthen the longer clause). With our clone+short-solve pattern, focus on the template's original clauses, not per-solve learnt clauses.

### CMS10. Community-structure-aware branching (CryptoMiniSat / ModularSAT)

Partition variables into "communities" based on clause co-occurrence. Bias branching to fully assign one community before moving to another. For Turyn sequences, the natural communities are X variables, Y variables, and lag groups (all variables involved in autocorrelation at lag k).

**Implementation plan:** At solver construction, compute variable co-occurrence from quad PB constraints. Assign each variable to a community (X-sequence vs Y-sequence, or by lag interaction density). Add a community-awareness bonus to VSIDS: when picking the next decision variable, prefer variables in the same community as the most recent decision. This focuses the search and produces lower-LBD learnt clauses.
