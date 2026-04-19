# IDEAS

## How to read this file

Every idea below is annotated, where possible, against the project's headline
metric: **Time to Cover (TTC)** — the wall-clock time a run would need to
fully cover the search space, given the current pruning and per-boundary
work rate.

TTC is computed in `src/main.rs`:

- **MDD modes (`--wz=apart|together`)**: `ttc = (live_zw_paths - eff) / (eff/elapsed)`
  where `live_zw_paths = count_zw(mdd.root)` (live paths through the MDD)
  and `eff = effective_coverage_metric(walked, xy_sat, xy_unsat, xy_timeout,
  xy_timeout_cov_micro)`. Each boundary completed contributes 1.0; XY
  timeouts contribute a fractional `log2(decisions+1)/free_vars` via
  `xy_cover_micro`. See `effective_coverage_metric` at `src/main.rs:4210`.
- **Cross mode (`--wz=cross`)**: `ttc = (est_total_xy - xy_done_eff) /
  (xy_done_eff/elapsed)` where `est_total_xy` is extrapolated from tuple
  progress via `cross_estimated_total_xy` at `src/main.rs:4185`.

So any optimization changes TTC through one or more of three levers:

1. **Denominator (total work)**: shrink `live_zw_paths` (tighter MDD
   pruning, larger `k`, stricter spectral filters at boundary-gen time) or
   `est_total_xy` (fewer tuples enumerated, smaller sum-tuple set).
2. **Rate (eff done per second)**: make each stage (MDD walk, SolveW,
   SolveZ, SolveXY) cheaper, add more pruning upstream of SAT, or raise
   worker utilization.
3. **Shortfall (timeouts)**: reduce XY SAT timeouts so each walked
   boundary contributes a full 1.0 to `eff` instead of a fraction. Watched
   via `flow_xy_timeout` and the per-stage pruning block
   (`print_stage_pruning_block`, `src/main.rs:4229`).

Per-stage instrumentation (all atomics in `run_mdd_sat_search`):

- `stage_exit[0..3]` — boundaries/W/Z/XY items completed (lines 2740, 3733)
- `flow_{w,z,xy}_{decisions,propagations,root_forced,free_sum,solves}`
  — SAT pruning stats captured by diffing `Solver::num_decisions` /
  `num_propagations` around each solve (lines 2717-2733)
- `flow_xy_{sat,unsat,timeout,timeout_cov_micro}` — XY outcomes
- `extensions_pruned` — XY candidates rejected by `has_extension`
- `flow_{z,w}_{spec_pass,spec_fail,pair_fail,prep_fail}` — spectral/GJ
  funnel counters shown in the final "Pipeline Flow" block

When an idea below says "detect via X", X is one of these counters.

## Implemented experiments (measured)

- **SIMD in autocorr and spectrum** *(from Grok)*: Tried a SIMD-friendly
  step (manual loop unrolling in autocorrelation and XY verification hot
  loops). Benchmark `--n=16 --theta=256`: 101→97 ms (~3.7% faster).
  - **TTC mechanism**: rate (faster autocorr in the legacy hybrid path).
  - **Detection**: `benchmark --n=16 --theta=256` mean/median; would
    show up in MDD mode as higher `stage_exit[0..3]`/s.
  - **Status**: the kept version is manual 4x unrolling in the autocorr
    inner loop used by `autocorrs_from_values` and `spectrum_if_ok`
    (src/main.rs). Still present, but the hot path in the current
    pipeline is the SAT solver, not autocorr, so TTC impact is now
    negligible.
- **XY backtracker dynamic variable ordering** *(from Grok)*: Pick next
  unassigned position with the most interactions with already-assigned
  variables. Benchmark: 103→88 ms (~14.8% faster).
  - **TTC mechanism**: rate — fewer SAT decisions per candidate, so
    `flow_xy_decisions/flow_xy_solves` drops.
  - **Status**: the XY backtracker it targeted was removed when the
    MDD+SAT pipeline replaced the legacy `run_hybrid_search`
    backtracker. Obsolete.
- **Bucket cap during Z/W generation** *(from Grok)*: cap
  `HashMap<BoundarySignature, Vec<…>>` retention per signature.
  Benchmark: 88→72 ms (~17.5% faster).
  - **TTC mechanism**: rate — lower memory pressure in legacy Phase B.
  - **Status**: legacy hybrid Phase B still uses `push_capped` logic in
    `stream_zw_candidates` (src/main.rs). Marginal TTC impact at n≥22
    where SAT dominates.

## Tried (no meaningful impact yet)

- **FFT for spectrum** *(from Grok)*: First attempt — in-tree FFT path for
  power-of-two grids with manual trig fallback — regressed 10.7% due to
  branch overhead even when inactive.
  - **Revisited (2026-03-30)**: replaced the manual DFT with `rustfft`
    (and later `realfft` for real input, commit dd7642f). FFT size =
    max(4n, 2θ) rounded to a power of 2, reusable buffer. n=14 θ=128:
    11.09→5.70 ms (**-48.6%**); n=16 θ=256: 38.25→20.20 ms (**-47.2%**).
  - **TTC mechanism**: rate — the post-hoc pair check and SolveW
    spectral filter are both O(θ) × O(seq_len) per W/Z; FFT makes
    them O(M log M).
  - **Detection**: higher effective bnd/s (`stage_exit[0]/elapsed`)
    and higher `flow_w_spec_pass/flow_z_spec_pass` per unit time.
    Also visible in the "Pipeline Flow" funnel.
  - **Status**: implemented via `SpectralFilter` (src/main.rs:389)
    using `realfft`; `compute_spectrum_into` is called post-hoc after
    every Z SAT and the SolveW brute-force path. Active everywhere in
    the current pipeline.
- **Better Z/W generation** *(from Grok)*: Tighter global DFS bounds +
  parity pruning in `generate_sequences_with_sum_visit`. Benchmark:
  97→103 ms (regression).
  - **TTC mechanism**: would affect rate if it helped — but the extra
    branches cost more than the pruning saves on this profile.
  - **Status**: not merged. `generate_sequences_with_sum_visit`
    (src/main.rs:627) still uses simple tail-sum feasibility pruning.

## Ideas from Gemini (credit: Gemini for every item below)

- **Incremental Spectral Pruning in XY backtracker** *(from Gemini)*:
  Track running DFT sums in XYState; prune if `|DFT_X_partial|² +
  |DFT_Y_partial|² > budget_k + ε` at any frequency.
  - **TTC mechanism**: rate and shortfall — would prune XY candidates
    before full SAT/backtrack, so `flow_xy_decisions/flow_xy_solves`
    and `flow_xy_timeout` both go down.
  - **Tried (2026-03-30)**: regressed +11-15% on the old backtracker;
    `xy_nodes=0` on standard benchmarks so overhead-only.
  - **Status now**: the old XY backtracker is gone. The equivalent in
    the current pipeline is `radical::SpectralConstraint` (radical/src
    /lib.rs:218) inside the Z SAT solver — that *is* implemented and
    wired via `z_solver.attach_spectral_constraint` at
    src/main.rs:3400ish. Its TTC impact is visible as reduced
    `flow_z_propagations` per decision. Re-doing the same trick inside
    the XY SAT solver is still an open idea; see "SpectralConstraint
    for XY" below.

- **SIMD-Accelerated Autocorrelation** *(from Gemini)*: explicit SIMD
  multiply-and-add via `std::simd` or `wide`.
  - **TTC mechanism**: rate.
  - **Tried (2026-03-30)**: branchless multiply regressed 5.4% on
    heavy spectral profile (branch predictor already handles ±1
    well). Stable Rust lacks `std::simd`.
  - **Status**: not merged. The FFT-based `spectrum_if_ok` path and
    the Z SAT `SpectralConstraint` already use cache-friendly float
    arithmetic via `rustfft`/`realfft`. TTC-wise, post-FFT transition
    to SIMD here is low-leverage; the SAT solver dominates at the
    sizes where TTC matters (n≥22).

- **Douglas-Rachford (DR) Projection Heuristic** *(from Gemini)*: Run
  DR iterations before XY SAT to reject hopeless (Z,W) pairs.
  - **TTC mechanism**: shortfall + rate — pre-filters (Z,W) before
    cloning the solver, so `flow_xy_timeout` would drop.
  - **Skipped (2026-03-30)**: needs FFT (now available) but in all
    tested profiles `pair_spec_ok=0` so would never execute.
  - **Status now**: the post-hoc `spectral_pair_ok` check
    (src/main.rs:590) and the SAT `SpectralConstraint` already reject
    ~99.996% of Z solutions at small k — the pipeline is not (Z,W)-
    quality-limited anymore, it is SAT-solve-limited. Retrying DR as
    an XY-quality pre-filter is possible but the payoff depends on
    actual XY-timeout rates (`flow_xy_timeout/flow_xy_solves`).

- **Symmetry Breaking (X palindromic, Y skew-symmetric)** *(from Gemini)*.
  - **TTC mechanism**: denominator — would shrink the live XY search
    space by ~2^n.
  - **Rejected (2026-03-30)**: known TT(6) solution is not palindromic
    / skew-symmetric, so this would miss valid solutions. Result
    applies to continuous ±1 relaxations, not discrete ones.
  - **Status**: do not revive as-is. A weaker, measured symmetry
    reduction would need TT(n) normalization rules (x[0]=+1,
    time-reversal/complementation) — these are already exploited in
    `phase_a_tuples` sum canonicalization (src/main.rs:464).

## Why backtracking (Phase C) is never triggered on standard benchmarks

*(Historical note: all three `--wz` modes now funnel into
`SolveXyPerCandidate::try_candidate` SAT instead of the legacy
backtracker. What follows is preserved for context; the analysis of
where pairs die still applies — it just happens inside SAT now.)*


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

- **CaDiCaL SAT solver integration** *(from Grok, "SAT/CP hybrids")*:
  `--sat` mode using `cadical` v1.9.5 via optional feature flag.
  Encodes TT(n) with XNOR agree aux vars, sequential counters (Sinz
  2005), and selector-based weighted cardinality. TT(4)–TT(18) all
  found; TT(18) in 89s vs SA 580s (**6.5× faster**).
  - **TTC mechanism**: rate (faster SAT) + denominator (CaDiCaL's BVE
    preprocessing proves UNSAT earlier without walking the full
    tree).
  - **Status**: present behind `--features cadical`
    (Cargo.toml:11,17). Current default is the in-tree `radical`
    solver because the live pipeline needs the custom quad-PB and
    spectral constraints that CaDiCaL does not implement. CaDiCaL is
    used only for the standalone `--sat` top-level encoding, not
    per-(Z,W) XY solves, so it doesn't currently feed into TTC.

### Tried from Grok SAT/CP ideas

- **Z-aware per-frequency W spectral tightening** *(from Grok)*:
  use `spectral_bound - min_z_power[k]` when filtering W.
  - **TTC mechanism**: denominator (fewer W candidates reach
    SolveZ, so `stage_enter[1]` and all downstream counters shrink
    proportionally).
  - **Measurement**: θ=256 reduced w_spec_ok by 7.1%; θ=20000 zero
    effect; 3.8% wall-clock regression overall.
  - **Status**: reverted. Not currently in the code. For MDD modes
    the equivalent per-frequency Z-conditioned bound is now
    computed *inside* the Z SAT solver via `SpectralConstraint::
    per_freq_bound` (set from `pair_bound - |Ŵ(ω_fi)|²`); see
    `src/sat_z_middle.rs`. That's effectively the same trick,
    applied after W is fixed.

*(All four SA items below affect the `--stochastic` mode only. SA
is not part of the TTC pipeline: it doesn't walk MDD boundaries and
doesn't emit stage_exit events. TTC is undefined for SA runs. Kept
here for completeness; tracked in flips/sec.)*

- **Greedy repair near solution** *(from Grok)*: steepest-descent
  pair swaps when defect <4n. 6.1% regression; stuck at n≥18.
  Reverted.
- **Simplified delta-corr computation** *(from Grok)*: SA inner loop
  refactor, `32.03M → 34.13M flips/sec` (+6.6%). **Kept** in
  `stochastic_worker` (src/main.rs:1733).
- **Pre-grouped value indices for O(1) SA partner selection** *(from
  Grok)*: `34.13M → 41.65M flips/sec` (+22.0%). **Kept**.
- **Lag-targeted SA move selection** *(from Grok)*: 7.8% regression.
  Reverted.
- **Legendre/QR seeding** *(from Grok)*: 7.3% regression. Reverted.

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

- **Z/W-indexed boundary table → replaced by MDD** *(London §3.3
  Step 1)*: pre-enumerate valid (x,y) boundary configs per (z,w).
  - **TTC mechanism**: denominator (the MDD's `count_live_paths()`
    counts exactly the post-boundary-filter live space; this was a
    flat-table version of the same idea).
  - **Status**: the XYBoundaryTable flat table was deleted in
    commit 7b1ec5e once `table_vs_mdd_same_k_agree` confirmed the
    MDD walker returns the identical candidate set. The MDD (1 MB)
    replaces a 1.9 GB flat table. `Mdd4` in
    `src/mdd_zw_first.rs`; loaded by `load_best_mdd`
    (src/mdd_zw_first.rs). Feeds TTC as the denominator via
    `live_zw_paths` (src/main.rs:2503).

- **Spectral budget restriction (`--max-spectral`)** *(London §5.1)*:
  `|Z(ω)|² + |W(ω)|² ≤ M` with M < spectral_bound.
  - **TTC mechanism**: denominator — shrinks the live (Z,W) space
    by rejecting spectrally "loose" candidates. Trades completeness
    for TTC. London used M=66 for first TT(32), M=84 for first
    TT(40).
  - **Detection**: final "Pipeline Flow" block would show higher
    `z_pair_fail` / lower `z_xy` counts.
  - **Status**: implemented; `--max-spectral=M` flag, consumed by
    `PhaseBContext::pair_bound` (src/main.rs:2547). Not instrumented
    as a separate TTC lever, but lowers `live_zw_paths` → `eff`
    arrival rate effectively when set.

- **Early sum feasibility pruning in XY backtracker** *(London §3.3
  Step 6)*: pre-check mirror sum bounds before `set_pair(mirror)`.
  - **TTC mechanism**: rate (prunes infeasible XY states).
  - **Measured**: 1903 ms → 17.5 ms (−99.1%) on the old backtracker
    Phase C benchmark.
  - **Status now**: the old backtracker is gone. The analogous
    early-prune in the current pipeline is inside
    `SolveXyPerCandidate::try_candidate` where the GJ equalities
    and partial-lag `lag_filters` reject bad (x,y) before the SAT
    clone. Reflected in `flow_xy_root_forced / flow_xy_free_sum`
    (higher forced = more pre-filtering).

### Tried from London thesis (no improvement on current benchmarks)

- **Integer spectral storage** *(London §3.4, item 1)*: i16 instead
  of f64 for pair comparisons.
  - **TTC mechanism**: rate (cache density).
  - **Measured**: +4-27% regression at n=16 benchmarks. Modern FPU
    already wins; bucket reduction would only matter for millions
    of stored spectra.
  - **Status**: reverted. Not in code.

- **Pair-based tuple searching** *(London §3.4, item 4)*: share
  Z/W candidates across tuples with matching (|z|,|w|).
  - **TTC mechanism**: rate (amortize Z/W generation) and
    denominator-ish (fewer unique candidates).
  - **Measured**: all normalized tuples have unique (|z|,|w|) at
    n=16 and n=22, so no savings. Unchecked at n≥26. Worth
    re-auditing: `phase_a_tuples` count grows with n, and the
    cross-mode `cross_w_cache` (src/main.rs:3653) already caches
    w_candidates per `tuple.w` sum — a partial implementation.
  - **Status**: partial (cross mode caches by w-sum only).

- **Optimal theta ≈ 100** *(London §3.4, item 6)*.
  - **TTC mechanism**: rate (lower θ = cheaper FFT) vs. denominator
    (higher θ = tighter pair bounds = more rejections before XY).
  - **Status**: with `realfft`, θ=256 chosen as the sweet spot for
    n=16 exhaustive, but the SAT pipeline uses `SPECTRAL_FREQS =
    167` (src/main.rs:9) at the SAT's integer grid and θ=256 at
    the post-hoc FFT grid. Not a simple "pick one θ"; see
    "Spectral grid sweep" open idea below.

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

The Phase C SAT solver (radical) is the bottleneck at n≥22, consuming
≥95% of compute. Every technique here directly attacks TTC's *rate*
lever: faster SAT → higher `stage_exit[3]/elapsed` → higher effective
bnd/s. Many also attack shortfall by reducing `flow_xy_timeout`.

1. **Learnt clause minimization** *(from Claude)*: After 1-UIP conflict analysis, recursively remove redundant literals from the learnt clause. A literal is redundant if its reason clause is entirely subsumed by other literals already in the learnt clause (or at decision level 0). CaDiCaL's `minimize` pass typically shrinks learnt clauses 20-30%, improving propagation efficiency and reducing clause database bloat.

2. **EMA-based restarts** *(from Claude)*: Replace the fixed Luby restart schedule with glucose-style EMA (exponential moving average) tracking of recent vs. global LBD quality. Restart when recent LBD average exceeds global average by a margin. More adaptive than Luby — restarts aggressively when the solver is exploring unproductive regions, and holds steady when making progress.

3. **Failed literal probing** *(from Claude)*: At the start of solving (or periodically), probe each unassigned literal: assume it true, propagate, and if a conflict arises, the literal must be false. Also detects equivalent/implied literals. Particularly effective on structured/combinatorial instances with many binary implications, like the cardinality encodings used here.

4. **On-the-fly self-subsumption** *(from Claude)*: During conflict analysis, when resolving with a reason clause, check if the resolvent subsumes the reason clause. If so, strengthen the reason clause by removing the resolved literal. This is essentially free (check during existing analysis loop) and produces stronger propagation in future conflicts.

5. **Blocker literal in watch lists** *(from Claude)*: Store a "blocker" literal (the other watched literal) alongside each clause index in watch lists. Before accessing clause memory during BCP, check if the blocker is already true — if so, skip entirely. Avoids cache-miss-heavy clause access for satisfied clauses.

6. **Assumptions-based incremental solving** *(from Claude)*: Instead of cloning the solver template for each Z/W pair, use `solve_with_assumptions()` to pass per-pair cardinality targets as temporary assumptions. Avoids clone overhead and lets learnt clauses persist across candidates.

7. **CaDiCaL backend via feature flag** *(from Claude)*: Optional `--features cadical` compile-time flag that swaps radical for CaDiCaL (v1.9.5). Useful as a performance reference and for larger instances where CaDiCaL's preprocessing (BVE, subsumption, probing) pays off.

### Implemented from Claude SAT ideas

Each of these was measured against a stand-alone SAT microbench, not
against TTC directly. All four live in `radical/src/lib.rs` and
feed TTC through the `flow_xy_*` counters today.

- **Assumptions-based incremental solving** *(from Claude, idea 6)*:
  `solve_with_assumptions()` persists learnt clauses across Z/W pairs.
  n=22: 21.3s → 19.7s (**−7.5%**).
  - **Status**: `Solver::solve_with_assumptions` at
    `radical/src/lib.rs:1300`. Used by `SolveXyPerCandidate::
    try_candidate` inside the MDD pipeline.
  - **TTC feed**: higher `flow_xy_propagations / flow_xy_decisions`
    ratio (learnt clauses help propagation catch more).

- **Blocker literal in watch lists** *(from Claude, idea 5)*:
  `watches: Vec<Vec<(u32, Lit)>>` (radical/src/lib.rs:612). Blocker
  check short-circuits satisfied clauses. n=22: 19.7s → 15.5s
  (**−21.3%**).

- **Learnt clause minimization** *(from Claude, idea 1)*: MiniSat-style
  recursive minimization in `minimize_learnt`
  (radical/src/lib.rs:3113). n=22: 15.5s → 14.7s (**−5.1%**).

- **CaDiCaL backend** *(from Claude, idea 7)*: `--features cadical`,
  behind a `SatSolver` trait abstraction. n=22: CaDiCaL 11.8s vs.
  radical 14.7s.
  - **Status**: the CaDiCaL path is still wired via `cadical` crate
    but is *not* plugged into the MDD pipeline's per-candidate XY
    solving (which uses radical's custom constraints: MDD, quad PB,
    spectral). Only the top-level `--sat` encoding goes through
    CaDiCaL today. Keeping it compiled costs nothing; retiring
    would simplify.

### Tried from Claude SAT ideas (rejected)

- **EMA-based restarts**: reverted (+75% regression after blocker+
  minimization; aggressive restarts undo productive search).
  - **Status**: code path exists behind `config.ema_restarts`
    (radical/src/lib.rs:563), default `false`, flag `--ema-restarts`.
    TTC impact untested on current pipeline.
- **Failed literal probing**: +0.6% noise at the time.
  - **Status**: code path exists behind `config.probing` (line 564),
    default `false`, flag `--probing`.
- **On-the-fly self-subsumption**: correctness bugs, reverted.
  - **Status**: not in code.

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

- **Native XNOR constraints**: +35% regression; 2WL+blocker
  already cheap. Reverted.
- **CryptoMiniSat-style Gauss-Jordan on XNORs**: the quadratic
  structure defeats direct elimination. Not implemented.
  - **However**: a different GF(2) parity track *is* wired via
    `add_xor` / `XorConstraint` + `preprocess_scc_equivalences`
    (radical/src/lib.rs:1036, 1523). XOR propagation had a
    soundness bug in Feb 2026 (commits d337131 → 2ad1bb5 →
    f0dc681) and is currently default-*enabled* via
    `config.xor_propagation: true` (line 584) but can be disabled
    with `--no-xor`. TTC feed: XOR propagation reduces
    `flow_xy_decisions` per solve.

See README.md for the full CaDiCaL vs. radical feature comparison
matrix.

## Next optimization candidates (credit: Claude)

### 1. Quadratic PB constraints (eliminate XNOR aux vars entirely)

Express agree counts `agree(x_i, x_{i+s}) = x_i*x_{i+s} + ¬x_i*¬x_{i+s}`
directly on primary X/Y via `add_quad_pb_eq/range`.

- **TTC mechanism**: rate — radically shrinks per-candidate solver
  build cost (44 vars / 2 clauses vs 506/1850) and speeds up clone;
  also shrinks cache footprint during propagation.
- **Status**: **Implemented.** `QuadPbConstraint` at
  `radical/src/lib.rs:182`; `add_quad_pb_eq` line 912;
  `add_quad_pb_range` line 971; `propagate_quad_pb` line 2798;
  `recompute_quad_pb` line 2769. Used by the Z SAT builder
  (`src/sat_z_middle.rs`) and the XY SAT template
  (`SatXYTemplate::build`, src/main.rs:1438ish).
- **Benchmark n=22**: ~15.3s (neutral vs totalizer at that size).
- **TTC benchmark n=56**: 140 → 797 solves/s with `--quad-pb` as
  default (**+470%**; logged in OPTIMIZATION_LOG.md round 2).

### 2. BVE preprocessing (bounded variable elimination)

- **TTC mechanism**: rate — BVE would shrink clause DB for all
  solves.
- **Skipped** — quad PB leaves only 44 primary vars / 2 clauses.
  Nothing for BVE to eliminate.

### 3. Tier-based clause retention

- Tried CaDiCaL's 3-tier scheme; +3% regression at n=22. Flat glue≤3
  already tuned for short-solve + clone pattern. **Reverted.**

### 4. Expand GJ to partial agree targets (parity constraints)

- **TTC mechanism**: rate (extra unit propagations from GF(2)
  equivalences).
- **Implemented** via `add_xor`/`XorConstraint`/`preprocess_scc_
  equivalences` (radical/src/lib.rs:1036, 1523). n=22 neutral.
  Expected to help more at larger n; current TTC feed would show up
  as higher `flow_xy_root_forced` and fewer decisions per solve.

### 5. Rephasing / target phases

- **TTC mechanism**: shortfall — better phase saving might reduce
  timeouts on hard XY instances.
- **Tried**: neutral to +2% at n=22 across configs. **Reverted** —
  but the `config.rephasing` flag is still present
  (radical/src/lib.rs:567) behind `--rephasing`.

### 6-8. Clause compaction / subsumption / BVE

- All rejected for the same reason: clone-template + short-solve +
  discard means clause DBs are already small and fresh.
- **TTC pattern**: these all address *long-running* SAT; the
  Turyn pipeline is *millions of short solves*. The opportunity
  isn't inside one solve — it's in amortizing shared structure
  across solves. See "Assumptions-based incremental solving" and
  "XY dedup by zw_autocorr" for the ideas that did hit TTC.

### 9. Incremental slack tracking for quad PB

- **TTC mechanism**: rate (cuts per-assignment cost from O(terms) to
  O(1) amortized).
- **Status**: partially implemented via the "stale flag" +
  `recompute_quad_pb` pattern (radical/src/lib.rs:2769). Full
  delta-style tracking on every assign is not in the code. Profile
  n=56 `--quad-pb` shows `recompute_quad_pb` at 4.4% of runtime
  (post-round-2), so expected gain ~1-2% of solver time → ~1% of
  TTC rate. Low priority.

## Performance interventions — April 2026 profile-guided round (credit: Claude)

Profiling n=26 with callgrind (tuple 8,8,2,3, 26 Z/W pairs, 78s):
- `propagate` 13%, `backtrack` 10%, `propagate_quad_pb` 8%, `compute_quad_pb_explanation` 8%
- `solve_inner` 7%, `propagate_pb` 3%, malloc/free/realloc 6%
- `clear_learnt` 0.5%, `reset_quad_pb_state` 0.6%

SAT dominates >90% of runtime. These 10 items all target the TTC *rate*
lever via the SAT hot path. Instrumentation is indirect — they show up
as higher `flow_xy_decisions/s` and higher `stage_exit[3]/elapsed` but
not as their own TTC counters.

### P1. Reuse `seen` and `stack` allocations in conflict analysis

`analyze()` allocates `vec![false; num_vars]` on every conflict. `lit_removable()` allocates `visited` and `stack` on every call. Move these to solver-level reusable buffers (clear between uses). At n=26 with ~44 vars and hundreds of conflicts per solve, this eliminates thousands of heap allocations. Target: reduce malloc/free from 6% by ~1-2%.

**Result (v1):** Phase C n=26: 18.99s → 18.79s (-1.1%, within noise). Reverted — not a decisive win.
**Result (v2, iterated):** Extended to cover `compute_quad_pb_explanation` (16.67% of runtime returning `Vec<Lit>`), `lit_removable`, and all conflict analysis paths. Uses `mem::take` pattern for borrow-checker-safe buffer reuse. Phase C n=26: 18.88s → 16.99s (**-10.0%**). malloc/free dropped from 8.5% to ~2%. **Accepted.**

### P2. Avoid Vec allocation for `reason_lits` in `analyze()`

`analyze()` creates a `Vec<Lit>` for `reason_lits` on every resolution step (Clause, Pb, QuadPb). For Clause reasons, this is a needless `.to_vec()` copy. Switch to iterating the clause slice directly via an enum/index approach, avoiding allocation entirely for the clause case. The QuadPb and Pb paths still need allocation but are less frequent.

**Result:** Folded into P1 — the Clause path now iterates `clause_lits[cstart..cstart+clen]` directly with index-based access, no `.to_vec()`. PB and QuadPb paths reuse `analyze_reason_buf`.

### P3. Batch `clear_learnt` — don't call after every single config

In `solve_xy_with_sat`, line 2764: `configs_tested % 1 == 0` always evaluates true, meaning `clear_learnt` is called after every single boundary config SAT solve. This is wasteful — `clear_learnt` iterates all clause metadata + all watch lists. Batch to every N configs (e.g., 64 or 128) or skip entirely and rely on `reduce_db` in the solve loop.

**Status:** Already implemented (batched to every 8 configs, accepted in round 1, see optimization log). **N/A for n=56 cubed SAT** (only applies to `solve_xy_with_sat` hybrid path).

### P4. Skip `propagate_pb` for already-satisfied constraints

`propagate_pb` does a full scan of all literals in the constraint on every trigger. For PB constraints with large slack (many true literals), the scan is wasted work. Add a `satisfied` flag or slack cache that short-circuits when the constraint is trivially satisfied.

**Status: N/A for n=56 cubed SAT** — totalizer encoding uses only regular clauses, no PB constraints.

### P5. Eliminate `configs_tested % 1 == 0` dead code and reduce `clear_learnt` overhead

`clear_learnt()` iterates all `clause_meta` to mark learnt clauses deleted, then iterates all watch lists to retain. With incremental solving, learnt clauses from previous configs may actually help future configs. Try removing `clear_learnt` entirely from the table path — the solve loop's `reduce_db` already manages clause database size.

**Status:** Superseded by P3 implementation. **N/A for n=56 cubed SAT** (only applies to `solve_xy_with_sat` hybrid path).

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

**NOTE (2026-04-05):** R1-R10 were profiled on n=26 hybrid path.

**UPDATE (2026-04-05):** `--quad-pb` is now the default encoding: 223 vars, 55 quad PB constraints, 4 PB constraints. 797 solves/s at n=56 (vs 140/s with totalizer, **+470%**). Profile: `propagate` 55%, `solve_inner` 12%, `recompute_quad_pb` 4.4%, `backtrack` 2.6%.

R-series tested on n=56 `--quad-pb` (797/s baseline):
- **R2** (global stale flag): within noise (796/s). Stale check scan is cheap (55 entries, branch predictor handles it).
- **R3** (skip term update after recompute): **-6.5% regression** (745/s). Removing the incremental update breaks the propagation path.
- **R4** (state-based explanation filtering): within noise (800/s). MAYBE term skip saves ~50% of term scans but branch overhead roughly equals savings.
- **R10** (sort terms by variable index): **-2.4% regression** (778/s). Sorted order disrupts propagation candidate ordering.
- **CMS6/rephasing** tested at 200-conflict intervals: neutral to slight regression (792/s). Phase saving already well-targeted.

Remaining untested: R1 (fuse recompute — only 4.4% target, ~1% expected gain), R5 (PB slack — PB is negligible at 0.3%), R7 (flat arrays — 223 inner Vecs is small), R9 (mem::take — trivially cheap at 223 vars).

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

**Result (n=56 SAT cubed):** 69.0-71.3 vs baseline 69.0-70.1 — within noise. At n=56 scale with 576K clauses, the blocker short-circuit rate doesn't dominate. **Rejected.**

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

**Benchmark:** `turyn --n=56 --sat --tuple=8,14,6,1 --sat-secs=60 --conflict-limit=2000`
With k=7 table. Baseline (no CMS): 101 solves/60s, 1.63/s, avg 653 conflicts.
Note: --sat mode uses totalizer encoding (52K vars, 576K clauses at n=56).

### Results summary

| Idea | Status | n=56 solves/60s | Rate | Notes |
|------|--------|-----------------|------|-------|
| Baseline (no CMS) | — | 101 | 1.63/s | |
| + CMS4: Vivification | **Accepted** | 115-125 | 1.84-2.02/s | +18%, shortens learnt clauses every 500 conflicts |
| + CMS3: Chrono backtrack | **Accepted** | 628-671 | 10.4-11.1/s | +540%, avoids expensive deep backtracks in 52K-var problem |
| + CMS1: Phase-only warm | **Accepted** | 628 | 10.4/s | Stable ~10%, phase transfer between cubes |
| CMS2: Lucky phases | Rejected | — | -17% | Full propagation on UNSAT too expensive |
| CMS5: SCC equiv | Rejected | 106-118 | 1.55-1.71/s | 6372 equiv pairs found but no speedup |
| CMS7: XOR/GJ | Rejected | OOM | — | 25K XOR constraints + 52K vars exceeds memory |
| CMS8: BVE | Rejected | 99-104 | 1.55-1.64/s | 9360 vars eliminated, net neutral (code available) |
| CMS6: Local search | Skipped | — | — | SA operates on 167 primary vars, not 52K aux |
| CMS9: Distillation | Skipped | — | — | Subsumption on 576K clauses = O(n²) |
| CMS10: Community VSIDS | Skipped | — | — | Marginal with chrono BT already dominant |

**Cumulative: ~6.4x faster** (101 → 628-671 solves/60s)

### CMS1. Warm-start learnt clause and phase transfer across SAT calls

Keep a pool of high-quality learnt clauses (LBD <= 2) from previous solves and seed new instances with them. Save phase vectors from SAT results. The structural similarity between Z/W pairs means clauses about X/Y variable interactions are reusable.

**Single commit:** In `solve_xy_with_sat`, after each `solve_with_assumptions()`, extract learnt clauses with LBD <= 2 that don't mention assumption variables. Store in a shared pool (cap ~100 clauses). Before next solve, inject pool clauses. Save phase vector from SAT results and use as initial phase.

### CMS2. Lucky phases (Kissat)

Before main CDCL search, try a handful of complete assignments: all-positive, all-negative, and phases from previous solutions. Propagate each to completion — if consistent, return immediately. Over thousands of SAT calls, catching even 1-2% trivially saves time.

**Single commit:** In `solve_inner()` before the main loop, try 4-8 candidate phase vectors. For each: set all variables, propagate, check consistency. If any reaches a solution, return immediately. Cost: ~8 propagation passes per SAT call.

### CMS3. Chronological backtracking (CaDiCaL / MapleSAT)

When backjump level is close to current level (within threshold), backtrack chronologically (one level) instead. Avoids re-deriving implications already on the trail.

**Single commit:** In `analyze()`, after computing backjump level, check `current_level - backjump_level < 3`. If so, backtrack to `current_level - 1` instead. Handle re-propagated literals on the trail above backjump level.

### CMS4. Vivification / clause strengthening (CaDiCaL / Kissat)

Shorten existing clauses by tentatively assuming each literal is false and propagating. If conflict before exhausting clause, shorten it. Safe (temporary propagation fully undone). Apply to top learnt clauses by LBD during restarts.

**Single commit:** After each restart, pick top N learnt clauses by LBD. For each: save trail, assume negations left-to-right, propagate. If conflict at literal k, shorten to first k literals. Restore trail.

### CMS5. Equivalent literal substitution via SCC (Lingeling)

Build binary implication graph, run Tarjan's SCC to find equivalent literal pairs. Replace one with the other throughout formula. Shrinks variable count.

**Single commit:** At solver construction, extract binary implications from watch lists and XOR/PB constraints. Run Tarjan SCC. For each equivalence class, pick representative and substitute throughout clause, PB, and quad PB structures.

### CMS6. Local search phase advising (CryptoMiniSat 5.x)

Use SA engine as phase advisor: on every Nth restart, run short burst of local search (~5000 flips), import result as phase vector. Combines CDCL completeness with local search guidance.

**Single commit:** On every 4th restart, extract current partial assignment, run ~5000 SA flips targeting X/Y autocorrelation defect, import as phase[] vector. SA engine at 41M flips/s means ~0.1ms cost.

### CMS7. Gauss-Jordan elimination for XOR propagation (CryptoMiniSat)

Maintain XOR constraint matrix in row-echelon form. When multiple XORs interact, GJ deduces implications that individual XOR propagation misses. Dense, interdependent XOR structure makes this high-impact.

**Single commit:** In `propagate()`, after BCP, run incremental GJ elimination on XOR matrix. Maintain row-echelon form (add/remove rows on assign/backtrack). When row reduces to single variable, enqueue as unit.

### CMS8. Bounded variable elimination (BVE) inprocessing (CaDiCaL)

Resolve out variables appearing in few clauses. If resolvent count <= original, eliminate. Focus on any remaining CNF clauses (symmetry breaking, learnt).

**Single commit:** Before first `solve()`, scan for variables in few clauses. Compute resolvents. If count <= original, apply elimination. Note: with quad PB encoding we have very few clauses, so may have limited scope.

### CMS9. Clause distillation / inprocessing (Lingeling)

Periodically run subsumption + self-subsuming resolution on clause database. Different from vivification — focuses on inter-clause relationships.

**Single commit:** Every 100 restarts at decision level 0: sort clauses by length, check for subsumption, apply self-subsuming resolution. Focus on template's original clauses.

### CMS10. Community-structure-aware branching (CryptoMiniSat)

Partition variables into communities (X-vars vs Y-vars, or by lag group). Bias VSIDS to prefer variables in same community as recent decisions.

**Single commit:** At construction, assign each variable to community (X vs Y). Add community bonus to VSIDS: prefer same-community variables. Produces lower-LBD learnt clauses.

## Phase B: SAT-based W middle generation (credit: Claude, April 2026)

For large n (n≥40), brute-force W middle enumeration via `generate_sequences_permuted` is the Phase B bottleneck. At n=56 with k=9, W middle has 37 free positions with C(37,19)≈17.7B combinations for sum=1. Even with LCG-scattered sampling (max_w=200K), the spectral rejection rate is high and most samples are wasted. The fix: use SAT to generate W middles, streaming each one immediately to Z generation and Phase C.

### W1. SAT solver for W middle with sum constraint — **Implemented**

Replace `generate_sequences_permuted` for W middles with a SAT solver encoding the cardinality constraint. Adaptive threshold: use SAT when C(middle_m, r) > 10 × max_w, brute-force DFS otherwise. SAT-based generation uses random phase initialization (xorshift64) for diversity and blocking clauses for uniqueness.

**Result:** Implemented in `sat_w_middle.rs` + `run_mdd_sat_search()`. At n≥42 k=8, SAT activates (C(25,12)=5.2M > 2M threshold). For n=56 k=8, space is 69B — brute-force would need to sample <0.0003% via LCG scatter. SAT generates max_w solutions directly. No regression on small-n benchmarks (n=18 k=8: 49.7ms → 45.0ms). **Accepted.**

### W2. Streaming W→Z pipeline — **Tried, rejected**

Streaming each W directly to Z SAT solver (sat_z_middle) instead of batch+SpectralIndex approach.

**Result:** The per-W Z SAT solver's autocorrelation constraints are W-specific, severely limiting Z diversity. SpectralIndex pairing across multiple W candidates finds far more (Z,W) pairs. n=24 k=4: streaming found 0 SAT items vs baseline ~190K. **Rejected** — batch W + SpectralIndex + brute-force Z is superior.

### W3. Random phase diversity in W SAT solver — **Implemented** (with W1)

xorshift64 PRNG seeded from (z_bnd_sum, w_bnd_sum) provides deterministic but diverse phase initialization. Combined with blocking clauses, ensures unique and varied W candidates.

### W4. SAT-based Z middle generation in MDD path — **Rejected**

Replaced brute-force Z with sat_z_middle in run_mdd_sat_search(). Z SAT solver's tight autocorrelation constraints (given fixed W) produce few Z candidates that also pass spectral pair filter. Brute-force Z with SpectralIndex covers more of the Z space and pairs better.

**Result:** n=24 k=4: 0 SAT items dispatched (vs 190K with brute-force). The SpectralIndex approach tests many Z×W combinations; SAT limits Z to one W at a time. **Rejected.**

### W6. Hoist W generation out of per-boundary loop — **Implemented**

W middles depend only on (middle_m, w_mid_sum), not boundary bits. Generate ONCE per (sum_group, tuple) and reuse across all entries. Each entry still does per-boundary spectral filtering (different prefix/suffix). Eliminates redundant W generation for groups with many entries.

**Result:** n=18 k=4: 45.3ms → 43.9ms. n=24 k=4: ~70s → ~63s. **Accepted.**

### W7. Group boundary entries by (w_bits, z_bits) — **Implemented**

Entries with identical (w_bits, z_bits) share BOTH W and Z spectral filtering + pair checking. Only the XY sub-MDD walk differs per entry. Combined with W6 (hoisted W generation), this eliminates ALL redundant FFT work.

**Result:** n=24 k=4: ~70s → ~10-18s (cumulative **75-85% speedup** from W1+W6+W7). At n=56 k=8, 128M boundaries reduce to fewer unique (w_bits, z_bits) pairs, expected dramatic FFT savings. **Accepted.**

### W5. W autocorrelation constraints in SAT (approximate spectral filter)

Add per-lag W autocorrelation decomposition to the W SAT solver: boundary×boundary (constant), boundary×middle (linear PB terms), middle×middle (quad PB terms via XNOR aux or direct quad PB). Even with trivially-satisfied per-lag bounds, the quad PB variable interactions create CDCL conflicts that bias the solver toward lower-autocorrelation (hence lower-spectral-power) solutions. Expected to increase spectral pass rate.

**Single commit:** In `build_w_middle_solver()`, for each lag s (1..m-1): decompose agree count into const + linear + quad terms. Add PB/quad PB constraints with bounds [adj_lo, adj_hi]. Benchmark spectral pass rate before/after.

## Throughput Optimization Ideas (April 2026, from profiling)

Profile: n=56 k=10, 4 workers, 30s. Baseline: **2487 xy/s**.
The SAT solver (radical) dominates: recompute_quad_pb (34.7%), propagate (20.1%), compute_quad_pb_explanation_into (15.1%), solve_inner (11.2%), propagate_pb (7.2%), backtrack (4.3%).

### T1. Eliminate Vec allocation in compute_lbd
`compute_lbd` allocates `vec![false; decision_level+1]` on every conflict. Replace with a reusable solver-level buffer.
**Single commit:** Add `lbd_buf: Vec<bool>` field to Solver, resize and clear in `compute_lbd` instead of allocating.

### T2. SIMD-accelerate recompute_quad_pb
The inner loop loads aa/ab from assigns[], does table lookup, accumulates sums. Batch 8+ terms with SIMD gather/scatter.
**Single commit:** Rewrite `recompute_quad_pb` inner loop with `#[target_feature(enable = "avx2")]` using gather intrinsics.

### T3. Track dirty quad PB constraints explicitly
`recompute_stale_quad_pb` scans ALL constraints. Replace with explicit dirty-set Vec.
**Single commit:** Add `stale_quad_pb: Vec<u32>` to Solver, push on mark-stale, drain on recompute.

### T4. Pack QuadPbTerm tighter for cache density
Currently 16 bytes. Explore 12-byte packing by combining small fields.
**Single commit:** Restructure QuadPbTerm layout, benchmark cache effect.

### T5. Conflict limit per XY solve
Hard UNSAT instances waste time. Set conflict limit (e.g., 10K) to fail fast.
**Single commit:** Add `solver.set_conflict_limit(10000)` before XY solve, benchmark throughput vs. miss rate.

### T6. Pre-gather assigns for cache-friendly quad PB recompute
Sort terms by variable index or pre-copy assigns into contiguous buffer.
**Single commit:** Pre-sort terms in `add_quad_pb_eq`, benchmark recompute speedup.

### T7. Replace GJ with assumptions-based approach
GJ is O(n^2) per candidate. Use solver assumptions instead.
**Single commit:** Convert GJ equalities to unit assumptions, skip Gauss-Jordan.

### T8. Strengthen feasibility pre-filter
Add parity checks and tighter range bounds before cloning solver.
**Single commit:** Add parity + tighter bound checks in `is_feasible`.

### T9. Cache GJ results by zw_autocorr
Many candidates share zw_autocorr. Cache equalities by hash.
**Single commit:** Add `HashMap<u64, Vec<(i32,i32,bool)>>` cache in worker, hash zw_autocorr.

### T10. Copy-on-write solver clone
Share immutable clause DB, only copy mutable state.
**Single commit:** Split Solver into shared/mutable parts, share clause_lits/clause_meta.

### T11. Merge quad PB constraints for lags with same target
Reduce constraint count by combining equivalent lags.
**Single commit:** Group lags by target, merge term lists, benchmark propagation savings.

### T12. Incremental XY solver with checkpoint/restore
Skip clone entirely: keep persistent solver, checkpoint/restore per candidate.
**Single commit:** Use save_checkpoint/restore_checkpoint in solve_for_warm.

### T13. Skip trivially-satisfied PB constraints
Track min-slack incrementally, skip propagation when slack is large.
**Single commit:** Add slack tracking to PB propagation, skip when slack > max_coeff.

### T14. Branchless lit_value
Replace branches in lit_value with lookup table.
**Single commit:** Implement 6-entry lookup table for lit_value.

### T15. Pre-compute spectral constraint boundary-independent parts
Avoid re-creating SpectralConstraint per boundary.
**Single commit:** Factor SpectralConstraint::new into reusable + boundary parts.

### T16. Lock-free work queue
Replace Mutex<BinaryHeap> with lock-free concurrent queue.
**Single commit:** Implement crossbeam-style lock-free priority queue or per-worker queues.

### T17. Batch XY item emission
Batch walk_xy_sub_mdd results, push all at once.
**Single commit:** Collect XY items in Vec, single lock acquisition for batch push.

### T18. Sort quad PB terms by variable index
Improve assigns[] cache locality during recompute.
**Single commit:** Sort terms in add_quad_pb_eq by min(var_a, var_b).

### T19. Optimize XOR propagation — precompute last-unknown
Replace linear scan with tracked last-unknown variable.
**Single commit:** Cache last_unknown_var in XorConstraint, update incrementally.

### T20. Disable warm-start clause injection
Profile whether warm-start clauses help or hurt throughput.
**Single commit:** Set `inject_clauses: false` (already default), verify no regression.

### T21. Share lag_pairs across tuples in template cache
SatXYTemplate is rebuilt per tuple but lag_pairs is tuple-independent.
**Single commit:** Factor lag_pairs out of SatXYTemplate, share via Arc.

### T22. Smaller clause indices for cache density
Use u16 for watch list entries if clause count < 65K.
**Single commit:** Conditional u16 clause IDs, benchmark cache improvement.

### T23. Dedicated monitor thread (already exists)
Verify monitor thread isn't starving workers by sleeping too long.
**Single commit:** Reduce monitor sleep from 10ms to 1ms, benchmark fill rate.

### T24. Fuse GJ equalities into quad PB terms
Substitute equal variables directly into quad PB constraints.
**Single commit:** After GJ, rewrite quad PB term lists to use canonical variables.

---

## Boundaries/s → Time to Cover paradigm shift

**2026-04-09 insight**: the right optimization metric is boundaries/s
(eliminate dead regions), NOT xy/s (per-candidate throughput). Pruning
a dead boundary early is a win even if per-boundary overhead rises.

**2026-04-15 refinement (this audit)**: bnd/s is still the wrong
normaliser because it ignores *total work*. TTC = `(live_zw_paths -
eff) / (eff/s)` is the right metric:

- Shrinking `live_zw_paths` (larger k, tighter MDD) is credited
  *even if bnd/s doesn't move*.
- A boundary that XY-times-out contributes <1.0 via `xy_cover_micro`,
  so bnd/s overstates progress on hard instances.
- Cross and MDD modes get directly comparable numbers (same units —
  wall-clock seconds to finish).

**Practical guidance when evaluating an idea**:

1. Does it change `live_zw_paths`? (MDD-side lever)
2. Does it change `stage_exit[0]/s`? (pipeline rate lever)
3. Does it change `flow_xy_timeout / flow_xy_solves`? (shortfall
   lever)
4. Ideally all three are examined; none alone is a full picture.

Previous ideas like `--mdd-extend=1` were rejected on xy/s alone —
TTC retrospect says that was wrong; see E1 below.

### E1. Restore extension check before XY SAT — **ACCEPTED**
Restored `has_extension()` in `walk_xy_sub_mdd` callback with per-worker
u128 cache.

- **TTC mechanism**: rate — prunes ~44% of XY candidates at n=56
  k=10 *before* the SAT clone. Also cuts `flow_xy_timeout` by
  eliminating the deepest UNSATs.
- **Measurement**: median bnd/s 394→504 (+28%); worst-case cliff
  eliminated (92→498–538 stable). Neutral at n=26 (307 both).
- **Status**: wired at `src/main.rs:3458-3471` behind `cfg.mdd_extend`.
  Default is `mdd_extend=1` for MDD modes (src/main.rs:4687). TTC
  feed: `extensions_pruned` atomic counter reported in the final
  block (src/main.rs:2694).

### E2. ZW-only boundary autocorrelation bound at stage 0 — **REJECTED**
Implemented and tested. At n=26 k=7: only 27 out of 8637 boundaries pruned (0.3%).
At n=56 k=10: similarly negligible. The XY slack (2×(n-1-j) free pairs) overwhelms
the ZW boundary contribution. Would need XY info to be effective, but that's only
available at stage 3. ZW-only check fundamentally too loose.

### E3. Extension check cache — **IMPLEMENTED (part of E1)**
Per-worker HashMap<u128, bool> cache. Key = (z_bits, w_bits, x_bits, y_bits) packed
into u128. Critical for performance: same boundary 4-tuple is checked across Z
solutions, cache avoids redundant MDD builds.

### E4. Early W spectral reject saves boundary throughput
Currently SolveW generates W middles and filters by individual spectral bound.
Tighten this: compute the ZW combined spectral bound and reject W values that
can't possibly combine with any Z to meet the pair bound. This prunes W earlier,
freeing workers for more boundaries.
**Single commit:** Add combined ZW spectral pre-filter in SolveW brute-force loop.

### E4. Early W spectral reject — **REJECTED (analysis)**
Analyzed: W individual bound = (6n-2)/2 = 3n-1. The pair constraint gives
2|W(ω)|² ≤ 6n-2, i.e., |W(ω)|² ≤ 3n-1 = individual_bound. Already optimal.
A tighter Z-aware bound using min_Z_power(ω) = max(0, |DFT_Z_bnd|-middle_n)²
degenerates to individual_bound when middle_n > 2k (true for n=56 k=10).

### E5. Conflict limit proportional to boundary promise — **REJECTED**
Tested reducing XY conflict limit from 5K to 2K at n=56: median bnd/s dropped
from 431 to 123. The 5K limit is well-tuned: enough to find SAT answers that
exist, not too many to waste on hard UNSAT.

### E6. Skip already-explored ZW pairs across tuples
When a (z_bits, w_bits) pair is explored for one tuple, the W/Z work is done.
If the same ZW pair appears for another tuple (different sum target), the
W middles and Z solves are independent. But the boundary was already "walked."
Track explored ZW pairs to avoid re-processing expensive stages.
**Single commit:** Add per-worker HashSet of explored (z_bits, w_bits, tuple) triples.

### E7. Batch boundary pruning with precomputed k+1 node reachability
Build MDD at k+1, precompute which k-boundary (z_bits, w_bits) patterns are
prefixes of valid k+1 boundaries. Store as a Bloom filter or HashSet. At stage 0,
reject boundaries not in the set. Cost: one-time MDD build at k+1.
**Single commit:** After loading k-MDD, build k+1 ZW-only MDD, extract valid k-prefixes.

### E8. Checkpoint/restore XY solver instead of clone — **REJECTED (profiling)**
Profiled: prepare_candidate_solver (clone) takes only 504us/call, 12ms total
in a 30s run = 0.04% of time. The clone overhead is negligible compared to
XY SAT time (5036ms). Not worth the complexity of checkpoint/restore.

### E9. Pre-check XY extensions at stage 0 — **REJECTED (analysis)**
Walk XY sub-MDD at stage 0 and check extension for all (x,y). If none pass,
skip the boundary. Analysis: with 44% per-candidate prune rate and ~44
candidates per boundary, P(all fail) = 0.35^44 ≈ 0. No boundaries pruned.

### E10. extend=2 vs extend=1 comparison
Tested: extend=1 median=538 bnd/s, extend=2 median=485 bnd/s (5 runs each).
extend=2 prunes more candidates but the per-check cost is higher (larger MDD).
extend=1 is the better choice for n=56 k=10.

### E11. Group SolveW by w_mid_sum to share W SAT — **REJECTED**
Group tuples with same w_mid_sum into one SolveW, run W SAT once and fan out
SolveZ items to all matching tuples. Reduces W items from 161K to 68K (-58%).
But bnd/s dropped from 538 to 381 (-29%). The Vec cloning overhead for fan-out
and altered pipeline dynamics (more SolveZ items created simultaneously) cause
a systematic regression. The W SAT reduction doesn't compensate.

### E12. Encode XY sub-MDD as SAT constraint — **PARTIALLY DONE,
NOT WIRED**

Instead of enumerating ~3400 (x,y) boundary candidates and solving
each, encode the MDD as a constraint so one solver call explores all
boundaries with clause-learning across them.

**Tseitin encoding** (tested, scales poorly): 10× faster at n=18;
regressed at n=20+ due to aux-var blowup.

**Activity boosting** (tested, no benefit): boundary vars pinned by
assumptions, VSIDS moot.

**Native MDD propagator** — **IMPLEMENTED in radical but NOT wired
into the live pipeline.**

- **TTC mechanism (predicted)**: denominator — conflict-driven
  sub-tree pruning. Today's pipeline iterates every (x,y) leaf and
  calls `try_candidate`; `solve_with_assumptions` already persists
  learnt clauses across leaves, so it's *not* a "save the clone"
  story. The actual marginal win is that a conflict can kill many
  MDD paths at once via a single learnt clause, whereas today each
  leaf still triggers an enumeration step + short SAT call. Rate
  also improves marginally (one solve-setup per boundary instead
  of per leaf), but the denominator effect dominates.
- **Predicted range**: extrapolating from the n=18 Tseitin
  result (10×) is optimistic because Tseitin had the aux-var
  penalty that the native propagator avoids, but Tseitin regressed
  at n=22 for the same reason. Plausibly 2-10× reduction in
  `flow_xy_solves/boundary` at n=26; could easily be flat or
  negative at n=56. **Not a measurement.** Verify before
  celebrating.
- **Status**: commit 3a0563c added `MddConstraint` at
  `radical/src/lib.rs:82`, `add_mdd_constraint`
  (line 1103), and `propagate_mdd` (line 1166). Commit 62396ed
  attempted to wire this via an `XY_MODE=mdd` env switch.
  **Verification**: `grep add_mdd_constraint src/main.rs` → no
  hits. The propagator is not currently called anywhere in the
  search pipeline. Tests around it are live in radical's unit
  tests, not in the search.
- **Action**: this is the #1 candidate to revive. See final report.

## Interventions found only in git log (audit 2026-04-16)

These are either too small to have merited their own IDEAS entry, or
they landed before TTC existed. All verified by reading the listed
code locations.

### G1. `max_z` cap from 10 → 1 per SolveZ item (commit b65021d, b65021d)
- **TTC mechanism**: rate. The post-hoc FFT pair check rejects >99.99%
  of Z solutions at small k. Enumerating more Z per W wastes SAT time
  without covering new (z_boundary, W) pairs faster.
- **Measured**: n=26 k=3 boundaries-walked-in-20s: max_z=1→14,
  max_z=10→15, max_z=100→11, max_z=200000→9. Picking 1 maximises bnd
  coverage rate.
- **Status**: `max_z: cfg.max_z.min(1)` at src/main.rs:2545.

### G2. Skip blocking clause on last Z iteration (9df0881)
- **TTC mechanism**: rate — saves one SAT incremental step on the Z
  loop's final iteration since no further solve will use the block.

### G3. Sign-flip instead of multiply in W DFT inner loop (38967d2)
- **TTC mechanism**: rate — a small constant-factor speedup in the W
  spectral filter loop. Shows up in SolveW time per W.
- **Status**: in `sat_z_middle.rs` W fill path.

### G4. SpectralConstraint Arc-share of tables (f7a7864)
- **TTC mechanism**: rate — avoids O(n×θ) table clones per SolveZ.
- **Status**: radical/src/lib.rs:284 — `SpectralTables` held in `Arc`.

### G5. Cache z_boundary DFT alongside fill prep (b053c81)
- **TTC mechanism**: rate — reuses the boundary DFT across all W's
  for the same z_boundary instead of recomputing per SolveZ.
- **Status**: `ZBoundaryPrep` in src/sat_z_middle.rs.

### G6. Buffered spectrum reuse in SolveW brute-force (63bda36, 7be4015)
- **TTC mechanism**: rate — one allocation per worker instead of
  per-W for the W post-hoc spectrum.

### G7. Batch queue pushes in SolveW / Boundary stages (04f90a6)
- **TTC mechanism**: rate — fewer lock acquisitions on the shared
  `work_queue`. Important because workers contend on the queue
  mutex.

### G8. MDD-guided tuple fail-fast (f2a6ec9)
- **TTC mechanism**: denominator (skipped tuples ≡ work never
  issued). If `any_valid_xy(xy_root, tuple)` is empty, that tuple
  contributes nothing to this boundary.
- **Status**: in `Boundary` stage handler (src/main.rs:run_mdd_sat_
  search).

### G9. XY dedup (1 solve per Z/W pair) — critical correctness+rate
- **TTC mechanism**: denominator — prior code re-solved the same
  (z_bits, w_bits, x_bits, y_bits) up to 69× per tuple.
- **Status**: per-worker `ext_cache: HashMap<u128,bool>`
  (src/main.rs:3459) plus `SolveXyPerCandidate`'s own
  `configs_tested` counter.
- **Measured**: 3× boundary throughput at n=18, TT(18) in 148ms.

### G10. Live MDD path counting for denominator (22d119e, 8c6ee56,
ec7b3bc, 1c846e6)
- **TTC mechanism**: denominator (this IS the TTC denominator in MDD
  modes).
- **Status**: `count_live_paths` in `src/mdd_reorder.rs:25` (walks
  the MDD counting 4^(depth-level) per LEAF and 0 per DEAD). Live
  ZW paths computed once at startup (src/main.rs:2503).
- **TTC feed**: yes — the denominator `live_zw_paths` passed into
  TTC formula.

### G11. Quad PB + XOR soundness fixes (d337131 → 2ad1bb5 →
9007880 → f0dc681)
- **TTC mechanism**: neither rate nor denominator — these are
  *correctness* fixes. Before them, the solver returned false
  UNSAT. Having sound UNSAT means `flow_xy_unsat` contributes full
  1.0 to `eff`; without soundness, walked boundaries that claimed
  UNSAT were actually unexplored.
- **Status**: fixed; `XorConstraint` re-counts unknowns from
  `assigns[]` on each update (radical/src/lib.rs).
- **Note**: if we ever resurrect native MDD propagator (E12), a
  similar correctness audit is needed for its `propagate_mdd` path
  — the propagator passes unit tests but has never been measured
  against the full Turyn pipeline.

### G12. Native MDD propagator (3a0563c, 62396ed) — see E12 above.
Not wired.

### G13. Subcube elimination metric (ec7b3bc, 1c846e6, 8c6ee56)
- Early attempts at denominator-like metrics before TTC was invented.
  `mdd_elim_log2` in src/main.rs:3927 is computed but gated behind
  `_mdd_elim_log2 = ...` (underscore-prefixed → unused). Dead code
  that could be either revived or removed; it estimates
  "2^subcube × dead_paths" eliminated at MDD build time.
- **TTC mechanism**: this *would* be a second denominator view —
  total configs pruned at build time — but TTC already captures
  this via the live-path count.
- **Status**: dead code. Safe to remove.

### G14. TTC metric instrumentation (de8ceef, 0203ba3, 8156e6e,
bc9beb7) — **this is TTC itself**.
- `stage_exit[0..3]` counters (src/main.rs:2740, 2885, 3014, 3215,
  3265, 3475) — true completion counts, not queue pushes.
- `flow_*_decisions/propagations/root_forced/free_sum`
  (src/main.rs:2717-2733) — per-stage SAT pruning stats.
- `flow_xy_sat/unsat/timeout/timeout_cov_micro`
  (src/main.rs:2737) — XY outcome counts and fractional coverage.
- `effective_coverage_metric` (src/main.rs:4210) — MDD-mode eff.
- `cross_estimated_total_xy` (src/main.rs:4185) — cross-mode total.
- `xy_cover_micro` (src/main.rs:4153) — fractional credit for
  timeouts based on `log2(decisions+1)/free_vars`.
- `print_stage_pruning_block` (src/main.rs:4229) — diagnostics.

### G15. T-sequence direct finder (2f90864, 01feaee)
- `src/bin/tseq.rs` and `src/bin/tseq_mdd.rs` are a separate search
  that does not go through the Turyn pipeline. Memo experiments
  found 0 cache hits on `--memo` mode; `tseq_mdd --cross-only` has
  70-90% last-few-level hit rate.
- **TTC mechanism**: not applicable — tseq doesn't produce the
  stage_exit counters.
- **Status**: separate binary, not instrumented for TTC. Open
  question: should TTC be extended to cover tseq too?

## Idea audit: ideas that should be retried now that TTC exists

(Ideas previously rejected on xy/s grounds that might be wins on
TTC. Details in the final report.)

- **E2 ZW-only boundary autocorr bound**: rejected on 0.3% prune
  rate at n=26, but the relevant number for TTC is *shortfall
  reduction* when XY times out, not just prune rate.
- **E4 Early W spectral reject**: rejected on analysis showing
  individual bound is already optimal without Z info. But a
  Z-conditioned early reject using `min_Z_power` for boundary-
  compatible Z could work — basically London §3.4 item 1's
  Z-aware tightening, applied inside SolveW.
- **E11 Group SolveW by w_mid_sum**: rejected on bnd/s drop; but it
  reduced W SAT items by 58% (i.e. denominator at the W-stage
  level). With quad-PB-dominated XY, the W cost may now be small
  enough that the regression is noise.
- **DR projection for XY timeout reduction**: ideas like Douglas-
  Rachford could be re-framed as pre-filters that specifically
  target reducing `flow_xy_timeout` — the shortfall term, which
  we never used to measure.
- **Native MDD propagator (E12)**: already in radical,
  just not wired.

These are promoted for retest in the report below.

---

## Audit report (2026-04-16): most-important untried & retry candidates

Framed against TTC. Ordered by expected leverage. All location
references verified in code.

### Tier 1 — ship these next

1. **Wire the native MDD propagator into the XY SAT stage (E12).**
   - **Why it's worth trying**: the code already exists
     (`MddConstraint` at radical/src/lib.rs:82, `add_mdd_constraint`
     at 1103, `propagate_mdd` at 1166) and the Tseitin precursor
     showed a measured 10× at n=18 — so there *is* a win to extract
     somewhere. The native propagator was specifically designed to
     avoid the aux-var penalty that killed Tseitin at n≥22. Never
     wired after `SolveXyPerCandidate` unified the XY fast path.
   - **What I am NOT claiming**: this isn't a "save the clone" win.
     `SolveXyPerCandidate::new` already clones once per (Z,W) pair,
     not per (x,y); `try_candidate` uses `solve_with_assumptions`,
     so learnt clauses already persist across XY candidates in the
     same boundary. The clone-elimination pitch from earlier drafts
     was wrong.
   - **What the actual marginal win looks like**: conflict-driven
     sub-tree pruning. When the solver discovers a conflict deep in
     the XY assignment, today we still enumerate every other MDD
     leaf and call `try_candidate` (fast, but still O(leaves)). A
     native MDD constraint lets one learnt clause eliminate many
     leaves at once via BCP.
   - **Predicted range**: plausibly 2-10× reduction in
     `flow_xy_solves/boundary` at n=26. Extrapolating from n=18
     Tseitin to n=56 is speculative — it could be flat or negative
     there. **This is a prediction, not a measurement.**
   - **Detection plan**: add an `XY_MODE` switch to
     `SolveXyPerCandidate::new`. Compare TTC on n=26 --wz=apart k=7
     at 60s with mode=per-candidate vs mode=mdd-constraint. The
     signal to watch is `flow_xy_solves/boundary` (from the final
     stats block); TTC should drop roughly in proportion.
   - **Risk**: same soundness-bug class as the XOR false-UNSAT
     chain from Feb 2026. Gate behind an env flag; run the
     `known_tt26_verifies` regression test before trusting any
     speedup number.

2. **Boundary-level XY timeout budget.**
   - **Why it matters**: currently 5K conflicts/XY for n>30.
     `flow_xy_timeout/flow_xy_solves` at n=56 is nonzero; each
     timeout is fractional coverage. If we set a *boundary-level*
     budget (e.g. total conflicts per boundary ≤ N × avg_solve),
     we trade a small rate drop for a big shortfall cut — TTC net
     positive because each timed-out boundary credits less than 1
     today.
   - **Detection plan**: sweep the budget and plot TTC vs budget.
     The per-stage block already shows `timeout%` and `avg cov`;
     add total XY budget as a CLI flag and diff.
   - **Code**: src/main.rs:3191 and 3584 set
     `set_conflict_limit(5000)` unconditionally for n>30.

3. **Retire dead TTC-adjacent code** (`_mdd_elim_log2`,
   unused subcube stats). Keep one denominator (`live_zw_paths`).
   Makes it easier for future ideas to attribute their effect.

### Tier 2 — retry on TTC

These are ideas that were rejected on bnd/s or xy/s alone and never
evaluated against TTC. Expected TTC payoff is plausible but
unmeasured.

4. **E11 group SolveW by w_mid_sum** — 58% fewer W SAT items
   (denominator at the W stage) was called a −29% bnd/s regression.
   With quad PB now default, W work is a smaller share; expected
   TTC is roughly flat or positive.

5. **E4 Z-aware early W spectral reject** — rejected because the
   individual W bound is already optimal. But a *Z-boundary-
   conditioned* early reject using `min_Z_power(ω)` restricted to
   Z candidates compatible with the current MDD sub-tree can
   tighten beyond the individual bound. Implementation: compute
   `min_Z_power` once per boundary's live Z sub-MDD, reject W
   below the tighter bound.

6. **Gemini incremental spectral pruning — in XY SAT**, not the
   old backtracker. Track `|X(ω)|² + |Y(ω)|² partial` as
   assignments come in; reject at first frequency where budget
   exceeds `6n-2 - 2|Z(ω)|² - 2|W(ω)|²`. Today we only enforce
   this spectrally for Z (via `SpectralConstraint`); doing it for
   XY is a direct shortfall win on tough boundaries.

7. **Revive London §3.4 item 4 (pair-based tuple search) at n≥26**.
   The "unique (|z|,|w|) per tuple" finding was at n=16, 22. The
   cross-mode `cross_w_cache` already caches w_candidates by
   `tuple.w` — extend to MDD modes and add z-side caching.

### Tier 3 — interventions that may have optimized the wrong thing

These are accepted optimizations where the win is suspect under TTC.

8. **max_z = 1** (forced cap, src/main.rs:2545). Justified on
   "boundaries walked in 20 s at n=26 k=3". That's a rate-only
   number. At large n where SolveZ is cheap relative to walking,
   a slightly higher cap might amortize z_boundary prep better.
   **Action**: re-sweep `max_z ∈ {1,2,4,8}` at n=56 --wz=apart
   k=10 with TTC as the metric.

9. **Conflict limit 5000 for n>30** (src/main.rs:3191, 3584).
   Chosen to recover +112% xy/s. But xy/s-per-solve ≠ TTC:
   shortening timeouts gives up partial coverage and inflates
   the TTC denominator through the `xy_cover_micro` term.
   **Action**: sweep `conflict_limit ∈ {2K, 5K, 10K, 20K, 50K}`
   at n=56 against TTC (not against xy/s).

10. **Dual queue (gold + work)** — accepted because a single PQ
    starved the pipeline. Current dual queue uses a coinflip
    between XY and upstream items. **Risk**: the ratio is hard-
    coded and never tuned against TTC. A monitor that adapts the
    coinflip based on `flow_xy_timeout%` might squeeze ~5-10%.

11. **`mdd_extend = 1` hard-coded** for `--wz=apart|together`
    (src/main.rs:4687). Accepted on +28% bnd/s; `extend=2`
    rejected on lower bnd/s. But the candidate-prune rate at
    extend=2 is higher, which would be a denominator win. **Not
    re-measured under TTC.**

### Tier 4 — cleanup that aids future measurement

12. **TTC for tseq.rs / tseq_mdd.rs** — separate binaries, no
    stage_exit counters. Either define a tseq-specific coverage
    metric or mark them as out-of-scope for TTC explicitly.

13. **cadical feature flag** — present but not integrated with
    the MDD pipeline's custom constraints. Either integrate
    (adapter that keeps quad PB / spectral / MDD propagators on
    the radical path) or retire the dependency. Current state is
    code bloat with no TTC feed.

14. **toc-ideas.md** — the TOC analysis predates TTC and still
    frames ideas in terms of "quality of (Z,W)". With TTC that
    frame becomes "shortfall + denominator" — rewrite the
    document in TTC terms so new ideas land in the right lever.

### Candidates that no longer look effective in hindsight

15. **EMA restarts / rephasing / vivification / chrono BT**:
    code paths in radical, defaults off, never turned back on.
    Each was rejected on n=22 rate benchmarks. At n=56 where
    timeouts dominate, it's plausible that *one* of these helps
    shortfall — but without a TTC experiment it's impossible to
    say. **Action**: a single sweep day across all four flags at
    n=56 would settle whether any deserves to become default.

16. **Round-2 R-series ideas (R1, R5, R7, R9, R10)**: all
    rejected on `xy/s` at n=56 `--quad-pb` where the solver
    dominates. If the MDD propagator lands, these profiles shift
    dramatically and several are worth re-evaluating.

17. **CaDiCaL integration** (CMS8 BVE specifically): rejected
    because the template has "nothing to eliminate" with quad
    PB. If we instead passed *expanded* XY constraints to
    CaDiCaL on a per-boundary basis, BVE might preprocess the
    whole XY sub-tree at once — a denominator-ish win. Low
    priority given the propagator option in tier 1.

### Summary

The most *tractable* unshipped experiment is **wiring
`MddConstraint` into the XY SAT stage** — code exists, it's just
not called, and the Tseitin precursor gives us ground truth that a
win of *some* size exists at small n. The actual magnitude at n≥26
is unmeasured and the pitch needs to be "worth trying" not
"guaranteed win." The biggest *"wrong-metric" regret* is that
several tuning decisions (`max_z=1`, conflict_limit=5K,
mdd_extend=1) were made on xy/s or bnd/s and have never been
retested against TTC; at minimum one sweep of each is cheap and
either confirms the decision or flips it.

**Update (2026-04-17)**: the native MDD propagator has since been
wired (commits 9160e15 / 2f92c5a / 6cee2ce / c3d70ca / d516c64).
Accessible via `--wz=xyzw` as a single-SAT-call architecture
covering all four sequences; see the "April 2026 — MDD-as-
propagator architecture experiments" section of
`docs/OPTIMIZATION_LOG.md` for measurements. Short version: 99%+
fewer XY solves confirmed, but per-solve cost grew to match —
net TTC roughly flat at n=26 because `solve_with_assumptions`
already transfers learnt clauses across leaves. `--wz=xyzw` is a
correct proof-of-architecture; to beat the pipeline at n≥18 it
needs a multi-sequence spectral constraint in `radical`.

## SolveWZ enumeration ideas (not yet tried)

- **Hand off timed-out SAT state to `--stochastic` worker**: When SolveWZ's
  `solver.solve()` returns `None` (conflict limit hit), the solver has a
  partial assignment representing its last exploration frontier. We could
  extract the learnt clauses + current trail as a seed for a stochastic
  local-search worker (e.g. one of the `TURYN_THREADS` workers running a
  completely different algorithm on the same boundary).  The stochastic
  worker operates on full ±1 sequences, so it'd need a bridge: read the
  partial assignment → fill unassigned middle positions with random ±1 →
  run WalkSAT-style local search.
- **Seed blind SAT with `--stochastic` output**: Before `--wz=together`
  starts, run `--stochastic` for a short budget (say 10s) to collect a
  handful of candidate (W, Z) pairs at the canonical boundary.  Feed
  those as blocking-clause seeds or initial-phase hints to each SolveWZ
  SAT — the solver's first few decisions would then align with the
  stochastic's best guess, dramatically improving hit rate on the
  canonical pair.  Downside: `--stochastic` has no concept of the MDD
  boundary, so we'd need to filter its output by boundary bits.
- **Branch heuristic bias**: instead of random phases on every retry,
  initialise the phase vector to match the "all +1" canonical prefix
  (BDKR rule i pins x[0]=y[0]=z[0]=w[0]=+1, and similar tail pins).
  The SAT would then explore canonical-biased region first, possibly
  finding canonical TT in the first solve.

## Fix performance regression of c8a0db5 (April 2026)

**Context:** Commit `c8a0db5` ("turyn: add coupled WZ per-lag constraints to
--wz=together (1460x speedup)") added a per-lag autocorrelation constraint
encoded as quadratic PB on the union of W and Z agree literals. While the
commit's claim of 1460x decision reduction at n=26 k=7 is real (decisions
went from 216k to 148 per solve), the wall-clock impact across the broader
benchmark spectrum was mixed:

Baseline measurements (4 threads, mdd-5.bin, repeat=3-5):

| Benchmark                          | main         | eloquent-bell-merged | Δ        |
|------------------------------------|--------------|----------------------|----------|
| n=18 wz=together mdd-k=5           | 0.07-1.6s    | 1.3-3.8s             | 5x worse |
| n=20 wz=together mdd-k=5           | 0.8-3.3s     | 25-30s               | 8x worse |
| n=26 wz=together mdd-k=5 (bnd/s)   | 0.3 bnd/s    | 1.85-3.22 bnd/s      | 6-9x better |
| n=26 wz=together mdd-k=7 (bnd/s)   | 6.0 bnd/s    | 5.7 bnd/s            | neutral  |
| n=18 wz=apart mdd-k=5              | 0.25-1.7s    | 4-10s (1 miss)       | 5x worse |
| n=20 wz=apart mdd-k=5              | 0.14s ✓      | 30s ✗ (no solution)  | 200x worse|

**Primary benchmark for this work**: `n=26 wz=together mdd-k=5` median
eff bnd/s (4 threads, sat-secs=20).

**Final state after fix-performance-regression branch**: ~1500 bnd/s
at n=26 wz=together mdd-k=5 (**~560× the eloquent-bell-merged baseline**).
All 35 tests pass. n=18-20 find solutions reliably. n=26 mdd-k=7
throughput went from 6 bnd/s (main/eloquent tied) to 1800 bnd/s (300×).

**Performance hypotheses (each ≈ one commit):**

- **F1: SPECTRAL_FREQS reduction** — ACCEPTED. 6.2× speedup. Moved to
  `docs/OPTIMIZATION_LOG.md`. Changed constant from 563 to 17.

- **F2: Cache spectral cos/sin tables across SolveWZ calls** — TRIED,
  rejected. Implemented `WzCombinedSpectral` struct in `PhaseBContext` with
  Arc'd cos/sin/amplitudes + boundary-DFT fallback to `{w,z}_spectral_tables.pos_cos`.
  Result at n=26 wz=together mdd-k=5 (4 threads, 7 runs): 16.43 median
  eff bnd/s vs F1-only baseline 16.47 median — **neutral** (within noise).
  After F1 reduced SPECTRAL_FREQS to 17, the per-boundary table allocation
  is only ~2KB × 3 = 6KB per boundary, and the trig calls are only
  17 × 31 = ~520. The SAT solve time dominates, so avoiding this setup
  cost buys nothing. Reverted.

- **F3: Cache trig values for spectral DFT** — TRIED (as F3a buffer reuse
  in per-lag loop), within-noise improvement (~2.4%). Not decisive
  enough to commit. The per-boundary DFT loop is fast after F1
  (SPECTRAL_FREQS=17).

- **F4: Skip per-lag constraint entirely** — TRIED, rejected.
  Removing the per-lag quadratic PB constraint at n=26 k=7 gives
  +35% bnd/s (1700 → 2300), but regresses n=22 finding rate from
  3/10 to 1/10. The per-lag constraint provides real pruning — it
  just has high setup cost. F9/F12 might be better approaches.

- **F5: Reuse PbSetEq counts via dedup HashSet**: The current
  `if !w_counts.contains(&c) { w_counts.push(c); }` inside a loop is
  O(N²). Use a `HashSet<u32>` or a Vec built then sorted+deduped in
  one shot.
  Single commit: replace the contains-loop with sorted+dedup.

- **F6: Lower per-attempt conflict budget for re-queue** — ACCEPTED.
  93× speedup. Moved to `docs/OPTIMIZATION_LOG.md`. Budget lowered
  from 5k/50k to 20/200.

- **F7: Drop attempt re-queue entirely** — TRIED, rejected. With
  MAX_WZ_ATTEMPTS = 1 (no re-queue), n=26 bnd/s jumps to 3320 but n=20
  finding rate drops from 5/5 to 1/5. The re-queue provides diversity
  (different random phases on each attempt) that's essential when the
  conflict budget (after F6) is only 20. Reverted.

- **F8: Coalesce small per-lag constraints into one**: For very-small
  lags (s near n) the constraint has 0 or 1 terms — trivial. For very
  large lags it can also be tight. The constraint addition overhead
  (HashSet-style dedup of var watchers) is amortised over many calls,
  but several lags have only 2-4 terms. Combine all lags' terms into
  one bigger combined constraint (different `target_lo/hi` per lag is
  a problem — would need to express as N × max_pairs ≤ ... using a
  different encoding).
  Single commit: investigate; may not be feasible without changing
  constraint semantics.

- **F9: Replace the per-lag quadratic PB-range with a leaner "agree
  count" derived constraint**: The current encoding adds two quad terms
  per mid-mid pair `(a,b)` and `(-a,-b)`. The watcher overhead per
  variable scales with the number of constraints touching that variable.
  Instead: for each lag s, allocate one fresh aux var per mid-mid pair
  encoding the XNOR (4 binary clauses), then a single PB constraint on
  the union. This is what `c8a0db5` originally did before being
  rewritten in `b9d92ac`. The commit b9d92ac claimed "20× fewer
  propagations per decision" but also same dec/solve — meaning weaker
  pruning, more work for VSIDS. Reverting to XNOR aux + PB might
  recover the lost pruning.
  Single commit: revert b9d92ac's encoding (or A/B test).

- **F10: Skip the per-lag constraint at lag s where it's trivially
  satisfied**: Compute `combined_lo` and `combined_hi`. If
  `combined_lo == 0 AND combined_hi >= max_possible`, skip. Check the
  current logic — it does have an early-out but maybe too late
  (after building the term lists).
  Single commit: move the trivial-satisfaction check earlier.

- **F11: Remove rules (iv)/(v) middle clauses for small n** — TRIED,
  rejected. Skipping rule iv/v middle clauses at n=26 k=7 gives 1778 bnd/s
  (vs 1791 baseline, within noise) and helps n=20 finding time (1-11s vs
  9-20s) but n=22 finding rate unchanged at 2/10. Canonical clauses add
  little cost so no measurable bnd/s gain. Not worth the canonical-form
  semantic change. Reverted.

- **F12: Re-use combined SolveWZ solver via checkpoint/restore**: The
  per-lag constraints, rules, and spectral tables don't depend on
  per-boundary information for their structure — only the boundary
  contributes constants (agree_const) and signed bnd-mid lit signs.
  Precompute the constraint structure once per (n, m, k), then for
  each boundary push/restore deltas instead of building from scratch.
  Single commit: add SolveWZ template with checkpoint/restore.

- **F13: Reduce SpectralConstraint per-assign cost via SIMD or by skipping
  freqs already at zero**: After `assign`, the `re/im` arrays are scanned
  for conflict. With 563 freqs that's 6 × 563 = 3378 multiplies per
  assign call. Could vectorise; or, if `mr1[fi] == 0`, the freq is
  saturated and could be skipped.
  Single commit: SIMD-vectorise the inner spectral assign loop.

- **F14: SpectralConstraint: store cos/sin as SoA, not interleaved**:
  Currently `cos_table[var * nf + fi]` — accessing all freqs for one var
  is sequential, but accessing one freq for all vars strides by nf bytes.
  The per-assign code does the former (sequential), good. Confirm SoA
  layout and check cache miss rate.
  Investigation only.

- **F15: Move outfix pin handling out of hot path**: Currently every
  SolveWZ iterates `outfix_z_mid_pins` and `outfix_w_mid_pins` even
  when they're empty. Move into a one-shot vec of (var, lit) prebuilt
  at MddCtx creation.
  Single commit: precompute outfix_pins as Vec<i32>.

## April 2026 — Claude session: Z post-hoc pair check optimisation (credit: Claude)

**Baseline (2026-04-17, n=26 wz=apart k=7 30s)**: 520 eff bnd/s, TTC
46.5m. Pipeline funnel: 26K boundaries → 6M Z SAT solutions → 99.997%
fail post-hoc spectral pair check at theta=128 (129 freqs) → 184 reach
XY → 18011 XY SAT solves (100% UNSAT). Per-stage: Z 0 dec/solve (fully
decided at level 0 by SAT spectral 563 freqs); FFT + pair check is the
hot path for the 6M Z solutions.

### S1. Pre-DFT at W's tightest frequencies before Z FFT — *single commit*

99.997% of Z post-hoc rejections happen at frequency `arg max_ω
|W(ω)|² + |Z(ω)|²` where the joint power exceeds `pair_bound`. The
rustfft post-hoc computes Z power at all 129 freqs, then
`spectral_pair_ok` scans them; the FFT itself is non-cancellable.
Replace this with: compute Z(ω) directly via DFT at the K (~3) freqs
where W has highest power; if the pair sum exceeds bound at any of
them, reject without running the full FFT. Direct DFT at K freqs is
~K·n muladds (78 for n=26 K=3) vs ~M log M (~896 for M=128) for FFT.
- **TTC mechanism**: rate (cuts FFT cost on 99.997% of Z solutions)
  and shortfall-neutral (no change to which Z's pass).
- **Detection plan**: `flow_z_pair_fail` rate same; eff bnd/s up.
  Add a counter for "rejected by partial DFT" vs "rejected by full
  FFT" (= 0 when partial DFT is monotone with full FFT).
- **Where to wire**: `src/mdd_pipeline.rs:1977` (the
  `compute_spectrum_into` call after Z SAT returns), and
  `src/spectrum.rs` (add a `spectral_pair_partial_check` function).

### S2. Precompute Z boundary DFT contribution per z_bits — *single commit*

The Z boundary occupies positions `[0..k] ∪ [n-k..n]` and is shared
across all middles for a given `z_bits`. Currently `fill_real_input`
copies the boundary into the FFT input on every Z solution. Cache the
boundary contribution to the DFT at the K constraining freqs (or all
129) per (z_bits) and per worker, lookup instead of recomputing the
boundary part. Saves `2k * num_freqs` muladds per Z FFT. For n=26
k=7: saves 14 * 129 = 1806 muladds, ~10% of the post-FFT work.
- **TTC mechanism**: rate.
- **Detection plan**: eff bnd/s up; new counter
  `z_bnd_dft_cache_hit` (will dominate, 232 hits/boundary average).
- Combine with S1 for largest effect (partial DFT becomes:
  bnd_contrib + middle_DFT, only the middle part computed per Z).

### S3. Drop Z post-hoc when SPECTRAL_FREQS is dense enough — *single commit*

If we increase the SAT's `SPECTRAL_FREQS` (currently 563) to include
the FFT's 129 frequencies (or just go denser), the SAT spectral
constraint already proves `|Z(ω)|² + |W(ω)|² ≤ pair_bound` at those
freqs. Then any SAT-passing Z is guaranteed to pass post-hoc, and the
post-hoc check (FFT + pair_ok) can be skipped entirely.
- **TTC mechanism**: rate (skip 6M FFTs at n=26) but possibly
  offset by denominator (denser SAT grid = more vars forced or
  fewer Z's pass = fewer Z solutions reach post-hoc anyway).
- **Detection plan**: `flow_z_solutions` and `flow_z_pair_fail` both
  drop, eff bnd/s should rise. Risk: the SAT spectral check uses
  f32 cos/sin tables and integer arithmetic — slight numerical drift
  vs FFT's f64 may permit edge-case false-pass at boundary
  frequencies. Verify no regression in the n=18 known-solution test.

### S4. Move Z post-hoc check to use SAT's exact frequency grid — *single commit*

Alternative to S3: instead of FFT post-hoc, do a direct DFT at the
SAT's 563 frequencies. Eliminates the SAT/post-hoc grid mismatch.
`SpectralTables` already has `pos_cos`/`pos_sin` cached at those
freqs (radical/src/lib.rs:343). Use those to compute `|Z(ω)|²` at
the SAT grid — guaranteed redundant with SAT spectral, so post-hoc
becomes a no-op. **Same idea as S3 in different implementation.**

### S1. Pre-DFT at W-tightest bin before Z FFT — *tested, rejected (null)*

Hypothesis: 99.996% of Z solutions fail the post-hoc spectral-pair
check; an O(n) DFT at W's single tightest frequency bin (where W's
budget is smallest, so most likely to fail) would reject most Z's
without ever computing the full O(M log M) rfft.

Implementation: added `dft_magnitude_sq_at_bin` + `argmax_spectrum`
to spectrum.rs; plumbed `w_tight_bin` through `SolveZWork`; in the Z
post-hoc block (mdd_pipeline.rs:1980-2036), compute
`|Z(ω_tight)|² + w_spectrum[tight]` first, `continue` on reject;
only fall back to the full FFT + all-bins pair check on pass.

**Detection counters**: added `flow_z_pair_fail_tight`, reported
alongside `z_pair_fail` in the pipeline-flow block as
`[tight-bin caught N = X%]`.

**Measurement** (n=26 --wz=apart --mdd-k=7 --sat-secs=30):
- Tight-bin rejection rate: 74-75% of all Z pair fails (good!).
- TTC: head-to-head on a warm machine, S5+S1 ran 31.3-35.3m, S5 alone
  ran 30.4-31.9m — S1 is neutral-to-slightly-worse.

**Root cause of the null**: Z SAT runs at 0.0 decisions/solve at
n=26 — every Z is forced at level 0.  Per-item Z SolveZ cost
(5.4M items in 30s ≈ 8.9 µs/item/worker across 16 workers) is
dominated by SAT *setup* (spectral-table attach, `fill_z_solver`,
checkpoint/restore, blocking-clause handling) — NOT the FFT.
Skipping FFTs on 74% of Z's saves real work but doesn't move the
stage's critical path.

**Lever targeting lesson**: "rate" improvements need to hit the
dominant cost, not the most intuitive one.  max_z is already
capped at 16 and only 1.2 Z solutions are returned per item on
average, so S7 (increasing max_z) won't help either — most items
run out of Z candidates before hitting the cap.  The next
productive levers for the Z stage are direct setup-cost reductions:
reusing `SpectralConstraint`'s `re/im/re_boundary/im_boundary`
Vec<f64> allocations across items, or batching items by `z_bits`
so `z_prep` + boundary-DFT are amortized over many `w_vals`.
Reverted; kept in the idea pool below as a building block for a
future "full pair-check via single-bin DFT + on-demand extra bins"
design that skips the full FFT entirely.

**Additional diagnostic findings**:
- `SKIP_Z_SPECTRAL=1` env (bypass `SpectralConstraint` build/attach
  in SolveZ): TTC 30.0/31.2/32.5m vs S5 baseline 30.4/30.5/30.5/31.0/
  31.9m — indistinguishable.  Spectral-constraint setup is NOT the
  dominant cost either.
- Thread scaling (n=26 wz=apart mdd-k=7 20s): 63/261/491/811 eff
  bnd/s at 1/4/8/16 threads → ~80% scaling efficiency at 16 threads
  (13× speedup on 16 cores).  Some contention but not catastrophic.
- TTC variance on this 16-core shared machine is ±5m across 30-s
  samples (baseline 30-35m, noise dominates micro-optimizations
  below ~10% absolute change).

### S5. Reduce SPECTRAL_FREQS for wz=apart — *accepted, TTC −20%*

F1 (wz=together) reduced SPECTRAL_FREQS from 563 to 17 for a 6.2×
speedup. Never measured for `wz=apart`. The trade-off: smaller grid
= cheaper SAT spectral propagation = more rejections leak to
post-hoc = more FFT work. With Z SAT at 0 dec/solve already (fully
forced at level 0), the SAT cost may be dominated by spectral table
allocation rather than per-decision propagation; smaller grid could
still help. **Detection**: sweep SPECTRAL_FREQS ∈ {17, 64, 128, 256,
563, 1024} on n=26 wz=apart 30s and pick the TTC peak.

**Result**: swept 17..1024 then fine-swept 40..128 at n=26 wz=apart
mdd-k=7 30s. Peak at 64 with TTC 37.0m median (5 runs) vs 46.4m
baseline = **−20.3% TTC**. Values 40/100 land in a broad ~38–41m
plateau (all within 4m of the peak); 64 selected for best-validated
central value. Lever: rate (eff bnd/s 520 → ~650–740). Correctness
preserved: n=18 TT finds in <1s; n=20 finds with same variance as
the 563 baseline. See OPTIMIZATION_LOG.md §S5 for the full table.

### S6. Sort pair_ok freq order by W's power (descending) — *single commit*

`spectral_pair_ok` walks freqs 0..129 in order. Most pair fails
happen at freqs where W has high power. Sort the freq indices once
per W (after W FFT), then iterate Z+W in that order — early-exit
triggers on the first iteration in 99% of cases instead of on
average half-way through.
- **TTC mechanism**: rate (smaller, but composable with S1).
- **Detection plan**: micro-bench: count avg `i` at which
  `spectral_pair_ok` returns false.

### S7. Increase max_z above 1 to amortise per-boundary fixed cost — *single commit*

Currently `max_z = 1` (forced cap, `src/mdd_pipeline.rs:` analogous
to old `src/main.rs:2545`). At n=26 the Z SAT call is essentially
free (0 dec/solve), but the SolveZ stage's *fixed* setup cost
(z_prep rebuild, spectral table attach, fill_z_solver_quad_pb) runs
per item regardless. With max_z>1 we'd amortise that setup over
multiple Z's. Risk: post-hoc rejects 99.997%, so extra Z's are
likely waste. Only worthwhile if z_prep/setup is a meaningful
fraction of per-Z time. **Detection**: sweep max_z ∈ {1, 2, 4, 8}
on n=26 wz=apart 30s; watch eff bnd/s and Z solves/s.

### S8. Skip W spectral when boundary contribution alone exceeds bound — *single commit*

Some W boundaries have `|DFT_W_bnd(ω)|² > individual_bound` at some
ω. No middle can reduce that (the middle adds ≤ middle_m² to the
DFT magnitude). Pre-compute W boundary DFT, find the per-freq
boundary power, reject the entire SolveW if the boundary is hopeless
at any ω. Saves the 1477 W middle FFTs for that boundary.
- **TTC mechanism**: rate (eliminates futile SolveW work) and
  denominator (fewer W solutions emitted to SolveZ).
- **Detection plan**: `flow_w_unsat` count; eff bnd/s.

### S9. Direct DFT at top-K boundary-peak freqs in SolveW — *single commit*

Same as S1 but for W: pre-compute W boundary's top-K freqs (those
where boundary alone has high power, hence W middle most likely to
fail). For each W middle, compute power at those freqs via direct
DFT (with cached boundary contribution); reject if exceeds
individual_bound. Saves FFT cost on the 82% rejected W middles.
- **TTC mechanism**: rate; W reject rate already high (82%) so
  direct savings.
- **Caveat**: brute-force W path uses `spectrum_into_if_ok` which
  already early-exits at first violating freq. Improvement comes
  from skipping the FFT entirely for early-rejectable W's.

### S10. Skip extension cache lookup for already-walked (Z,W,X,Y) sets — *single commit*

The `ext_cache: HashMap<u128, bool>` (src/mdd_pipeline.rs:2116)
records per-worker extension results. With workers sharing the same
boundaries indirectly, the same cache key may be computed in multiple
workers. Switch to a process-wide `DashMap<u128, bool>` so the work
is done once globally. Risk: contention may exceed savings; the
per-worker cache hit rate is already high (the 4312 prunes /22323
candidates ≈ 19%). Measure.

## N-series: boundary throughput and pipeline balance (April 17 2026, Claude)

Observation from fresh baseline measurements (`--wz=apart` on current
container, 16 threads):

- n=26 mdd-k=7 sat-secs=60: TTC = **45.4 m**, 526 eff bnd/s, XY
  timeout 0.0%, `flow_w_spec_fail` = 82.7% of W solutions, `flow_z_pair_fail`
  = 99.996% of Z solutions, W dec/solve ~0 (brute-force path: middle_m = 10).
- n=56 mdd-k=10 sat-secs=60: TTC = **114883 d**, 0.27 eff bnd/s,
  only **16 boundaries** walked in 60s because every W solve is a SAT
  path doing ~12M decisions per solve (W middle_m = 34, SAT loop runs
  until UNSAT → blocking clauses force it through huge UNSAT proofs).
  `flow_w_solutions` = 127k across 16 boundaries = 8000 Ws per boundary.

Big picture: at n=56 the pipeline has an unbalanced W stage that
monopolises every worker. None ever reach SolveZ/XY. Some of these
ideas pull the W stage back into budget so the rest of the pipeline
can run.

### N1. Cap W enumeration per boundary in SAT path — **LANDED**

At middle_m > 20 the W SAT loop (`src/mdd_pipeline.rs:1055`) calls
`w_solver.solve()` in an unbounded loop, adding a blocking clause after
each solution. At n=56 each boundary produces ~8000 Ws over ~4s
wall-clock, and ~82% fail the post-hoc spectral filter anyway. Analogue
to `max_z: cfg.max_z.min(16)` at line 518.

- **TTC mechanism**: rate — frees the worker to process new boundaries.
  Each capped boundary still produces 16–32 (Z, W) pairs to XY-check,
  which is plenty of coverage at n=56.
- **Detection plan**: `stage_exit[0]`/s (boundaries walked) should
  rise significantly; `stage_exit[1]`/s should fall (fewer W solutions
  per boundary) but `stage_exit[0]` dominates TTC. Watch `eff bnd/s`.
- **Risk**: capping W may leave the pair spectral filter unable to
  find good (Z, W) pairs → higher XY UNSAT rate. Not a soundness risk;
  just need to verify the W cap doesn't starve downstream XY SAT of
  work.

**Result (on top of main @ 1316047 which includes F1
`SPECTRAL_FREQS 563→64`)**: at n=56 `--wz=apart --mdd-k=10` 60s,
boundaries walked 34→730 (21×), `eff bnd/s` 0.57→12.16 (21×),
TTC 53923d→2509d (**21.5×**). Env override:
`TURYN_MAX_W_PER_BND=<N>`. See OPTIMIZATION_LOG.md "N1+N2".

### N2. W and Z SAT conflict budget per solve — **LANDED**

Set a conflict limit on each W and Z `solver.solve()` call, same as XY
already does for n>30. At n=56 the per-solve average was into the
millions of decisions — most of those are wasted UNSAT proofs, and
without a limit a single pathological solve could block shutdown past
`sat_secs`.

- **TTC mechanism**: rate (+ makes runs cleanly measurable).
- **Detection plan**: `flow_w_decisions/flow_w_solves` drops;
  `stage_exit[1]`/s rises; `eff bnd/s` goes up; `sat_secs` expiry
  now leads to clean exit.
- **Risk**: a too-tight budget kills SAT diversity. Default 5000
  matches the XY n>30 pattern; override via `TURYN_W_CONFL` /
  `TURYN_Z_CONFL`.

**Result**: default 5000 combined with N1 gives the 21× TTC win
recorded under N1 (mostly attributable to N1; N2 is the
testability / shutdown-soundness piece).

### N3. Share SolveZ "pair check" with W spectral filter

Today: W passes post-hoc spectral (individual bound) → goes to Z SAT →
every Z solution is then FFT-ed and passed through `spectral_pair_ok`.
99.996% fail at this step. If we computed the W's spectrum once and
used `pair_bound - |W(ω)|²` as a tighter per-freq bound inside the Z
SAT solver (already implemented as `per_freq_bound` in
`src/sat_z_middle.rs`), the Z SAT would reject most of these without
producing a solution.

- **TTC mechanism**: rate (Z stage gets cheaper) + denominator (fewer
  Z solutions reach the pair filter).
- **Detection plan**: `flow_z_solves` drops sharply; `flow_z_pair_fail`
  drops; `stage_exit[2]`/s rises.
- **Verification needed**: is this *already* active? Read
  `src/sat_z_middle.rs` and confirm. If it is, then this idea is
  already done; if not, wire it.

### N4. BDKR rules (ii)–(vi) enforced at MDD build time

Today rules (ii)–(vi) are enforced only via SAT unit propagation in
XY/W solvers. At MDD build the MDD still contains live ZW paths whose
W would be rejected by rule (v) at SAT time. Enforcing the rules
directly in the MDD (as boundary-rule-v / iv pre-filters during the
ZW-first MDD build) shrinks `live_zw_paths` directly.

- **TTC mechanism**: denominator — smaller live ZW path count.
- **Detection plan**: `mdd.count_live_paths()` delta before/after;
  TTC should drop by the ratio.
- **Risk**: soundness — if we mis-encode a rule, we lose the
  canonical TT. Required check: `known_tt26_verifies` regression
  test.

### N5. Adaptive gold/work queue ratio

Current dual queue hard-codes a coinflip between XY (gold) and
upstream (work). At n=56 the work queue is backlogged with SolveZ
items but the XY queue drains fast; at n=26 the opposite may be true.
Monitor thread adjusts the ratio based on queue sizes.

- **TTC mechanism**: rate — better worker utilization.
- **Detection plan**: `stage_exit[3]/elapsed` rises uniformly
  through the run; workers spend less time on cheap stages.

### N6. Per-freq W rejection using full tuple sum_w

Currently W spectral filter uses `individual_bound = 3n-1` (optimal
under the pair identity). But for a *specific tuple* with fixed
`σ_Z, σ_W`, the sum tuple also fixes `σ_X, σ_Y` — and therefore
`|X(0)|² + |Y(0)|² = σ_X² + σ_Y²`. This tightens `|Z(0)|² + |W(0)|²`
below the generic pair bound at ω=0. At other frequencies the bound
doesn't tighten, but every frequency counted reduces false-positive
W solutions.

- **TTC mechanism**: denominator + rate — fewer W solutions reach
  the Z stage.
- **Detection plan**: `flow_w_spec_pass` drops with no regression
  in `flow_xy_sat`.
- **Risk**: tuple-specific filtering may reject some boundaries
  that have a legitimate other-tuple match. Need to preserve
  canonical coverage.

### N7. Eager XY item emission from SolveZ batch

Today SolveZ → emits one XY item per Z solution. If we batch
multiple Z solutions against the same W and emit a single XY item
that iterates them internally, we avoid per-Z queue lock overhead.

- **TTC mechanism**: rate.
- **Detection plan**: no direct counter; measure via `eff bnd/s`.
- **Risk**: changes the work-stealing dynamics, may actually slow
  down overall (monitor needs even units of work for load-balancing).

### N8. Conflict limit retest at n=56 (tier-3 #9 retry)

`set_conflict_limit(5000)` for n>30 was tuned on xy/s, not TTC.
Sweep `{2k, 5k, 10k, 20k, 50k}` at n=56 mdd-k=10 sat-secs=60 and
record TTC, `flow_xy_timeout/flow_xy_solves`, and `eff bnd/s`. Watch
for a TTC win that higher budgets provide via reduced shortfall.

- **TTC mechanism**: shortfall.
- **Detection plan**: TTC vs budget curve.

### N9. mdd_extend retest at n=26 and n=56 (tier-3 #11 retry)

`mdd_extend=1` was accepted on +28% bnd/s. Sweep
`{0, 1, 2, 3}` on TTC (not bnd/s) to confirm.

- **TTC mechanism**: denominator (higher extend = more pruning) vs
  rate (higher extend = more per-candidate work).

### N10. max_z cap retest at n=56 (tier-3 #8 retry)

`max_z` currently capped at 16 (src/mdd_pipeline.rs:518). Re-sweep
`{1, 4, 8, 16, 32, 64}` at n=56 mdd-k=10. Note comment says measured
sweep was at n=26 k=3, which is a very different profile — at n=56
k=10, cheap Z per boundary prep may amortise better with a higher
cap.

### N11. Incremental spectral filter in XY SAT

The Z SAT solver already has `SpectralConstraint` to enforce
`|Z(ω)|²  ≤ pair_bound - |W(ω)|²` per-frequency. The XY SAT solver
does NOT — it relies on the post-facto spectral pair check at the
XY output to reject bad assignments. Adding `SpectralConstraint` on
XY (with `pair_bound - |Z(ω)|² - |W(ω)|²` as the per-freq bound) would
prune XY assignments that blow the Parseval budget during search.

- **TTC mechanism**: shortfall + rate.
- **Detection plan**: `flow_xy_decisions/flow_xy_solves` drops;
  `flow_xy_timeout` drops at large n.
- **Risk**: the spectral constraint is pair-dependent, so must be
  rebuilt per (Z, W) candidate — cheap if the `SpectralTables` can
  be shared via Arc.

### N12. Skip SolveZ when XY sub-MDD is empty

Today the MDD-guided tuple fail-fast (G8, `any_valid_xy`) happens at
SolveW / Boundary time. But `xy_root` is available at SolveZ too. If
after fixing Z the XY sub-MDD is empty, we know the pair can't
produce an XY. Pre-check before entering SAT.

- **TTC mechanism**: rate — skip Z SAT for dead tuples.
- **Detection plan**: `flow_z_solves` drops; `flow_z_pair_fail`
  unchanged; `eff bnd/s` rises.

### N13. Monitor thread bumped at n=56

Today the monitor sleeps between dispatches. At n=56 where
boundaries are the limiting resource (workers stuck in W SAT
because monitor hasn't dispatched enough), a faster monitor thread
may help.

- **TTC mechanism**: rate.
- **Detection plan**: `stage_exit[0]` rises as monitor dispatches
  more boundaries per second. Tricky — can't improve if workers
  can't process what they have.

### N14. Precompute and cache W boundary DFT contribution

W SAT builds `SpectralConstraint::from_tables(wtab, &w_boundary,
individual_bound)` once per boundary, which recomputes
`boundary_dft` every time. If two boundaries share prefix/suffix
bits, the per-prefix contribution can be cached.

- **TTC mechanism**: rate — per-boundary setup cheaper.
- **Detection plan**: indirect; measure via `stage_exit[1]/elapsed`
  (SolveW throughput) net of the setup cost.

### N15. Deprioritise boundaries where sub-MDD is tiny

The MDD walker produces boundaries in LCG order. Some boundaries
have very few live (x, y) extensions; these produce little XY
coverage per W/Z work done. Monitor could use `any_valid_xy` count
as a priority signal.

- **TTC mechanism**: rate.
- **Detection plan**: `eff/elapsed` curve should be steeper early
  when we prioritise "bigger payoff" boundaries.
- **Risk**: we still need to walk every boundary eventually for
  completeness — this is purely a *rate* win (same denominator,
  better rate shape).

## S-series: `--wz=sync` walker optimisation (April 18 2026, Claude)

Baseline (n=26 `--wz=sync` sat-secs=60, 16 workers):
- nodes=3.6M, rate 60k nodes/s, max_lvl=25/26, 0 leaves
- memo_hits=**0** (memoization is dead code on every benchmark we've run)
- rule_rejects=**0** (walker-side rule check catches nothing; SAT handles it)
- avg_nogood 70.9/70.6 (**1.00× shrink** — 1-UIP produces nothing)
- cap_rejects=48M (dominant pruner), tuple_rejects=1.4M, sat_unsat=1.6M
- b_eff levels 0..5 all = 1.0 (deterministic — every worker re-walks them)
- peer_imports=416 (tiny cross-worker clause exchange)
- projected TTC 3.8s parallel, but 60s real time never finished. Projection
  overestimates because early b_eff=1 dominates the geometric mean.

The hot inner loop per DFS node runs 16 times (once per choice of
(X, Y, Z, W) sign tuple at `pos_order[level]`): build Cand with cloned
assumptions, speculatively set bits, rebuild_sums (O(n²)), check capacity /
tuple-reachable / rules, rollback, rebuild_sums again. Then for the
accepted siblings: `propagate_only(&state.assumptions)` (re-asserts every
ancestor assumption), optionally harvest forced bits, insert into memo
(never queried), recurse.

### S1. Remove the dead memoization

`memo_hits=0` on every run we've measured (n=18, 22, 26). Removing memo
drops: (a) `compute_signature`'s hash of `state.level` × 4 bits per
call (O(level) per DFS call), (b) FxHashMap insert, (c) the entire
`memo` HashMap allocation. Net win: per-node cost drops with no
pruning lost.

- **TTC mechanism**: rate.
- **Detection plan**: `nodes_visited / elapsed` rises; `memo_hits`
  remains 0 (confirmed dead); TTC (projected_parallel) should drop
  by the same ratio.
- **Risk**: none — `memo_hits=0` is proof the map is write-only.
  Should still keep the hash signature mechanism in the tree for
  potential future coarser memoization (S8 below).

### S2. Avoid cloning state.assumptions per candidate

`dfs()` builds `Cand { assum: state.assumptions.clone() + new_assums,
... }` for every sibling. At depth L the assumption list is ~4L lits;
with 16 siblings per node, that's 64L i32 allocations per node. At
n=26, ~50 MB/s of churn once the walker is deep. Replace by storing
only the `new_assums` (≤4 lits, fits in inline array) and
reconstructing full assumptions from `state.assumptions` at child
entry via `truncate + extend_from_slice`.

- **TTC mechanism**: rate.
- **Detection plan**: `nodes_visited / elapsed` rises; check with
  `perf` that `Vec::allocate` in candidates ranking falls.

### S3. Skip speculative rebuild_sums — compute score from delta

Current code: for each candidate, set bits, `rebuild_sums` (O(n²)),
compute capacity+score, unset bits, `rebuild_sums` again to parent
state. Two full O(n²) sweeps per candidate × 16 candidates × every
node. Replace with: keep parent-level sums unchanged; for each
candidate, compute a `sums_delta` from `closure_events[level]` using
the candidate's placed bits (O(|events at this level|)); add/subtract
for checks; no global rebuild. Same savings on the post-SAT harvest
path by incrementally updating.

- **TTC mechanism**: rate (large — rebuild_sums is in the innermost
  loop and does O(n²) work).
- **Detection plan**: nodes/s should rise; per-node elapsed (via
  `perf stat -e cycles,instructions`) should drop meaningfully.

### S4. Partition first deterministic levels across workers

b_eff=1 for levels 0..5 means all 16 workers re-walk the same prefix.
Pre-compute the single forced path through levels 0..L* (where L* is
the first branching level) once, then dispatch workers from there
with distinct first-branching assignments. Equivalent to doing a
single serial walk until the first branch, then parallelising.

- **TTC mechanism**: rate (stop wasting 15/16 × prefix work).
- **Detection plan**: `nodes_visited / elapsed` aggregate should
  rise by ~15/16 when prefix is forced; the `nodes_by_level[0..L*]`
  should be 1 per worker rather than ~1 per worker × 16.
- **Risk**: workers need distinct starting assumptions; need to
  emit N work-items (one per first-branching sibling) to a shared
  queue and let workers pull.

### S5. Raise cross-worker nogood-share threshold

`MAX_SHARED_LEN: usize = 16` in `dfs()`. Measured avg nogood len is
~70; basically nothing gets shared. Try raising to 256 (or: share
unconditionally and let the solver DB evict). Peer clauses prune
repeat deadends across different workers — this is literally the
mechanism that makes parallel CDCL scale.

- **TTC mechanism**: rate (bigger peer clause flow → fewer
  redundant SAT-UNSAT calls across workers).
- **Detection plan**: `peer_imports` should rise 10–100×; `sat_unsat`
  should drop; need to verify no regression in nodes/s from added
  clause-DB overhead.
- **Risk**: long clauses rarely fire via two-watch and bloat the DB.
  If regression, add a heuristic: share clauses with short LBD
  regardless of length.

### S6. Remove `compute_sigma` O(4n) sweep from tuple_reachable

`tuple_reachable` is called in the speculative-candidate loop and
calls `compute_sigma` which scans all 4 sequences × n positions
looking at every bit. We can maintain sigma/free incrementally per
sequence and update on bit set/unset.

- **TTC mechanism**: rate (cuts per-candidate cost).
- **Detection plan**: nodes/s rises.

### S7. Skip `propagate_only` when new bits are only deterministic

When the just-placed bits are all forced by already-present SAT
constraints (e.g., the placement matches what the parent's
`harvest_forced` predicted), we know `propagate_only` would be a
no-op and just re-assert ancestor assumptions. Detect this via a
"would-be-forced" check before calling propagate_only.

- **TTC mechanism**: rate.
- **Detection plan**: `sat_unsat` unchanged; nodes/s rises.
- **Risk**: has to be sound — if we skip propagate_only we're
  trusting walker pruning to be equivalent. Gated on
  harvest_forced's prediction matching the placement.

### S8. Coarser memo key — (level, sums, rule_state) only

Current signature also hashes walker-placed bits, which means every
DFS path is unique and memo never fires. If we drop the bit hash,
different sibling orderings that reach the same (sums, rule_state)
at the same level would short-circuit. But: two placements with the
same (sums, rule_state) may still differ in feasibility because
harvest_forced's set of forced bits differs. Need either (a) a
soundness proof that (level, sums) determines feasibility, or (b)
a weaker guarantee — memo only the "UNSAT" outcomes (they're always
safe to cache by sums).

- **TTC mechanism**: rate (denominator on revisit paths).
- **Detection plan**: `memo_hits` rises; `sat_unsat` drops.
- **Risk**: soundness — must not prune feasible states. Start with
  UNSAT-only memo for safety.

### S9. Incrementally maintain sums instead of rebuild_sums

Store sum deltas per level in a stack so descent = add delta,
backtrack = subtract delta. Replaces all three `rebuild_sums` calls
in the dfs (top-of-sibling-loop, speculative, post-harvest) with
O(events at this level) updates.

- **TTC mechanism**: rate.
- **Detection plan**: nodes/s up; function-level profile shows
  `rebuild_sums` disappearing.
- **Status**: subsumed by S3 if implemented carefully.

### S10. Swap `solve_with_assumptions` at leaf for `propagate_only`-plus-model-extraction

At the leaf (level==depth), code calls `solver.solve_with_assumptions`
to validate. At depth≥18 we've already filtered with capacity/tuple
and propagate_only; the full solve is redundant work (harvesting the
model only). Replace with `propagate_only` + `solver.value()` calls.

- **TTC mechanism**: rate — leaves are rare but each full solve costs
  ms+. However leaves reached ≤1 at n=26 baseline, so impact is small
  unless we also fix TTC.
- **Detection plan**: `leaves_reached` unchanged; elapsed lower when
  leaves are actually reached.
- **Risk**: model extraction requires the solver to have the full
  assignment. If propagate_only didn't force all lits, we need a
  separate model-completion step.

### S11. Delete unused `dynamic_capacity_violated` hot path

`dynamic_capacity_violated` runs after every accepted child's SAT
propagate. It's O(n²) and checks a tighter bound than
`capacity_violated`. But with the static max_remaining bound already
catching 48M/node ratio, the dynamic check may never fire. Measure
its contribution: run with dynamic check removed; compare
`cap_rejects` delta. If delta ≈ 0, remove it entirely.

- **TTC mechanism**: rate.
- **Detection plan**: `cap_rejects` unchanged; nodes/s rises.

### S12. Test `--no-xor` on sync walker

Sync's SAT config uses the default (XOR + QuadPB + spectral where
applicable). propagate_only is called per DFS node, and on every call
all three propagators re-fire across all re-asserted assumptions.
XOR propagation is heavy. Unclear if it's necessary for the Turyn
identity once QuadPB is active. Try toggling.

- **TTC mechanism**: rate if XOR is unnecessary; regression if it's
  catching what QuadPB can't.
- **Detection plan**: `sat_unsat` stays similar (or drops slightly
  from slower propagation); nodes/s rises.
- **Risk**: none (gated by config).

### S13. Pre-compute and cache the level-0 propagated solver

All workers build the same base solver via `build_solver`. Building
the solver with quad PB and Tseitin chains takes ~10-50ms per worker.
Build once in `search_sync_parallel`, then `Clone` the solver into
each worker. Currently `Solver` is not `Clone`, but the walker's
base clause set is constant across workers — can clone the core DB.

- **TTC mechanism**: rate (faster startup; matters for short runs).
- **Detection plan**: only visible on short runs; TTC-relevant at
  small sat-secs.
- **Status**: low-priority unless we also lean on restart churn.

### S14. Early exit the sibling loop when a rule just fired

If check_rules on the first few accepted candidates resolves the
same rule (RULE_II / RULE_IV / RULE_V), later candidates likely fail
the same rule check. Currently we enumerate all 16 candidates
regardless. Cache "rule fired at this level by early-bit=X" and
skip any candidate that'd re-fire with an inconsistent early bit.

- **TTC mechanism**: denominator (fewer candidates per node).
- **Detection plan**: `candidates.len()` avg drops; nodes/s stays flat
  but per-node effective work drops.

### S15. Adaptive per-worker sibling-sort randomness

Worker 0 is best-first (seed=0 → score-sorted), workers 1..15 fully
random. Middle ground: workers 1..15 do epsilon-greedy (best-first
with probability `1-ε`, random otherwise). At ε=0.1 they follow the
gradient most of the time but diverge onto different paths
occasionally — more likely to find leaves than pure random.

- **TTC mechanism**: rate (faster leaf discovery → earlier first
  solution).
- **Detection plan**: `time_to_first_leaf` should drop.
- **Risk**: on UNSAT-complete search this is neutral (still need
  to cover tree); purely a find-solution-faster optimisation.

## R-series: radical vs CaDiCaL feature-by-feature (April 19 2026, Claude)

Baseline recorded at session start (n=26, 16 threads, 60s budget,
`runsc`, commit `3484b54`):

- `--wz=apart --mdd-k=7`: TTC 37.8 min parallel, 629 eff bnd/s,
  1.47M live ZW paths, 0 % XY timeout.
- `--wz=sync`: direct TTC ≈ 6.76e8 s parallel (~21.4 y), ~51k
  nodes/s, 3.1M nodes, 40.6M cap_rejects, 0 leaves at max_lvl=25.
  Per-feature forcings: **clause 77.8 % / quadpb 21.7 % / pbseteq
  0.4 %**.
- `--wz=cross`: at 60 s budget the producer is still streaming Z/W
  candidates; 0 boundaries walked → TTC "infd". Not a usable
  baseline at this budget for this session.

Sync is ~3e5× worse TTC than apart at n=26. CaDiCaL comparison (agent
Explore report) identified 5 gaps in `radical` relative to CaDiCaL
that plausibly help a `propagate_only`-dominated workload:

1. **Chronological backtracking** (CaDiCaL SAT'18 signature) — keep
   shallow-level literals on the trail across conflicts.
2. **Dedicated binary clause list** — CaDiCaL's `bins` index lets
   binary propagation skip the general 2WL scan.
3. **LBD-tiered clause retention (glue)** — keep `glue ≤ 2` forever;
   radical currently deletes by age only.
4. **On-the-fly subsumption during learning** — radical adds the
   learnt nogood without checking if it subsumes or is subsumed.
5. **Hyper-binary resolution (HBR) during probing** — derive binary
   clauses eagerly to densify the implication graph.

The highest-leverage lever I can see in the existing
`radical::propagate_only` code (`radical/src/lib.rs:1723`):

> **Every `propagate_only(&assumptions)` call backtracks to
> decision level 0 and re-enqueues every literal in the assumption
> list as a fresh decision.** Sync's DFS sibling loop calls
> `propagate_only(state.assumptions)` with a prefix of ~4L literals
> that is identical across all 16 siblings at this node, differing
> only in the last 4 lits. We pay full O(L) re-propagation 16 times
> per node.

This is by far the most promising single commit for `--wz=sync`
rate.

### R1. Incremental assumption propagation (push/pop frames)

Expose `push_assumption_frame(&[Lit]) -> Option<bool>` and
`pop_assumption_frame()` on `radical::Solver`. `push` pushes the new
lits at `decision_level + 1`, propagates, returns Some(true) / Some
(false); `pop` backtracks one level. Sync's DFS:

```
// on entering level L, after filtering candidates:
solver.push_assumption_frame(&cand.new_assums[..n]);
// ... harvest, recurse ...
solver.pop_assumption_frame();
```

- **TTC mechanism**: rate — propagation cost per node drops from
  re-asserting 4L lits to propagating 4 lits. Expected 5-20×
  speedup on the `propagate_only` call alone.
- **Detection plan**: `clause` forcing rate (per-second) rises ~5–
  20×; `nodes_visited/elapsed` rises; `avg_nogood` size should be
  stable; `sat_unsat` per second rises.
- **Risk**: must guarantee pop matches push; learnt clauses that
  fire within an assumption frame must be consistent with being
  popped. Existing `solve_with_assumptions` path is unaffected.

### R2. Dedicated binary clause list in radical

Maintain a `Vec<Vec<Lit>>` (per-literal `bin_implications`) in
addition to the general 2WL. During `propagate()`, when a literal
`l` is enqueued, walk `bin_implications[index(l)]` first — each
entry implies a single other literal, zero overhead.

- **TTC mechanism**: rate. 77.8 % of sync's forcings are `clause`;
  a large fraction are binary (Tseitin chains, BDKR rule
  encodings, learnt unit-like nogoods). Separate-path binary
  propagation is a known ~1.2–1.5× solver speedup.
- **Detection plan**: `clause` forcings/sec ↑, total forcing count
  unchanged, nodes/s ↑.
- **Risk**: have to keep the bin list consistent with clause DB
  deletions and the clause arena. Needs a `Clause::is_binary()`
  short-circuit in `reduce_learnt`.

### R3. LBD-tiered learnt clause retention

On learning, compute `lbd = #distinct decision levels in the
clause`. Tag the clause `Tier1` if `lbd ≤ 2`, `Tier2` if `lbd ≤ 6`,
`Tier3` otherwise. `reduce_learnt` never evicts Tier1; preserves
Tier2 until size/2 pressure; evicts Tier3 aggressively.

- **TTC mechanism**: rate — high-quality propagators persist across
  the sync walker, so the same state's conflict is cheaper the
  second time.
- **Detection plan**: `clause` forcing count rises (more short
  clauses firing); `peer_imports` may rise; nodes/s ↑.
- **Risk**: clause DB grows until cap is raised; watch RSS.

### R4. Preload walker-infeasible tuples as solver nogoods

Phase-A enumerates sum tuples `(σ_x, σ_y, σ_z, σ_w)`. The walker
checks `tuple_reachable(state)` after each speculative placement
and rejects infeasible branches with `tuple_rejects`. If we
encode those tuple constraints as native solver clauses (one
PbSetEq per sequence's target sum, plus a disjunction over
allowed tuples), the CDCL branch ordering + VSIDS gets to use
them.

- **TTC mechanism**: denominator (fewer siblings reach the SAT
  stage) + rate (solver can cut earlier).
- **Detection plan**: `tuple_rejects` drops; `sat_unsat` rises
  proportionally; TTC ≈ no change unless the SAT prunes earlier
  than the walker's capacity check.
- **Risk**: sync already attaches Phase-A sum PbSetEq (see
  sync_walker.rs) — verify these are wired in before claiming an
  easy win. If they are, R4 is already landed in a weaker form
  and moves to "verified".

### R5. Session benchmark: `--no-xor` on `--wz=sync` (S12)

Just run `target/release/turyn --n=26 --wz=sync --sat-secs=60
--no-xor` and compare TTC, nodes/s, per-feature forcing
breakdown. No code change; pure measurement. If XOR propagation
has negative marginal value on sync (which is plausible — quad PB
already enforces the Turyn lag identity), removing it frees
propagation budget.

- **TTC mechanism**: rate if XOR is net-overhead; regression if
  it's net-positive.
- **Detection plan**: per-feature `xor` forcings should drop to 0;
  `clause`/`quadpb` unchanged or up; nodes/s ↑ or ↓.

### R6. Raise sync's `MAX_SHARED_LEN` 16 → 64 (S5 concrete)

In `src/sync_walker.rs`, change `const MAX_SHARED_LEN: usize = 16;`
to 64. avg_nogood len at baseline is ~71; current threshold
filters out essentially everything.

- **TTC mechanism**: rate (cross-worker nogood flow increases).
- **Detection plan**: `peer_imports` should rise 10–100×;
  `sat_unsat` should drop in aggregate.

### R7. Delete dead `dynamic_capacity_violated` (S11 concrete)

Verified dead: defined at `src/sync_walker.rs:687`, never called.
Simple cleanup; removes a dead-code warning. Zero TTC impact
expected, filed for measurement discipline.

- **TTC mechanism**: rate (micro; instrumentation).
- **Detection plan**: `cap_rejects` unchanged; warning disappears.

### R8. Incremental sum maintenance (S3/S6/S9 consolidated)

Replace the three `rebuild_sums` calls per candidate with a delta
stack: at each level, precompute `sums_delta_by_bit[level][bit]`
(the 4-bit sigma deltas if we place each of the 4 kinds with
sign). Candidate loop: for each choice, add 4 deltas; on
reject/accept/rollback, subtract or stay.

- **TTC mechanism**: rate — `rebuild_sums` is O(n²) on n=26; delta
  is O(4).
- **Detection plan**: nodes/s ↑ by a visible margin in profiling
  (expected 15–30 % at n=26).
- **Risk**: easy to get off-by-one; add a debug-only `assert_eq`
  against `rebuild_sums` under `cfg(test)`.

### R9. Early sibling-loop exit when a BDKR rule just fired (S14)

Cache "rule X fired with early-bit Y at level L"; later siblings
at the same level with the same early-bit skip the rule check and
skip directly. Cheap denominator filter.

- **TTC mechanism**: denominator.
- **Detection plan**: `rule_rejects` unchanged, avg candidates
  processed per node drops, nodes/s stable.

### R10. Epsilon-greedy sibling order on workers 1..N (S15)

Replace workers 1..N's fully-random ordering with ε-greedy (best-
first with probability 1-ε; ε=0.1). Diverges enough to explore
different regions but exploits the score heuristic for bulk of
choices.

- **TTC mechanism**: rate (time-to-first-leaf).
- **Detection plan**: `time_to_first_leaf` drops; TTC unchanged
  for UNSAT-complete coverage.

### R11. Probe the first branching level once per search (S4)

Pre-walk levels 0..L* (where L* is the first branching level —
measure with `nodes_by_level / children_by_level`) serially once,
then dispatch workers at L* with distinct first-branch
assignments via a shared queue. Avoids 15/16 × prefix work.

- **TTC mechanism**: rate.
- **Detection plan**: `nodes_by_level[0..L*]` drops to 1 per
  worker instead of ~1 per worker × N.

### R12. UNSAT-only coarser memo (S8 concrete)

Memoize only the UNSAT verdict keyed by `(level, sums, rule_state)`
(drop the walker-bits dimension). Sound because UNSAT at this key
holds regardless of which bits led here, provided rule_state
encodes BDKR state. Re-entering the same key at a later sibling
returns UNSAT immediately.

- **TTC mechanism**: denominator.
- **Detection plan**: `memo_hits` > 0; `sat_unsat` drops.
- **Risk**: soundness proof needed — rule_state must be a
  complete summary of BDKR enforcement at this level.

### Ranking of R-series by expected TTC leverage

Top 3 likely wins (single-commit feasible):
- **R1** (incremental assumption propagation): biggest rate lever;
  theoretically ~5-20×. Medium complexity.
- **R8** (delta sums): solid rate lever; low complexity.
- **R6** (MAX_SHARED_LEN 16→64): trivial; rate lever via peer flow.

Low-risk quick tests to run first:
- **R5** (`--no-xor` measurement): no code.
- **R7** (delete dead fn): cleanup.
- **R6** (1-line const change): trivial.

### R-series results (this session, April 19 2026)

Clean n=26 `--wz=sync --sat-secs=60` baseline (16 threads, `runsc`,
MAX_SHARED_LEN=16): **noise floor ~11 %** over 3 back-to-back runs
(TTC 6.79e8, 6.78e8, 7.54e8 → mean 7.03e8). Need ≥15 % TTC move to
call a win decisively on a single 60 s run.

- **R5 (`--no-xor`)**: direct TTC 6.58e8 s vs baseline 6.67e8 s
  (-1.4 %), nodes/s +3 %. **Within noise — rejected.** Per-feature
  forcing shape unchanged (baseline already shows `xor=0` lines
  suppressed — XOR propagator fires but forces nothing visible at
  telemetry granularity). Keep XOR on; no benefit demonstrated.

- **R6 @ MAX_SHARED_LEN=64**: peer_imports 416 → 3.64M (8800×),
  nodes/s −20 %, direct TTC +2 % (6.81e8). Long clauses via
  2WL are net overhead. **Rejected.**

- **R6 @ MAX_SHARED_LEN=32**: peer_imports 416 → 592 (essentially
  unchanged — baseline noise), nodes 3.94M → 2.60M, direct TTC
  7.70e8 s. Regression falls inside the noise envelope; no signal
  of benefit. **Rejected.**

The 2WL architecture in `radical` penalises long shared clauses
(clause DB scans grow and most never fire). A smarter share
policy — e.g., share only if `lbd ≤ 2` regardless of length — is
the right follow-up, but requires glue tracking first (see R3 or
CaDiCaL's tier retention).

- **R7 (delete dead `dynamic_capacity_violated`)**: deferred —
  `grep` confirms it's never called; removing is pure cleanup and
  should not move TTC. Not committed this session.

- **R1 (incremental assumption propagation)**: **ACCEPTED — TTC
  −20.6 % decisive (12 σ).** Exposed
  `push_assume_frame(&[Lit])` / `pop_assume_frame()` /
  `current_decision_level()` on `radical::Solver`
  (`radical/src/lib.rs:1819-1972`).  Sync's DFS sibling loop now
  pushes only the 4 new lits per sibling instead of re-asserting
  the ancestor prefix.  Details in
  `docs/OPTIMIZATION_LOG.md#r1`.  Rate lever: nodes/60 s
  3.9 M → 11.2 M (+187 %); `sat_unsat` fell 98 % because baseline
  was re-deriving the same UNSAT per descent.  Peer-clause import
  is gated on `current_decision_level() == 0` for soundness
  (install path can immediately propagate at non-zero level).

- **R8 (delta sums in sync walker's speculative choice loop)**:
  **ACCEPTED — TTC −50 % vs R1 (−60 % vs pre-R1 baseline).**
  `apply_sum_delta_at` replaces two full `rebuild_sums` per choice
  with an O(|closure_events[level]|) delta filtered by
  `newly_placed` kinds (so we don't double-count events whose kind
  was pre-set by `harvest_forced`) and an O(n) `copy_from_slice`
  on rollback.  Nodes/60 s: 11.2 M → 37-58 M (3-5×).  Subtle
  correctness invariant on `newly_placed` caught by debug
  assertion; n=18 TT(18) verified in 1.8 s.

### Kissat comparison (April 19 2026)

Kissat (`/home/user/kissat`, 206 source files, ~32k LOC C) is a
re-engineered CaDiCaL focused on cache layout and adaptive
heuristic policy. All five gaps found vs. CaDiCaL also exist vs.
kissat; in addition kissat has the following mechanisms worth
considering for the Turyn `--wz=sync` loop.

#### K1. Binary-watch prioritization (kissat: `watch.h:38-80`)

Kissat separates watch lists into tagged `binary_watch` vs
`large_watch` and runs transitive reduction that moves all
binaries to watch-list heads. Propagation touches binaries first;
cache line per propagated literal is well-packed. Radical has one
flat `Vec<(u32, Lit)>` per literal.

- **TTC mechanism**: rate. 77.8 % of sync's forcings are `clause`;
  many are binary (Tseitin, BDKR rules). Hitting binaries first
  terminates the per-lit watcher loop earlier and reduces cache
  pressure.
- **Detection plan**: `clause` forcings/sec ↑; nodes/s ↑;
  `sat_unsat` rate ↑.
- **Complexity**: moderate — either a dedicated `bin_watches:
  Vec<Vec<Lit>>` index (R2 as originally proposed) or an in-place
  partition + tagged watch struct. Former is simpler and
  compatible with existing clause-arena API.

#### K2. Backbone detection at solver build time (kissat: `backbone.c:16-68`)

Kissat detects literals forced to a single polarity across *all*
satisfying assignments of the base formula, then fixes them at
level 0. Radical has failed-literal probing but no systematic
backbone phase.

- **TTC mechanism**: denominator (variables fixed pre-search never
  enter the walker's assumption stack) + rate (solver starts at
  smaller instance).
- **Detection plan**: number of variables assigned at level 0
  after backbone phase rises; per-level `children` at deep
  levels shrinks.
- **Complexity**: ~200-500 LOC. Gated by config; off by default
  until measured.

#### K3. Enable and tune radical's existing vivification path (`radical/src/lib.rs:2635`)

Radical has a vivification implementation but it's off by default
(`vivification: false` in default config) and only runs every
1000 conflicts on ≤ 50 clauses. Kissat runs vivification regularly
and integrates it with minimization via the removable-set (shrink).

- **TTC mechanism**: rate (shorter clauses propagate faster) +
  shortfall (earlier UNSAT on redundant branches).
- **Detection plan**: avg_nogood len drops; clauses/sec ↑;
  nodes/s roughly flat (fewer but shorter) unless a clause-DB-
  compaction win manifests.
- **Complexity**: trivial to enable, non-trivial to tune (budget
  fraction, subsumed-clause eviction).

#### K4. Congruence closure / gate recognition (kissat: `congruence.c`)

Detects AND/XOR/ITE gate sub-structures in clause sets and merges
equivalent variables. For Turyn, XOR/QuadPB constraints are
explicit (`quad_pb_var_terms`, `xor_chain`), not hidden in CNF, so
gate recognition over the pure-clause part (BDKR Tseitin chains,
MDD canonicalization rules) might find something.

- **TTC mechanism**: denominator (fewer decision variables after
  merge).
- **Detection plan**: `num_vars` after preprocessing < original;
  nodes/s ↑ via smaller search tree.
- **Complexity**: large (~500-1000 LOC). Lower priority than K1/K2.

#### K5. Adaptive LBD tiers with mode switching (kissat: `tiers.c:6-49`, `reduce.c:82-86`)

Kissat splits reduction into `tier1` (glue ≤ adaptive1),
`tier2` (glue ≤ adaptive2), `tier3` (rest). Thresholds are
computed from the running glue histogram and differ between
stable and focused modes. Radical has a hard-coded `lbd ≤ 3`
cutoff.

- **TTC mechanism**: rate (longer retention of high-quality
  learnt clauses).
- **Detection plan**: `clause` forcing count ↑; peer exchange
  quality ↑ (clauses fired more often before eviction).
- **Complexity**: moderate. Pre-requisite: track LBD per learnt
  clause (R3 above).

### Continuation session (April 19 2026, autonomous extended) — **−91 % TTC cumulative**

After the initial inventory & methodology fix above, the session
continued autonomously. The cumulative TTC delta on n=26 sync went
from 0 → −91 % across many commits.

**Landed wins** (in OPTIMIZATION_LOG.md with full before/after):

- **R1** (incremental assumption frames in radical, push/pop frame
  API): −20.6 % TTC. Sync's per-sibling propagate dropped from
  re-asserting 4L lits to pushing 4 fresh lits.
- **R8** (delta sums in candidate-building loop): −50 % vs R1.
  Replaced two full `rebuild_sums` per choice with O(events at this
  level) delta + O(n) restore. Subtle correctness bug (double-count
  when `harvest_forced` pre-set a kind) caught by debug assertion
  before commit.
- **R8b** (delta sums in sibling loop): −12 % vs R8. Same idea as
  R8 applied to the post-set-bit rebuild in the sibling loop.
- **R8c** (skip post-harvest rebuild_sums when no walker bit forced):
  **−74 % vs R8b** — the single biggest win. Most pushes at
  shallow-to-mid levels force 0 walker bits, making the rebuild pure
  waste.
- **R7** (delete dead `dynamic_capacity_violated`): trivial cleanup.
- **R10** (`Solver::add_clause_deferred` infrastructure + ungated
  peer-clause import): TTC parity at n=26 (very few binary
  nogoods to share), but enables future LBD-tier sharing.
- **stack-saved_bits, debug-assert dead guard, per-kind ranges in
  closure_events, SCC + BVE preprocessing**: each ~1–2 % nodes/s
  rate gain, TTC in noise but rate measurably above noise.

**Rejected this session**:

- **R5** (`--no-xor` flag at sync): in noise (~−1.4 %).
- **R6** (`MAX_SHARED_LEN` ∈ {32, 64, 8}): all regressed
  measurably; long shared clauses bloat watch lists faster than
  they prune.
- **R8d** (skip `harvest_forced` when no walker var inferred):
  +4 % regression. Harvest's side-effect of populating
  `state.bits` for the next dfs_body's candidate-building is
  necessary; skipping harvest pushes that work into more
  expensive `push_assume_frame` conflicts.
- **R9** (forbidden-lit cache from unit nogoods):
  **UNSOUND** — unit nogoods from `analyze_assumptions` aren't
  level-0 facts; they depend on the current assumption stack.
  Caching them lost solutions (n=18 max_lvl dropped from 18 to
  17, no leaves found).
- **S6** (incremental sigma in `tuple_reachable`): in noise
  (~+0.4 %). The compiler had already optimized
  `compute_sigma`'s O(4n) scan well.
- **`capacity_violated` unsafe + tight loop**: in noise. Compiler
  auto-vectorized the original. The function IS critical (1.16B
  rejects/min; stubbed → 5000× TTC regression) but already
  near-optimal.
- **Per-kind propagation telemetry skip via `cfg!(feature)` gate**:
  no measurable speedup (compiler folded the constant true/false
  branch).

**Methodology lessons** (logged to OPTIMIZATION_LOG.md):

- **Sequential single-machine measurements** brought the noise
  floor from 11 % (parallel benchmarks contending) to ~1.3 %.
- **Thermal bimodal patterns** are a tell that the hot path is
  sustained-CPU. Once we removed the dominant work (R8c), runs
  became tightly clustered (~0.3 % spread).
- **Decisive only**: no in-noise commits. Six experiments with
  plausible theoretical merit failed to clear the noise envelope
  and were not committed.

**Cumulative TTC trajectory at n=26 sync**:

| Stage           | TTC (mean)   | Δ vs baseline |
|-----------------|---------------|----------------|
| Baseline        | 6.581e8 s     | —              |
| + R1            | 5.224e8 s     | −20.6 %        |
| + R8            | 2.62e8 s      | −60 %          |
| + R8b           | 2.30e8 s      | −65 %          |
| + R8c           | 5.97e7 s      | **−91 %**      |
| + R7+R10+marginals | 5.87e7 s   | **−91.1 %**    |

**Next levers** (post-session priorities, hardest first):

1. **Chronological backtracking in radical**: the SAT '18-style
   shallow backtrack would help propagate_only-dominated workloads
   like sync. Medium-large solver-internal change.
2. **Combined-level walking**: place 2 levels' worth of bits per
   `push_assume_frame` (8 lits instead of 4). Halves push call
   count, doubles propagation per call. Net benefit dependent on
   propagation linearity.
3. **Sync-driven `reduce_db` schedule**: clauses accumulate
   unbounded under sync (no internal trigger). For long n=56 runs
   this matters. Wire reduce_db + vivify into sync's worker loop
   on a conflict-count schedule.
4. **Architectural denominator**: MDD-equivalent boundary
   pre-pruning for sync mode. Currently sync walks raw bouncing-
   order DFS while apart pre-prunes via MDD. The 5700× gap at n=56
   between sync and apart is denominator-driven.

### Earlier session wrap-up (April 19 2026 — initial measurement only)

Productive inventory, limited measurement:

- Established baselines for all three `--wz` modes at n=26 (60 s
  budget). Sync noise floor = 11 %, so deltas < 15 % need
  averaged runs to be decisive.
- Compared radical vs CaDiCaL and vs kissat; identified five
  cadical gaps + five kissat-specific gaps.
- Added 17 concrete, single-commit ideas to this file (R1-R12
  against the CaDiCaL/radical gap, K1-K5 against the kissat
  refinements).
- Tested R5 (`--no-xor`) and R6 at MAX_SHARED_LEN ∈ {32, 64} on
  sync. All three were within the 11 % noise envelope;
  rejected. **No commit landed this session.**
- Identified **R1 (incremental assumption propagation)** as the
  highest-leverage next step: `propagate_only` currently
  backtracks to level 0 and re-enqueues every ancestor
  assumption per sibling, costing O(L) per call where O(Δ) would
  suffice. Theoretical 5-20× rate improvement, medium-sized
  change (solver surface + DFS plumbing).

Priority order for the next session:

1. **R1 incremental assumption propagation** — biggest sync TTC lever.
2. **K1 binary-watch prioritization / dedicated bin list** —
   targets the 77.8 % of forcings that come from `clause`.
3. **R8 delta sums in sync** — rate win inside the walker.
4. **R11 first-branching-level probe** — rate win (stop 16-way
   redundant prefix walk).
5. **K3 enable vivification + measure** — potentially cheap.
