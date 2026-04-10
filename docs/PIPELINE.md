# Pipeline overview

A Turyn-type quadruple `TT(n)` is four `±1` sequences — `X`, `Y`, `Z` of
length `n` and `W` of length `n-1` — satisfying the aperiodic
autocorrelation identity

    N_X(s) + N_Y(s) + 2·N_Z(s) + 2·N_W(s) = 0    for every s ≥ 1

together with the sum-squared invariant

    σ_X² + σ_Y² + 2σ_Z² + 2σ_W² = 6n - 2.

Taking the DTFT of the autocorrelation identity gives the equivalent
spectral form

    |X(ω)|² + |Y(ω)|² + 2|Z(ω)|² + 2|W(ω)|²  =  6n - 2  ∀ ω

and therefore the pair bound `|Z(ω)|² + |W(ω)|² ≤ 3n-1` for every
frequency.  Almost every decision in the search is there to enforce
some discrete sample of this continuous condition.

## Entry points

`main()` dispatches into one of four modes (with a handful of
early-return subcommands for verification, DIMACS dumps, etc.):

```
main():
    cfg = parse_args()

    # Early returns (not searches)
    if --verify-seqs:      verify_tt(...); exit
    if --test-zw:          try every tuple against given Z,W via SAT XY; exit
    if --phase-a:          enumerate sum tuples and print; exit
    if --phase-b:          stats-only run through Phase B; exit
    if --dump-dimacs:      write SAT instance for the first tuple; exit
    if --benchmark=N:      time N repeats; exit

    # Search modes (first match wins)
    elif --stochastic:     stochastic_search()           # SA / local search
    elif --mdd:            run_mdd_sat_search()          # MDD pipeline
    else:                  run_hybrid_search()           # DEFAULT
```

All five layers — verify subcommand, benchmark wrapper, stochastic
search, hybrid search, and MDD search — share the same
`XyOwner`/`solve_xy_via_source` XY SAT stage.  The XY enumerator is a
k-MDD sub-tree walker; the flat `xy-table-k*.bin` format was retired
once we proved (test: `table_vs_mdd_same_k_agree`, now removed) that
at the same `k` it returned identical `(x_bits, y_bits)` sets.

## The two main search pipelines

Both pipelines ultimately feed the same XY SAT consumer
(`solve_xy_via_source`). They differ in how they *generate* the
candidate `(Z, W)` pairs that get handed to that consumer.

### `run_hybrid_search` (default)

Brute-force full `Z` and `W` sequences, spectral-filter them, bucket
by boundary signature, then dispatch to XY SAT:

```
tuples = phase_a_tuples(problem)
mdd    = load "mdd-7.bin"            # XY candidate enumerator
for each tuple (heuristic order):
    w_candidates = brute_force_w_middles + individual spectral filter
    stream_zw_candidates_to_channel():
        for each z_candidate (brute-force length-n with sum constraint):
            individual spectral filter on Z
            for each matching w_candidate:
                spectral pair check  (|Z(ω)|² + |W(ω)|² ≤ 3n-1 on FFT grid)
                if passes → emit SatWorkItem { z: Fixed, w: Fixed, tuple }

# Worker pool (run_parallel_search):
for each SatWorkItem in priority queue:
    solve_work_item → solve_xy_via_source(mdd-rooted xy sub-tree)
        build per-(Z,W) filter state (GJ equalities, lag filters, term-
        state template), clone the solver template once, then walk the
        XY sub-MDD and SAT-solve each (x_bits, y_bits) candidate that
        survives the bitwise pre-filters.
```

This is the path that found `TT(26)` on main (commit 88aae1a) in
~161 s at 16 threads.

### `run_mdd_sat_search` (`--mdd`)

Start from the MDD boundaries directly: navigate to a `(z_bits,
w_bits)` boundary, then SAT-solve the Z and W middles inline:

```
monitor thread:
    while queue low:
        idx = path_counter++
        path = LCG_scramble(idx)
        walk MDD along path → (z_bits, w_bits, xy_root)
        push Boundary item

N workers, identical loop:
    pop highest-priority item from dual priority queue:

    Boundary(z_bits, w_bits, xy_root):
        for each tuple:
            sum feasibility check
            any_valid_xy(xy_root, tuple) fail-fast
            push SolveW (or SolveWZ if --wz-together)

    SolveW(tuple, z_bits, w_bits, xy_root):
        enumerate W middles (brute-force if middle_m ≤ 20, else SAT)
        for each passing W: push SolveZ

    SolveWZ(tuple, z_bits, w_bits, xy_root):        # --wz-together
        single combined W+Z SAT call
        for each (W, Z) pair: push SolveXY inline work

    SolveZ(tuple, z_bits, w_bits, w_vals, w_spectrum, xy_root):
        build Z SAT solver with cached ZBoundaryPrep
        attach SpectralConstraint with per-freq bound
            pair_bound - |W(ω_SAT)|² at the SAT's 167-freq grid
        up to max_z solves:
            SAT-solve for a Z middle
            compute Z spectrum (realfft), post-hoc pair check
            if passes:
                walk XY sub-MDD from xy_root → (x_bits, y_bits)
                for each: SAT-solve XY with boundary assumptions
```

The `solve_xy_via_source` call in SolveZ's XY stage is the same one
the default hybrid path uses. The two pipelines differ only in how
they *get* to the point of having a `(Z, W, xy_root)` triple.

## Known-good anchor points

For sanity-checking correctness anywhere in the pipeline:

### Known `TT(26)`

```
X =: '++--+--+++++++-+-++--+-++-'   σ_X = 6
Y =: '+++-+-++++++-++-+---+-++--'   σ_Y = 6
Z =: '+++-+--++++++--++---+-+--+'   σ_Z = 4
W =: '++++-+---+--+++--++++-+-+'    σ_W = 5
```

- Sum tuple `(6, 6, 4, 5)`, `σ_X² + σ_Y² + 2σ_Z² + 2σ_W² = 154 = 6n-2`.
- Dense spectral sweep: `max(|Z(ω)|² + |W(ω)|²) ≈ 72.7 < 77 = 3n-1`.
  Roughly 6 % slack on both the SAT and FFT grids, so the real
  solution comfortably passes both spectral filters.
- At `k = 7`, the `(z_bits, w_bits) = (9495, 11183)` boundary is live
  in the MDD, and its XY sub-tree contains 1388 valid `(x_bits,
  y_bits)` candidates — `(6675, 3415)` among them — that match the
  tuple's sum constraints.

The `known_tt26_verifies` unit test runs `verify_tt` on this
quadruple.

## The two spectral filters

The pair bound `|Z(ω)|² + |W(ω)|² ≤ 3n-1` is enforced at two
different discrete frequency grids:

1. **Inside the Z SAT solver**, via `radical::SpectralConstraint` at
   the SAT's 167-point grid `ω_fi = (fi+1)/168 · π`. During CDCL
   propagation it uses a triangle-inequality lower bound on `|Z(ω)|`
   (soundness preserved; at full assignment the check is tight). The
   `per_freq_bound[fi]` is set to `pair_bound - |Ŵ(ω_fi)|²` computed
   once per `(Z-boundary, W)` pair.

2. **Post-hoc** after Z SAT returns, via `compute_spectrum_into` +
   `spectral_pair_ok` at the realfft 129-point grid `ω_k = πk/128`.
   Catches violations the SAT's grid missed.

Both checks are sound necessary conditions and they apply to
essentially disjoint frequency grids (they share only the 8 points
`ω = mπ/8` for `m = 1..8`).  At small `k` the filter chain rejects
roughly 99.996 % of Z solutions — that's not a bug, it's the real
density of valid `(Z, W)` pairs at the bound.

## Why MDD is the sole XY enumerator

Before the consolidation there were two XY candidate enumerators:

- `XYBoundaryTable` — a ~1.9 GB on-disk flat table keyed by `(z_bits,
  w_bits, x_bnd_sum, y_bnd_sum)`, built by `gen_table`.
- `walk_xy_sub_mdd` — a runtime DFS through the MDD's XY sub-tree
  rooted at `xy_root`.

Both enforce exactly the Turyn identity at the `k` "exact" lags (the
lags where every pair is boundary-to-boundary). The `table_vs_mdd_
same_k_agree` test confirmed identical candidate sets at `k = 7`.
Hybrid-path throughput at `n = 26` on 4 threads matched within 2 %
between the two backends. The MDD's ~2000× memory advantage (1 MB
vs 1.9 GB) made the decision trivial — the flat table and `gen_table`
are gone.

## Shared building blocks

- `Problem { n }` with `m = n-1`, `target_energy = 6n-2`,
  `spectral_bound = 3n-1`.
- `phase_a_tuples` — enumerates and normalizes sum tuples `(x,y,z,w)`
  satisfying `x² + y² + 2z² + 2w² = target_energy`.
- `SpectralFilter` (rustfft/realfft, FFT frequency grid).
- `radical::SpectralTables` (SAT frequency grid, 167 pts) and
  `radical::SpectralConstraint` (inside the SAT solver with per-freq
  bounds).
- `sat_z_middle::LagTemplate` — per-lag literal groupings for the Z
  and W SAT encodings.
- `sat_z_middle::ZBoundaryPrep` — per-worker cache of the boundary-
  dependent fill prep (agree_const, lits_a/lits_b, coeffs) keyed by
  `z_bits`; rebuilt in place on cache miss.
- `SatXYTemplate` — per-tuple XY SAT template with precomputed lag
  pairs and Gaussian-elimination prep.
- `XyOwner` + `solve_xy_via_source` — the shared XY SAT consumer,
  called by both the hybrid path and `run_mdd_sat_search`.
- `mdd_zw_first::Mdd4` / `load_best_mdd` — offline-built MDD loaded
  from `mdd-<k>.bin`.
- `PackedSeq`, `verify_tt`, `compute_zw_autocorr`.

## Offline artifacts

- `gen_mdd K` → `mdd-K.bin` — used by **both** search paths (hybrid
  loads `k = 7` for XY enumeration, `--mdd` loads whatever `--mdd-k`
  says). The only on-disk artifact the search needs.
- `gen_mdd_bfs K` — an alternative BFS-based MDD builder used for
  very large `k`.
