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

`main()` dispatches into one of several modes (with a handful of
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

    # Search modes
    elif --stochastic:     stochastic_search()           # SA / local search
    else:
        match cfg.effective_wz_mode():
            WzMode::Cross    => run_hybrid_search()              # DEFAULT
            WzMode::Apart    => run_mdd_sat_search(wz_together=false)
            WzMode::Together => run_mdd_sat_search(wz_together=true)
            WzMode::Sync     => sync_walker::search_sync()       # no MDD file
```

The producer is chosen by `--wz=cross|apart|together|sync`.
`--wz-together` still works as a short alias for `--wz=together`, and
`--mdd-k=N` / `--mdd-extend=N` imply `--wz=apart` when no explicit
`--wz` is given. Explicit `--wz` always wins.

`--wz=sync` is the newest mode and differs structurally from the other
three: it does **not** load `mdd-<k>.bin`, does **not** enumerate sum
tuples up-front, and does **not** split the search into `(Z, W)`
producer → XY consumer. Instead, one persistent CDCL solver holds every
constraint and a single DFS walker over all four sequences feeds it
assumptions. See [`--wz=sync`](#wzsync--sync_walkersearch_sync) below.

**The `cross`, `apart`, and `together` modes all load the same MDD**
(`mdd-<k>.bin`) — the name "MDD pipeline" for `--wz=apart|together`
is a historical artefact. Every search layer in those three modes
uses the MDD as its XY boundary enumerator; they differ only in how
they generate the `(Z, W)` candidate pairs before handing each pair
off to the shared `SolveXyPerCandidate::try_candidate` XY SAT path.

`--wz=sync` is different: no MDD file is loaded and there is no
separate XY stage. A single CDCL solver encodes the whole problem and
a unified 4-sequence walker drives it to a leaf.

The flat `xy-table-k*.bin` format was retired once we proved (test:
`table_vs_mdd_same_k_agree`, now removed) that at the same `k` the
MDD sub-tree walker returned identical `(x_bits, y_bits)` sets.

## The three (Z, W) producers (Cross / Apart / Together)

The `cross`, `apart`, and `together` modes ultimately feed the same
XY SAT consumer (`SolveXyPerCandidate::try_candidate`). They differ
in how they *generate* the candidate `(Z, W)` pairs that get handed
to that consumer. (`--wz=sync` is a separate architecture and is
described in its own section below.)

### `--wz=cross` — `run_hybrid_search` (default)

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

### `--wz=apart` / `--wz=together` — `run_mdd_sat_search`

Start from the MDD boundaries directly: navigate to a `(z_bits,
w_bits)` boundary, then SAT-solve the Z and W middles inline. The
`apart` variant runs SolveW → SolveZ as two separate SAT stages; the
`together` variant collapses them into a single combined W+Z SAT call.

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
            push SolveW            (--wz=apart)
            or   SolveWZ           (--wz=together)

    SolveW(tuple, z_bits, w_bits, xy_root):        # --wz=apart
        enumerate W middles (brute-force if middle_m ≤ 20, else SAT)
        for each passing W: push SolveZ

    SolveWZ(tuple, z_bits, w_bits, xy_root):       # --wz=together
        single combined W+Z SAT call
        for each (W, Z) pair: solve XY inline

    SolveZ(tuple, z_bits, w_bits, w_vals, w_spectrum, xy_root):
        build Z SAT solver with cached ZBoundaryPrep
        attach SpectralConstraint with per-freq bound
            pair_bound - |W(ω_SAT)|² at the SAT's 167-freq grid
        up to max_z solves:
            SAT-solve for a Z middle
            compute Z spectrum (realfft), post-hoc pair check
            if passes:
                SolveXyPerCandidate::new(problem, (Z,W), template)
                walk XY sub-MDD from xy_root → (x_bits, y_bits)
                for each: try_candidate(x_bits, y_bits)  → SAT
```

`SolveXyPerCandidate::try_candidate` is the same per-candidate fast
path that `solve_xy_via_source` uses for `--wz=cross`, so all three
producers share identical XY SAT behaviour once they reach that
stage. They differ only in how they *get* to the point of having a
`(Z, W, xy_root)` triple.

### `--wz=sync` — `sync_walker::search_sync`

One persistent CDCL solver, one DFS walker, all four sequences
assigned together. No MDD file, no tuple pre-enumeration, no
separate `(Z, W)` → XY handoff.

```
search_sync(problem, cfg):
    solver = radical::Solver::new_with_config(cfg.sat_config)
    encode_all_variables(solver):              # X, Y, Z boundary + middle
        length-n {±1} vars for X, Y, Z; length-(n-1) for W
        BDKR canonicalization rules (i..vi) as Tseitin clauses
        per-lag Turyn identity as native quad-PB constraints
        (spectral / MDD constraints are NOT attached in sync mode)

    # Bouncing-order position schedule: pin end-points first, work inwards.
    # depth = n for even n; at each level we pin all four sequences at one p.
    pos_order = [0, n-1, 1, n-2, 2, n-3, ..., n/2-1, n/2]

    # Parallel workers (N = available_parallelism or $TURYN_THREADS):
    # worker 0 explores siblings in score order (best-first); workers 1..
    # use a per-worker-seeded random permutation so each starts in a
    # different region of the tree. A shared ClauseExchange relays
    # learnt nogoods across workers.
    for worker in 0..N in thread::scope:
        state = DFS state; assumptions = [];
        dfs(state):
            if cancelled or timed out: return
            if level == depth: found leaf → verify → publish
            p = pos_order[state.level]
            for each (x,y,z,w) sibling at position p:
                extend assumptions with the 4 (or 3 when p == n-1) unit lits
                capacity check: |S(s)| ≤ max_remaining[level][s]  (walker-side)
                solver.propagate_only(&assumptions)                (SAT-side)
                    → learn nogood on conflict (persists for the whole walk)
                if sat: record forcings, recurse; else: backtrack
```

Key structural differences vs. the three MDD-backed producers:

- **No upfront MDD**: boundary sub-cubes are implicitly enumerated by
  the DFS. No `mdd-<k>.bin` dependency.
- **No tuple split**: the sum identity `σ_X² + σ_Y² + 2σ_Z² + 2σ_W² =
  6n-2` is a derived consequence of the per-lag constraints and is
  not used to pre-filter search regions.
- **Propagation-only**: the SAT solver is used exclusively via
  `propagate_only(&assumptions)` — no CDCL decisions, no full solve.
  It answers "can the current 4-sequence prefix be extended?" as
  cheaply as possible, and learns a nogood on failure.
- **Persistent solver**: there is no clone-per-candidate. Every
  walker node hits the same solver instance, so CDCL nogoods learnt
  early in the walk prune every later sub-cube they apply to.
- **Per-worker clause exchange**: parallel workers swap learnt
  clauses through a lock-free-ish `ClauseExchange` buffer. This is
  the only cross-worker communication besides the cancel flag.
- **Rich telemetry**: sync mode emits a per-level table, a
  per-propagator-feature summary, a per-(level, feature) matrix,
  and a direct TTC computed from the DFS coverage product. See
  [docs/TELEMETRY.md](TELEMETRY.md) for the output format.

`--wz=sync` is currently the only mode that exposes per-feature
SAT-propagator attribution. The `cross`/`apart`/`together` pipelines
use clones and per-candidate solves; their propagation counters are
reset per-clone and the total is not aggregated anywhere.

### Measured TTC at `n=26` (4 threads)

| Mode | TTC | Notes |
|---|---|---|
| `--wz=cross` | ~1 h (extrapolated) | SpectralIndex cross-matching prunes aggressively |
| `--wz=apart` | ~7.7 h | direct MDD path walk, ~371 paths/s |
| `--wz=together` | ~7.7 h | same walk, combined W+Z SAT changes per-stage accounting |

The ~7–8× gap between `cross` and the MDD producers is the `(Z, W)`
enumeration strategy difference, not the XY SAT stage — Commit A
(`SolveXyPerCandidate`) unified the XY stage and closed a ~24 %
per-solve gap at `n=22`, but at `n=26` the bottleneck is upstream of
XY for both MDD producers.

### Measured TTC at `n=56` (16 threads, April 2026)

| Mode | TTC (parallel) | In human units | Notes |
|---|---|---|---|
| `--wz=sync` | 9.67 × 10⁹ s | ~307 years | direct coverage-product TTC from sync telemetry |
| `--wz=apart --mdd-k=8` | 1.68 × 10⁶ s | ~19.5 days | MDD pre-prunes to 1.6×10⁻¹⁰ of naive space |

The ~5700× gap is entirely the MDD denominator — `--wz=apart` walks
a pre-pruned boundary DAG, `--wz=sync` walks the raw bouncing-order
DFS with SAT-side pruning only. Both use the same `radical` solver
and the same quad-PB identity; the difference is up-front search
space reduction.

At `n=18` `--wz=sync` solves in ~13.5 s wall-clock (16 threads) with
a reported TTC of ~6.7 × 10⁴ s (direct coverage, 16 threads) — the
leaf was hit early but residual tree coverage dominates the TTC
projection. This is the smoke-test correctness anchor for sync mode.

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

- `gen_mdd K` → `mdd-K.bin` — used by **all three** `--wz` modes
  (`--wz=cross` always loads `k = 7` for XY enumeration;
  `--wz=apart|together` load whatever `--mdd-k` says, defaulting to 8).
  The only on-disk artifact the search needs.
- `gen_mdd_bfs K` — an alternative BFS-based MDD builder used for
  very large `k`.
