# Telemetry output (`--wz=sync`)

A verbose run of `--wz=sync` emits four blocks after the search ends
(whether it found a solution, hit `--sat-secs` timeout, or exhausted
the tree). All four are written to stderr so they survive timeouts
and redirections that only capture stdout. This doc is the reader's
guide to those blocks.

Example invocation used throughout:

```bash
target/release/turyn --n=56 --wz=sync --sat-secs=30
```

## Block 1 — scalar summary line

```
sync_walker(parallel x16): nodes=… cap_rejects=… tuple_rejects=…
    rule_rejects=… sat_unsat=… leaves=… max_lvl=…
    elapsed=… time_to_first_leaf=… avg_nogood=…/… (…x shrink)
    peer_imports=…
```

- `nodes` — DFS visits summed across all workers.
- `cap_rejects` — walker-side capacity violations (`|S(s)| >
  max_remaining[level][s]`).  Rejected without a SAT call.
- `tuple_rejects` — sibling candidates discarded because they could
  not land on any feasible sum tuple.
- `rule_rejects` — rejected by a BDKR canonicalization rule without
  calling the solver.
- `sat_unsat` — propagate\_only returned UNSAT; a nogood was
  installed. This is the only place `avg_nogood` has a denominator.
- `leaves` — DFS frames that reached `level == depth`; must be
  verified by `verify_tt` before being reported.
- `max_lvl` — deepest level any worker reached.
- `avg_nogood` — mean learnt-clause size (`final / pre-minimization`,
  ratio is the minimization shrink factor).
- `peer_imports` — learnt clauses pulled from the shared
  `ClauseExchange` into each worker's local solver.

## Block 2 — TTC projection (`project_ttc`)

```
TTC projection (n=…):
  level  parent   child    b_eff   note
  …      …        …        …       …
  …
  N_total ≈ …
  rate (nodes/s, parallel) = …
  TTC_serial   ≈ …s
  TTC_parallel ≈ …s
```

Projects full-cover tree size from per-level true branching factor
`b_eff(L) = children_by_level[L] / nodes_by_level[L]`. Levels with
fewer than `NOISY_THRESHOLD=32` parents are flagged `?` but still
used. This is the headline TTC; the "direct TTC" in Block 4 is the
cross-check from DFS coverage.

## Block 3 — per-level table

```
Per-level: lvl |   nodes |  children | proc'd | cov% |   forced | f/node |   time(s) |  t/node
Per-level:   0 |       1 |       256 |    256 | 100.0 |       32 |   32.00 |    29.876 | 29.876000
Per-level:   1 |     256 |     12288 |    328 |   2.7 |     4096 |   16.00 |    29.800 |  0.116406
…
Per-level: cumulative root-coverage (∏ cov) = 3.102e-09  →  direct TTC = elapsed / coverage
Per-level: total walker-var forcings = 1234567 (avg 2^7.42 shrink per propagate call)
```

Columns:

- `nodes` — DFS parents visited at this level (all workers).
- `children` — sibling candidates generated at this level before
  walker/SAT pruning.
- `proc'd` — children that passed walker + SAT filters and became
  new DFS frames.
- `cov%` — `proc'd / children`. Coverage fraction "out of this
  parent's siblings, what share survived at least to the next
  propagate\_only call?"
- `forced` — walker-var forcings that this level's new assumptions
  caused the SAT solver to propagate (incremental over the parent
  level). Each forced walker var is a 1-bit sub-cube pruned.
- `f/node` — `forced / nodes`. `2^(f/node)` is the typical per-
  propagate sub-cube shrink at this level.
- `time(s)` — cumulative wall-seconds spent in DFS frames rooted at
  this level, inclusive of descendants. Summing across levels
  double-counts.
- `t/node` — `time / nodes`. Per-sub-cube cost at this level.

The `cumulative root-coverage` line is `Π_L cov(L)` over all levels
with generated candidates, and `direct TTC = elapsed / coverage`
assumes an even distribution of "missed" paths. Use it as a
reality check against Block 2's projected TTC.

## Block 4 — per-feature forcings

```
Per-feature forcings (total 12345678): clause=9989012 (80.9%)  quadpb=2271156 (18.4%)  pbseteq=85510 (0.7%)
```

One line, broken down by SAT propagator family (`PropKind` in
`radical/src/lib.rs`): `clause`, `pb`, `quadpb`, `xor`, `spect`,
`mdd`, `pbseteq`. Only kinds with non-zero counts are shown.
Totals are summed from `solver.propagations_by_kind(kind)` deltas
captured around each `propagate_only` call.

Interpretation cheat-sheet:

- `clause` high, `quadpb` low: most work is pure CNF propagation;
  the Turyn identity is mostly satisfied-by-default.
- `quadpb` high: the per-lag identity is doing heavy lifting; worth
  investigating whether a cheaper lag subset suffices.
- `pbseteq` non-zero only near leaves: expected — it's the
  sum-constraint tightening that fires when most boundary is pinned.
- `xor` high: Tseitin XOR chains from canonicalization are the
  limiting propagator; BDKR rules (ii..vi) lean on XOR semantics.
- `spect`, `mdd`: currently always zero in sync mode (those
  propagators are not attached).

## Block 5 — per-(level, feature) matrix

```
Per-level forcings by feature: lvl |     clause |     quadpb |    pbseteq
Per-level forcings by feature:   0 |       1234 |        456 |          0
…
Per-level forcings by feature:  15 |    4321000 |     982100 |      12345
Per-level forcings by feature:  16 |    3210000 |     783200 |      65432
Per-level forcings by feature:  17 |    1210000 |     471200 |      43210
```

Only kinds that were non-zero at some level appear as columns, and
only levels with non-zero total appear as rows. This is the 2D
breakdown of Block 4: "which propagator is hottest at which depth?"

Typical pattern observed at `n=18`:
- Ratio between `clause` and `quadpb` is roughly uniform across all
  levels (~4:1).
- `pbseteq` activates only at depth ≥ 11.
- Levels `n-3 .. n-1` do 99% of propagation work — expected because
  DFS spends most of its time near leaves.

## How to read a run together

1. Block 2's `TTC_parallel` is the headline. If it's too large to
   be feasible, Block 3's `cov%` column tells you which level is
   the widest — that's where pruning needs to improve.
2. Block 4 tells you *which propagator* is slowest. Multiply by
   Block 3's `time(s)` to map propagator work onto wall clock.
3. Block 5 tells you *where in the tree* each propagator pays off.
   If `quadpb` dominates near the root but `clause` dominates near
   leaves, a shallower quad-PB subset plus aggressive Tseitin
   learning would be a plausible win.
4. Compare `TTC_parallel` (Block 2) vs. `direct TTC` (Block 3): if
   they disagree by more than ~5×, one of them is mis-estimating
   (usually Block 2's `b_eff` on a level with `?` flag).

## Calibration target

The search-space size — number of distinct Turyn quadruples — at
a given `n` is known from the literature: `|TT(18)| = 675`,
`|TT(22)| = 3105`, `|TT(26)| = 3753`. Under perfect pipeline
efficiency (one propagate\_only call per solution), we would expect
`TTC_parallel / (time_per_propagate) ≈ |TT(n)|`. Any order-of-
magnitude gap is "room to prune". Use this as the sanity check
when a micro-optimization claims a 10× win.

## Publishing on timeout

All five blocks are printed unconditionally at the end of
`search_sync`, inside `thread::scope`, regardless of whether a
solution was found or the deadline fired. If you kill the process
with `SIGINT` *before* `thread::scope` returns, you lose the blocks;
use `--sat-secs=N` and let the walker time out naturally.

## Where this is implemented

- `radical/src/lib.rs`:
  - `PropKind` enum + `Reason::prop_kind()` mapping
  - `Solver::prop_by_kind` counter array, incremented in `enqueue`
  - `Solver::propagations_by_kind(kind)` public accessor
- `src/sync_walker.rs`:
  - `SyncStats::{prop_by_kind_total, forced_by_level_kind}`
  - Delta capture around each `propagate_only` call in `dfs`
  - `format_per_level_telemetry`, `format_prop_by_kind_summary`,
    `format_per_level_kind_table`, `project_ttc`
  - Final block printed in `search_sync` under `if verbose`

The `cross`/`apart`/`together` modes do not currently plumb
per-feature counters. Adding them requires capturing deltas around
`SolveXyPerCandidate::try_candidate`, `SolveW`, and `SolveZ` solver
calls and aggregating across clones — see `SearchStats` in
`src/legacy_search.rs` and `src/mdd_pipeline.rs` for the
aggregation points.
