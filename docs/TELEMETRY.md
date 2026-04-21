# Telemetry

This doc has two parts:

1. **Universal schema** (below) — the shared `ProgressSnapshot` that
   every mode (`cross`, `apart`, `together`, `sync`, `stochastic`)
   emits through `SearchEngine`. Describes the one TTC metric, the
   three 2-D forcing rollups, and the fan-out / edge-flow counters.
2. **`--wz=sync` specifics** — the five historical
   text blocks the sync walker prints after a run. These remain
   because the walker has rich, sync-specific diagnostics that
   aren't yet folded into the universal snapshot; they read cleanly
   against the universal schema below.

## Universal schema

Every run emits `ProgressSnapshot`s on a fixed tick (`EngineConfig::progress_interval`,
default 1 s) and one final `SearchEvent::Finished` snapshot. The
schema is defined in `src/search_framework/events.rs`:

```rust
pub struct ProgressSnapshot {
    pub elapsed: Duration,
    pub throughput_per_sec: MassValue,   // bits / second
    pub covered_mass: MassValue,         // bits covered so far
    pub total_mass: MassValue,           // log2(|full search space|)
    pub remaining_mass: MassValue,
    pub ttc: Option<Duration>,           // remaining_mass / throughput
    pub quality: TtcQuality,             // Direct | Projected | Hybrid
    pub edge_flow: BTreeMap<(String, String), EdgeFlowCounters>,
    pub fanout_roots: BTreeMap<u64, FanoutRootCounters>,
    pub forcings: ForcingRollups,        // stage×level + stage×feature
}
```

### TTC (mode-agnostic)

One metric, one unit across every mode:

- **unit:** search-space bits, `log2(|cube|)`.
- **`total_mass`:** `log2` of the enumeration size of the mode's
  fully-free search space (e.g. `log2(2^n × 2^n × ...)` for
  binary-valued sequence searches).
- **`covered_mass`:** Σ over stage handler calls of
  `log2(|sub-cube eliminated|)`. A handler that forces one variable
  at a decision level where `k` variables remain unfixed contributes
  `1 bit` (it halved the residual). A handler that proves a whole
  sub-tree UNSAT contributes the full `log2` of that sub-tree.
- **`throughput_per_sec`:** `covered_mass / elapsed` — bits per
  second.
- **`ttc`:** `remaining_mass / throughput_per_sec`, labelled with
  `TtcQuality`:
  - `Direct` — sampled coverage is trusted to continue; TTC is
    `elapsed / cumulative_coverage_fraction`.
  - `Projected` — TTC from an explicit branching-factor extrapolation
    (currently only sync-mode Block 2).
  - `Hybrid` — direct with projected smoothing on the remainder.

The coverage-bits unit replaces all pre-universal-review mode-specific
units (XY candidate solves, boundary count, walker nodes). Nothing
outside `ProgressSnapshot` should carry an ad-hoc TTC denominator.

### Forcing rollups (three 2-D tables)

`ForcingRollups` is published on every tick. Two of its tables are
owned by the framework coordinator; the third is read directly from
radical when the snapshot is built.

| Axis pair         | Owner        | Source                                                 |
|-------------------|--------------|--------------------------------------------------------|
| `[feature, level]` | `radical`    | `Solver::propagations_by_kind_level()` (2-D `Vec`)     |
| `[stage, level]`   | coordinator  | Sum of `ForcingDelta::by_level_feature` per stage     |
| `[stage, feature]` | coordinator  | Same source, rolled up along the other axis          |

"Feature" is a `PropKind` (`Clause`, `Pb`, `QuadPb`, `Xor`,
`Spectral`, `Mdd`, `PbSetEq`). "Level" is the SAT solver's decision
level at the moment the literal was forced. "Stage" is the framework
`StageId` of the handler that produced the forcing event (e.g.
`"boundary"`, `"solve_w"`, `"solve_z"`, `"solve_xy"`).

Sum of any one rollup equals `Solver::num_propagations()` — this is
the main correctness invariant to assert in tests.

### Fan-out and edge flow

`edge_flow: BTreeMap<(from_stage, to_stage), EdgeFlowCounters>`
tracks per-edge lifecycle counts (`spawned`, `dropped`, `queued`,
`started`, `completed`). `fanout_roots: BTreeMap<fanout_root_id,
FanoutRootCounters>` tracks the live-descendants / completed-
descendants / credited-mass for each subtree root.

Together these support the "Sankey-like text flow report" and
"per-level cut attribution" required by §8.1 of
`UNIFIED_SEARCH_FRAMEWORK_SPEC.md`.

### Deferrals, not timeouts

Stage handlers do not return "timed out". On budget exhaustion they
return a `MassDelta` (bits actually covered) plus a `Continuation`:
either `Split(children)` (residual branched into smaller items) or
`Resume(item)` (same sub-cube, saved-solver-checkpoint payload).
Both variants add their items to the same `edge_flow` and forcing
rollups as fresh work.

The TTC denominator therefore never double-counts coverage: a
handler only credits the sub-cube it actually eliminated; the rest
goes back to the queue as a smaller problem.

---

# `--wz=sync` blocks

A verbose run of `--wz=sync` emits four blocks after the search ends
(whether it found a solution, hit `--sat-secs` timeout, or exhausted
the tree). All four are written to stderr so they survive timeouts
and redirections that only capture stdout. This doc is the reader's
guide to those blocks. The blocks pre-date the universal schema
above and remain until the sync walker is ported onto the framework
engine (see `UNIFIED_SEARCH_FRAMEWORK_SPEC.md` §5.3).

Example invocation used throughout:

```bash
target/release/turyn --n=56 --wz=sync --sat-secs=30
```

## Minimal dashboard (recommended)

If the goal is to avoid over-tracking, use this compact dashboard and
ignore the rest unless debugging:

- **Primary 1: TTC_parallel**
  - For `--wz=sync`: Block 2 `TTC_parallel` (and Block 3 direct TTC as a
    consistency check).
  - For `cross/apart/together`: final `Time to cover` line.
- **Primary 2: Progress % (effective coverage)**
  - From the pipeline `Progress:` line (effective covered mass / total
    mass for that mode).
- **Primary 3: Timeout quality**
  - `XY timeout` line (rate + coverage credit behavior).
- **Primary 4: Conjecture pruning activity (only when enabled)**
  - `--conj-zw-bound rejects`.

Treat all other telemetry blocks as root-cause diagnostics, not KPIs.

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


## Smart-clause feature audit (what moves PropKind numbers vs not)

The `prop_by_kind` counters are incremented **only** when `enqueue(...)`
assigns a previously-unset variable with a non-`Decision` reason.
So these numbers are "forced literals by reason family", not total CPU
spent in each mechanism.

### Correctly reflected in current counters

- **CNF clause BCP** (including binary implications and learnt clauses)
  increments `clause` via `Reason::Clause`.
- **PB / quad-PB / PB-set-eq** propagations increment `pb`, `quadpb`,
  `pbseteq` respectively.
- **Native XOR constraints** (when added via `add_xor`) increment `xor`.
- **MDD forced literals** increment `mdd`.

### Not (fully) reflected / currently misleading

1. **Binary-watch fastpath (`bin_watch_fastpath`)**
   - Changes clause-propagation cost, but not reason type.
   - Effect appears only indirectly in wall-clock/TTC, not as a new
     per-feature counter.

2. **Clause DB maintenance (`reduce_db`, vivification, compaction)**
   - Can materially change runtime and future clause quality.
   - Not represented in `prop_by_kind`; only downstream clause forcing
     may change.

3. **Peer clause import (`add_clause_deferred`)**
   - Import activity is tracked separately (`peer_imports`), but imports
     do not increment `clause` until they later force literals.

4. **Spectral pruning in current code path**
   - The active spectral path learns/returns a clause conflict
     (`Reason::Clause`), so pruning work is attributed to `clause`, not
     `spect`.
   - `spect` only increments if spectral unit-propagation enqueues
     literals with `Reason::Spectral` (currently disabled in this path).

5. **Tseitin-encoded XOR logic**
   - If modeled as CNF clauses (current sync setup), effects are counted
     under `clause`, not `xor`.
   - `xor` counter represents only native XOR propagator activity.

6. **`xor_propagation` config flag caveat**
   - `SolverConfig` exposes this flag, but propagation is currently gated
     by constraint presence (`xor_constraints`) rather than the flag in
     the hot `propagate()` path. Treat this as a wiring gap when
     interpreting "feature on/off" experiments.

### Practical TTC implication

A SAT feature can improve TTC without moving the corresponding
`PropKind` bucket if it changes cost per propagation (fast paths,
vivification, clause exchange) instead of changing which propagator
*caused* assignments. Use PropKind together with wall-time and stage
throughput, not as a standalone cost model.

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


## Conjecture flags and telemetry (April 2026 update)

The conjecture flags are now live in CLI and pipeline modes:

- `--conj-xy-product`
- `--conj-zw-bound`
- `--conj-tuple`

How they interact with telemetry:

1. **`--wz=sync` blocks in this document are unchanged.**
   - These five blocks come from `search_sync` walker stats.
   - Current sync path does not apply conjecture toggles, so Block 2/3
     TTC values should be compared only against other sync runs with the
     same core sync settings.

2. **`cross/apart/together` print conjecture status in pipeline output.**
   - Verbose startup prints active `--conj-*` toggles.
   - `--conj-zw-bound` additionally prints a reject counter in the final
     summary (`--conj-zw-bound rejects: ...`).

3. **TTC comparison rule:**
   - If any conjecture flag is enabled, label runs as
     `conjecture-constrained` when comparing TTC to baseline.
   - In particular, `--conj-tuple` restricts tuple shells and can make
     progress/TTC look better while targeting a narrower search problem.

Practical workflow when testing conjecture impact:

- Keep mode, `n`, thread count, `--sat-secs`, and MDD settings fixed.
- Run baseline, then one flag at a time, then combined flags.
- Record both TTC and any conjecture-specific counters (especially
  `--conj-zw-bound rejects`) to separate "real pruning activity" from
  pure throughput noise.
