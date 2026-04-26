# Pipeline Overview

This document is the current high-level map of the Turyn search pipeline.
It merges the old operational pipeline notes with the useful framework
architecture that used to live in the unified framework proposal.

Authoritative contracts:

- `../SPEC.md` - top-level invariants future refactors must preserve
- `TTC.md` - normalized TTC accounting contract
- `TELEMETRY.md` - progress/forcing/fan-out telemetry contract
- `CANONICAL.md` - BDKR canonicalization rules and correctness notes

The old unified framework proposal has been folded into this document.
Its superseded `log2(|cube|)` TTC ledger must not be revived.

## 1. Mathematical Problem

A Turyn-type quadruple `TT(n)` is four `+/-1` sequences:

- `X`, `Y`, `Z` of length `n`
- `W` of length `n - 1`

They satisfy the aperiodic autocorrelation identity

```text
N_X(s) + N_Y(s) + 2*N_Z(s) + 2*N_W(s) = 0    for every s >= 1
```

and the sum-squared invariant

```text
sigma_X^2 + sigma_Y^2 + 2*sigma_Z^2 + 2*sigma_W^2 = 6n - 2
```

The spectral form gives the necessary pair bound

```text
|Z(w)|^2 + |W(w)|^2 <= 3n - 1
```

for every frequency. Most pruning in the solver enforces either the
autocorrelation identity, BDKR canonicalization, sum feasibility, or
this spectral bound.

## 2. Runtime Shape

The search binary routes all current search modes through the shared
framework runtime:

```text
main
  parse SearchConfig
  enumerate or select sum tuples when needed
  choose effective WzMode
  build one SearchModeAdapter
  run SearchEngine with LaneByPriority scheduler
```

The shared framework is in `src/search_framework/`:

- `engine.rs` - coordinator thread, worker pool, progress snapshots
- `queue.rs` - priority/gold-lane scheduler policy
- `stage.rs` - `WorkItem`, `StageHandler`, `StageOutcome`, continuations
- `mass.rs` - normalized TTC mass model
- `events.rs` - progress, edge-flow, fan-out, forcing rollups
- `mode_adapters/` - per-mode adapters

The coordinator owns global accounting. Worker threads are
interchangeable and pull work from scheduler lanes.

## 3. Search Modes

### 3.1 `--wz=apart` and `--wz=together`

Adapter: `MddStagesAdapter`

These are the MDD-backed exhaustive modes. They enumerate live MDD
boundaries and then solve the missing middle pieces.

Pipeline:

```text
Boundary
  -> SolveW -> SolveZ -> inline XY solves       (--wz=apart)
  -> SolveWZ -> inline XY solves                (--wz=together)
```

The boundary stage starts from a `(z_bits, w_bits, xy_root)` MDD
boundary. It checks tuple feasibility and whether the XY subspace has
any compatible boundary candidate.

`apart` solves W middles first, then solves Z middles against each W.
`together` uses one combined W+Z SAT call. Both eventually use the
same XY SAT fast path through `SolveXyPerCandidate`.

TTC quality is currently `Hybrid`: exact boundary completion is a real
additive fraction, while timeout partial credit is approximate and must
stay bounded/non-duplicated.

### 3.2 `--wz=cross`

Adapter: `CrossAdapter`

Cross mode is a brute-force Z/W producer wrapped as a framework stage.
It enumerates full Z and W candidates for each tuple, filters them by
individual and pair spectral constraints, deduplicates by ZW
autocorrelation, then brute-forces XY boundary codes for each surviving
pair.

Current shape:

```text
cross.enumerate
  for each tuple
    build/reuse W candidates by |sigma_W|
    enumerate Z candidates
    spectral pair check
    brute-force XY boundary codes up to the cross k cap
    try XY SAT candidate
```

Cross mode uses uniform tuple weighting today, so its TTC label remains
`Hybrid` rather than `Direct`.

### 3.3 `--wz=sync`

Adapter: `SyncAdapter`

Sync mode wraps the synchronized four-sequence walker inside the shared
framework so universal snapshots are emitted consistently. It does not
use a prebuilt MDD file or a separate Z/W-to-XY handoff. One persistent
SAT solver encodes all four sequences and the DFS walker feeds it
assumptions in bouncing position order.

Key properties:

- no tuple pre-enumeration
- no MDD boundary file
- persistent CDCL solver
- propagate-only walker calls
- learned clauses persist across the walk
- rich mode-specific sync telemetry remains authoritative

The universal TTC label is `Projected` for sync. Its mode-specific
coverage-product and branching-factor estimates are useful diagnostics,
but they are not a `Direct` normalized TTC claim.

### 3.4 `--stochastic`

Adapter: `StochasticAdapter`

Stochastic mode is non-exhaustive guess/search infrastructure. It runs
through the framework for consistent lifecycle and output shape, but it
must be treated as estimate-only/non-complete unless explicitly proven
otherwise.

## 4. Scheduler And Work Semantics

All ordinary workers pull `WorkItem`s from the shared scheduler.

Each item carries:

- `stage_id`
- `priority`
- `gold`
- `cost_hint`
- `replay_key`
- optional `mass_hint`
- lineage metadata (`item_id`, `parent_item_id`, `fanout_root_id`,
  `depth_from_root`, `spawn_seq`)

Priority encodes pipeline depth. Later stages have higher priority so
the system drains downstream work before producing more upstream work.
This is intentional throughput behavior: avoid work in progress sitting
around when it can retire search mass.

The `gold` flag is an explicit experimental promotion lane. It may bias
order, but it must not change completeness or accounting.

Work may be split, resumed, deferred, or left incomplete by cancellation.
In an exhaustive run, work must not be abandoned. A timeout is not UNSAT
and is not exact coverage.

## 5. TTC And Telemetry

`docs/TTC.md` is authoritative. The universal TTC ledger is normalized:

```text
total_mass = 1.0
covered_mass = covered_exact + covered_partial
coverage_rate = covered_mass / elapsed
TTC = (1.0 - covered_mass) / coverage_rate
```

Mass values are fractions in `[0, 1]`. Exact and partial credit must
refer to the same denominator, and completed regions must not be
credited twice.

Every progress snapshot includes:

- elapsed time
- throughput per second
- covered, total, and remaining mass
- TTC
- quality label: `Direct`, `Hybrid`, or `Projected`
- edge-flow counters
- fan-out root counters
- forcing rollups

Forcing telemetry has two coordinator-owned rollups:

- `[stage, level]`
- `[stage, feature]`

The solver also owns `[feature, level]` through its propagation counters.

## 6. Threading Model

The framework runtime has one coordinator and `N` worker threads:

1. The coordinator seeds initial work from the selected adapter.
2. Workers wait on the shared scheduler.
3. A worker pops one item, runs the matching `StageHandler`, and sends
   a report back to the coordinator.
4. The coordinator applies mass, forcings, edge-flow, fan-out updates,
   and pushes emitted or continued work back into the scheduler.
5. The coordinator emits periodic progress snapshots and one final
   finished snapshot.

The scheduler is protected by a mutex/condition variable. Workers do not
own stage-specific queues. This preserves load balancing and lets every
thread run the deepest available work.

Cancellation is a live atomic flag visible in `StageContext`. Long
handlers must poll it inside inner loops.

Deferral contract:

- A budget-exhausted handler returns the mass it actually covered.
- The uncovered residual must be represented as `Continuation::Split`,
  `Continuation::Resume`, or an explicitly incomplete/cancelled run.
- Residual work must not be counted both as covered and still-live full
  work.

## 7. Data Model And API

Current framework interfaces, simplified:

```text
trait SearchModeAdapter<T> {
  fn name(&self) -> &'static str;
  fn init(&self) -> AdapterInit<T>;
  fn stages(&self) -> BTreeMap<StageId, Box<dyn StageHandler<T>>>;
  fn mass_model(&self) -> Box<dyn SearchMassModel>;
}

trait StageHandler<T> {
  fn id(&self) -> StageId;
  fn handle(&self, item: WorkItem<T>, ctx: &StageContext) -> StageOutcome<T>;
}

struct WorkItem<T> {
  stage_id: StageId,
  priority: i32,
  gold: bool,
  cost_hint: u32,
  replay_key: u64,
  mass_hint: Option<f64>,
  meta: WorkItemMeta,
  payload: T,
}

struct StageOutcome<T> {
  emitted: Vec<WorkItem<T>>,
  continuation: Continuation<T>,
  mass_delta: MassDelta,
  fanout_delta: FanoutDelta,
  diagnostics: Vec<DiagEvent>,
  forcings: ForcingDelta,
}

enum Continuation<T> {
  None,
  Split(Vec<WorkItem<T>>),
  Resume(WorkItem<T>),
}

trait SearchMassModel {
  fn total_mass(&self) -> MassValue;        // default 1.0
  fn covered_mass(&self) -> MassValue;      // exact fraction
  fn covered_partial_mass(&self) -> MassValue;
  fn total_log2_work(&self) -> Option<f64>; // benchmark stop only
  fn quality(&self) -> TtcQuality;
}
```

`edge_flow.spawned` is the populated edge-flow lifecycle field today.
`fanout_roots.live_descendants` tracks currently outstanding descendants
per root.

## 8. Known-Good Anchors

For correctness checks, prefer catalogue-backed anchors and known
solutions rather than performance-only counters.

### Known `TT(26)`

```text
X = ++--+--+++++++-+-++--+-++-
Y = +++++-++++++-++-+---+-++--
Z = +++-+--++++++--++---+-+--+
W = ++++-+---+--+++--++++-+-+
```

Properties:

- sum tuple `(6, 6, 4, 5)`
- `sigma_X^2 + sigma_Y^2 + 2*sigma_Z^2 + 2*sigma_W^2 = 154 = 6n - 2`
- at `k = 7`, the canonical boundary is live in the MDD
- the `known_tt26_verifies` unit test verifies the tuple

The full catalogue counts through `n=32` are listed in `../SPEC.md`.

## 9. Offline Artifacts

The main offline artifact is the MDD:

- `gen_mdd K` -> `mdd-K.bin`
- `gen_mdd_bfs K` -> alternative BFS builder for large `K`

Flat `xy-table-k*.bin` tables are retired for the current primary
pipeline. Historical docs and logs may still mention `gen_table`, but
future work should treat the MDD and framework adapters as the current
path unless deliberately reviving a table experiment.

## 10. Reading Old Logs

Older logs use old names and counters:

- `run_hybrid_search` roughly maps to current cross-mode adapter work.
- `run_mdd_sat_search` roughly maps to current MDD staged adapter work.
- `DualQueue` roughly maps to the current priority/gold-lane scheduler.
- `xy/s`, `paths/s`, `live_zw_paths`, and `eff` are historical proxies
  for denominator, rate, or shortfall effects.

When in doubt, the current interpretation rule is:

1. Did the denominator change?
2. Did normalized covered mass change?
3. Did normalized coverage rate change?
4. Did the quality/completeness label change?
