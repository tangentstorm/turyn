# Unified Search Framework Specification (v1)

## Status

Proposed architecture + implementation plan for converging all `turyn search`
execution paths onto one shared scheduler/telemetry/TTC framework.

Target date for first implementation slice: **April–May 2026**.

---

## 1) Problem statement

Today, `turyn search` supports multiple solver paths (`--wz=cross|apart|together|sync`,
plus `--stochastic`). The codebase already has a strong shared core in the
MDD pipeline (`DualQueue`, workers, XY stage), but:

- scheduling is not represented through one explicit framework contract,
- TTC mass units differ by path and are only partially unified,
- `sync` is a separate engine with separate progress math,
- it is harder than necessary to add a new search path without touching
  multiple mode-specific loops.

We want one general framework that:

1. tracks TTC faithfully under a single contract,
2. distributes work across threads consistently,
3. allows all current `turyn search` paths to plug into the same execution
   model,
4. makes new search configurations easy to add.

---

## 2) Design goals and non-goals

### Goals

1. **One scheduler/runtime** for all search modes.
2. **One TTC contract** with explicit denominator/numerator/rate types.
3. **Mode adapters** convert existing logic into shared work-item interfaces.
4. **Extensible stages** (add/remove/reorder stage handlers without copying
   worker orchestration code).
5. **Deterministic replay option** (seeded ordering), while preserving parallel
   throughput.
6. **Incremental migration** with correctness parity at each phase.

### Non-goals (v1)

1. Rewriting SAT kernels (`radical`, `xy_sat`, `sat_z_middle`) in this phase.
2. Changing mathematical pruning semantics in this phase.
3. Forcing exact TTC for inherently estimated/infinite spaces (e.g. stochastic)
   in v1; instead, expose explicit estimate quality classes.

---

## 3) High-level architecture

Introduce a new crate/module boundary:

- `src/search_framework/` (new)
  - `engine.rs` (runtime + worker pool)
  - `queue.rs` (generalized DualQueue)
  - `mass.rs` (TTC/SearchMass contract)
  - `events.rs` (progress/final event model)
  - `stage.rs` (stage traits + stage outputs)
  - `mode_adapters/` (cross/apart/together/sync/stochastic adapters)

The framework executes a **SearchGraph**:

- nodes are stage handlers,
- edges are emitted follow-up work items,
- all work enters one shared scheduler,
- scheduler prioritization is policy-driven (not hard-coded per mode),
- all stage outcomes report mass-coverage deltas and diagnostics through one
  event stream.

### 3.1 Core abstractions

## `SearchModeAdapter`

Owns mode-specific initialization and stage registration.

Responsibilities:

- build mode context,
- register initial seeds,
- provide stage handlers,
- provide mode-specific mass model implementation.

## `WorkItem`

Typed payload with common metadata:

- `stage_id`
- `priority`
- `cost_hint`
- `origin`
- `mass_hint` (optional estimated subtree mass)
- `replay_key` (for deterministic ordering)

## `StageHandler`

Pure-ish unit of search expansion:

- consumes `WorkItem` + shared context,
- may emit:
  - additional `WorkItem`s,
  - candidate solutions,
  - terminal failures,
  - mass accounting updates.

## `SearchMassModel`

Single TTC interface:

- `total_mass()`
- `covered_mass()`
- `remaining_mass()`
- `coverage_quality()` (`Exact | Estimated | LowerBound | Hybrid`)

The engine computes:

- `coverage_rate = covered_mass / elapsed`
- `ttc = remaining_mass / coverage_rate`

and labels TTC quality from `coverage_quality()`.

## `SchedulerPolicy`

Generalized policy replacing fixed DualQueue behavior.

Baseline policy (`GoldThenWork`) reproduces current semantics:

- XY-like high-value items first,
- then producer-stage items,
- starvation guard with configurable fairness window.

Additional policies can be introduced without changing worker code.

---

## 4) TTC contract (framework-wide)

A single mass unit is required **per mode run** (not globally identical across
all modes). The contract is unified by interface and accounting algebra.

### 4.1 Required fields

Each mode must define:

1. `mass_total`:
   - exact when possible,
   - otherwise estimated with confidence class.
2. `mass_covered_exact`:
   - fully resolved subproblems.
3. `mass_covered_partial`:
   - timeout/progressive credit, normalized to the same unit.
4. `mass_remaining = mass_total - (mass_covered_exact + mass_covered_partial)`.

### 4.2 Quality labeling

Engine emits:

- `ttc_exact` when total and coverage are exact,
- `ttc_estimated` otherwise, with attribution:
  - denominator estimate,
  - partial-credit model,
  - projection-based estimate.

### 4.3 Mode mappings (initial)

- `cross`: mass unit = effective XY candidate solves.
- `apart/together`: mass unit = weighted boundary mass (not raw boundary count;
  use boundary × XY-mass estimate in v1.5).
- `sync`: mass unit = walker-node mass under coverage product model.
- `stochastic`: mass unit = sampled-trajectory coverage (estimate class only;
  no exact TTC guarantee).

---

## 5) Unifying existing paths

### 5.1 `--wz=apart` and `--wz=together`

These already fit staged execution best. Migration strategy:

- keep existing stage logic (`Boundary`, `SolveW`, `SolveWZ`, `SolveZ`, `SolveXY`),
- wrap each as `StageHandler`,
- replace direct DualQueue usage with `SchedulerPolicy::GoldThenWork`.

### 5.2 `--wz=cross`

Reframe producer and consumer as standard stages:

- `TupleSeed` stage
- `CrossPairGen` stage (Z/W generation and spectral pair filter)
- `SolveXY` stage (shared existing consumer)

This removes special-case orchestration while retaining current solver internals.

### 5.3 `--wz=sync`

Wrap walker loop as staged frontier expansion:

- `SyncNodeExpand` stage emits child prefix items,
- SAT propagate outcome updates partial/exact mass,
- leaf verification emits solution event.

Clause sharing remains a mode-internal service in adapter context.

### 5.4 `--stochastic`

Integrate as a mode adapter for consistency of threading + event reporting:

- items represent restart windows / trajectories,
- emits estimate-only TTC and explicit non-exhaustive flag,
- remains logically non-complete but operationally framework-compatible.

---

## 6) Threading model

Engine runtime:

1. one shared concurrent scheduler,
2. N workers (`TURYN_THREADS` / default parallelism),
3. one progress reporter (periodic snapshot from atomic counters),
4. optional feeder tasks (mode adapters can register background producers).

### 6.1 Backpressure and fairness

- per-stage queue budgets,
- bounded in-flight items per stage,
- starvation prevention (age-based boost),
- cancellation token checked at stage boundaries.

### 6.2 Determinism controls

- global run seed,
- per-stage deterministic replay keys,
- optional deterministic scheduling mode for debugging.

---

## 6.3 Fan-out jobs: accounting and visualization

Many stages naturally fan out:

- one boundary can yield many `W` candidates,
- one `W` can yield many `(W,Z)` pairs,
- one `(W,Z)` can yield many `XY` SAT jobs.

The framework must treat this as first-class rather than implicit queue growth.

### Fan-out identity model

Each `WorkItem` carries lineage metadata:

- `item_id` (globally unique),
- `parent_item_id` (optional),
- `fanout_root_id` (root of a spawned sub-tree),
- `depth_from_root`,
- `spawn_seq` (stable child index under parent for deterministic replay).

`StageOutcome` reports both emitted children and a compact fan-out summary:

- `children_emitted`,
- `children_dropped` (prefiltered before enqueue),
- `children_merged` (dedup/coalesced),
- `fanout_mass_emitted` (estimated + exact components).

### Fan-out lifecycle counters

Track lifecycle per fan-out root and per stage edge `(A -> B)`:

- spawned, queued, started, completed, cancelled, timed_out,
- effective coverage credit from descendants,
- live descendants currently in-flight.

This yields exact answers to:

- "how many sub-jobs did this parent create?"
- "how much of that subtree has been covered?"
- "which edge is exploding queue size?"

### Visualization requirements

Progress output should include a compact fan-out panel:

1. **Edge expansion table** (rolling and cumulative):
   - `Boundary->SolveW`, `SolveW->SolveZ`, `SolveZ->SolveXY`, etc.
   - show `avg children/parent`, `p50`, `p95`, and `drop rate`.
2. **Live subtree pressure**:
   - top-K `fanout_root_id`s by live descendants and by remaining mass.
3. **Stage waterfall**:
   - spawned -> filtered -> queued -> started -> completed counts per edge.

Post-run artifact (JSON/CSV) should support Sankey or flamegraph-like rendering
of fan-out flow, so large branch factors are visually obvious.

### Scheduler hooks for fan-out

Scheduler policy uses fan-out signals to avoid runaway producers:

- per-edge in-flight caps,
- adaptive priority dampening when an edge exceeds target expansion ratio,
- optional token-bucket for high-fan-out edges (e.g. `SolveW->SolveZ`).

This preserves throughput while preventing one prolific parent from starving
other roots.

---

## 7) Data model and API sketch

(Names are normative; exact signatures may vary slightly.)

```text
trait SearchModeAdapter {
  fn name(&self) -> &'static str;
  fn init(&self, cfg: &SearchConfig) -> AdapterInit;
  fn stages(&self) -> Vec<Arc<dyn StageHandler>>;
  fn mass_model(&self) -> Arc<dyn SearchMassModel>;
}

trait StageHandler {
  fn id(&self) -> StageId;
  fn handle(&self, item: WorkItem, ctx: &StageContext) -> StageOutcome;
}

struct StageOutcome {
  emitted: Vec<WorkItem>,
  mass_delta: MassDelta,
  fanout_delta: FanoutDelta,
  solution: Option<SolutionRecord>,
  diagnostics: SmallVec<[DiagEvent; 4]>,
}

struct WorkItemMeta {
  item_id: u64,
  parent_item_id: Option<u64>,
  fanout_root_id: u64,
  depth_from_root: u16,
  spawn_seq: u32,
}

trait SearchMassModel {
  fn total_mass(&self) -> MassValue;
  fn covered_mass(&self) -> MassValue;
  fn quality(&self) -> CoverageQuality;
}
```

---

## 8) Observability requirements

All modes emit the same top-level progress schema:

- elapsed,
- throughput (mass/sec),
- covered / total / remaining mass,
- TTC and quality label,
- stage in/out counters,
- timeout coverage quality,
- optional mode-specific diagnostics.

This preserves rich `sync` diagnostics while making cross-mode dashboards
consistent.

### 8.1 Required built-in reports (must survive unification)

The unified framework must preserve (and standardize) two existing report
families:

1. **Sankey-like text flow report**
   - Human-readable text table that shows flow through stage edges:
     `in -> filtered -> queued -> started -> completed`, plus rates.
   - Must be available live (periodic snapshots) and final (whole-run totals).
   - Must support grouping by tuple/sum shell and by fan-out root.

2. **Search-space cut attribution report (by variable level)**
   - Matrix-style report: rows = variable level/depth, columns = pruning/cut
     source (canonical rules, spectral filters, SAT propagation families,
     capacity checks, conjecture filters, etc.).
   - Each cell reports both absolute cuts and fractional cut share at that
     level.
   - Must include cumulative remaining-mass curve so cut attribution and TTC
     effects can be interpreted together.

### 8.2 Unified run artifact for post-hoc visualization

Every run should optionally emit a structured artifact (`.jsonl` or `.json`)
that can drive either Sankey or workstation-flow visualization without rerun.

Minimum schema blocks:

- `stages`: stage metadata (`stage_id`, label, worker pool, concurrency caps).
- `edge_flow_timeseries`: per edge and time bucket:
  - arrivals, drops, queue depth, starts, completions, service time stats.
- `stage_capacity_timeseries`: per stage and time bucket:
  - available workers, busy workers, queue depth, throughput, backpressure flags.
- `cut_attribution`: per level × cut-source matrix with totals and rates.
- `mass_timeseries`: covered/remaining mass and TTC estimate trajectory.

This artifact is the canonical source for:

- text Sankey-style reports,
- future graphical Sankey diagrams,
- future "workstation" flow diagrams (queue/throughput/utilization by stage).

### 8.3 Workstation-flow view requirements

To support the requested flow diagram (available work queue, processing speed,
throughput per workstation/task type), each stage must expose:

- `queue_depth_now`,
- `items_started_per_sec`,
- `items_completed_per_sec`,
- `p50/p95 service_time`,
- `worker_utilization` (`busy / available`),
- `blocking_reason` (none, queue cap, downstream cap, SAT budget, etc.).

---

## 9) Implementation plan (incremental)

## Phase 0 — Baseline freeze and contract tests

1. Capture current TTC/progress output snapshots for `cross`, `apart`,
   `together`, `sync` at representative `n`.
2. Add golden tests for TTC algebra invariants (no negative remaining mass,
   monotonic covered mass, etc.).
3. Add benchmark harness to compare pre/post migration throughput.

Deliverable: safety net for refactor.

## Phase 1 — Framework skeleton

1. Add `src/search_framework/` with runtime/scheduler/mass interfaces.
2. Implement `GoldThenWork` scheduler policy to mirror current DualQueue.
3. Add generic worker loop + event bus + progress reporter.
4. Add lineage/fan-out counters and edge-expansion telemetry plumbing.
5. Add report adapters for (a) sankey-like text flow and (b) per-level cut attribution.

Deliverable: framework compiles, but old execution paths still active.

## Phase 2 — Migrate apart/together first

1. Wrap existing MDD stages into `StageHandler`s.
2. Route `--wz=apart|together` through framework engine.
3. Validate parity vs baseline for:
   - solution correctness,
   - TTC trend,
   - throughput.

Deliverable: DualQueue internals replaced by framework policy for these modes.

## Phase 3 — Migrate cross

1. Factor cross producer into staged handlers.
2. Reuse shared `SolveXY` stage handler.
3. Switch `--wz=cross` to framework path.

Deliverable: all MDD-backed exhaustive modes unified.

## Phase 4 — Migrate sync

1. Implement sync walker adapter with node-expansion stage.
2. Bridge existing telemetry into shared event schema.
3. Keep advanced sync tables as mode-specific diagnostics.

Deliverable: `--wz=sync` runs through same engine.

## Phase 5 — Integrate stochastic adapter

1. Wrap stochastic restarts as framework items.
2. Mark coverage quality as estimated/non-exhaustive.
3. Align CLI progress and final summaries.

Deliverable: every `turyn search` path uses one runtime.

## Phase 6 — TTC fidelity upgrade (v1.5)

1. Replace apart/together denominator from boundary count to weighted
   boundary mass.
2. Add per-boundary timeout credit accumulation to reduce global shortfall bias.
3. Publish one canonical TTC field across modes with explicit quality metadata.

Deliverable: faithful TTC comparability improvements and clearer uncertainty.

---

## 10) Acceptance criteria

1. **Single runtime path:** all search modes instantiate `SearchEngine`.
2. **No mode-specific worker loops** remain in `main.rs`.
3. **Common progress schema** visible in logs for every mode.
4. **Fan-out visibility:** per-edge expansion metrics and live subtree pressure are emitted in progress snapshots.
5. **Required reports preserved:** sankey-like text flow report and per-level cut-attribution report are both available from unified runs.
6. **TTC contract enforced** by unit/property tests.
7. **Performance guardrail:** no >10% regression at `n=18` smoke modes,
   unless explicitly waived with profiling evidence.
8. **Extensibility demo:** add one synthetic example mode in tests with only
   adapter+stages (no runtime edits).

---

## 11) Risk register and mitigations

1. **Risk: throughput regression due to abstraction overhead**
   - Mitigation: keep stage handlers zero-allocation where possible,
     prefer `SmallVec`, preallocate item pools.
2. **Risk: TTC discontinuity during migration**
   - Mitigation: side-by-side old/new TTC counters in shadow mode during phases 2–4.
3. **Risk: sync clause-sharing semantics change accidentally**
   - Mitigation: keep clause exchange as adapter-owned service untouched in phase 4.
4. **Risk: queue starvation under mixed stage costs**
   - Mitigation: age boosting + per-stage budget caps + fairness tests.

---

## 12) Immediate next coding tasks

1. Add `search_framework` module skeleton and feature-gate it.
2. Implement `MassValue`, `CoverageQuality`, `MassDelta` and TTC unit tests.
3. Port existing `DualQueue` into `SchedulerPolicy::GoldThenWork` without
   behavior change.
4. Create `ApartAdapter` and `TogetherAdapter` wrappers around current stage
   code paths.
5. Add `--engine=new|legacy` hidden flag for A/B verification during migration,
   then remove once parity is proven.

---

## 13) Decision log (this proposal)

1. Keep one mass unit per mode run, unified by algebra and metadata, rather than
   forcing a single global physical unit prematurely.
2. Migrate highest-overlap modes first (`apart/together`) to derisk.
3. Treat scheduler policy as pluggable so DualQueue behavior is preserved while
   enabling future alternatives.
4. Preserve existing solver kernels and pruning semantics in initial refactor.

