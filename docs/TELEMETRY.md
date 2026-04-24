# Telemetry: normative schema and implementation notes

This document has three parts:

1. **Normative schema**: the required meaning of every universal telemetry
   field.
2. **Implementation status**: what the current tree does or does not yet
   populate.
3. **Legacy sync blocks**: the sync walker's mode-specific text output.

Only Part 1 is normative. Parts 2 and 3 are explanatory.

## Part 1: Normative schema

Every run MUST emit `ProgressSnapshot`s on a fixed tick and one final
`Finished` snapshot.

The universal schema is:

```rust
pub struct ProgressSnapshot {
    pub elapsed: Duration,
    pub throughput_per_sec: MassValue,
    pub covered_mass: MassValue,
    pub total_mass: MassValue,
    pub remaining_mass: MassValue,
    pub ttc: Option<Duration>,
    pub quality: TtcQuality,
    pub edge_flow: BTreeMap<(String, String), EdgeFlowCounters>,
    pub fanout_roots: BTreeMap<u64, FanoutRootCounters>,
    pub forcings: ForcingRollups,
}
```

## 1. Elapsed / coverage / TTC

These fields MUST follow `docs/TTC.md`.

- `elapsed`: wall-clock duration covered by this run's telemetry contract
- `throughput_per_sec`: `covered_mass / elapsed`
- `covered_mass`: `covered_exact + covered_partial` as published through the
  mass model
- `total_mass`: always `1.0`
- `remaining_mass`: `max(total_mass - covered_mass, 0)`
- `ttc`: `remaining_mass / throughput_per_sec`, or `None` if rate is zero
- `quality`: `Direct | Projected | Hybrid`

The universal snapshot MUST NOT invent a mode-specific denominator outside this
fraction-based contract.

## 2. Edge flow

`edge_flow[(from_stage, to_stage)]` describes logical work transitions from one
stage to another.

### Required semantics

At minimum, every implementation MUST define `spawned` as:

- the number of logical child work items created on that edge

The metric MUST count logical work transitions, not arbitrary queue pushes.

### Continuation rules

If the framework supports split or resume:

- `Split(children)` MUST contribute one spawned count per child edge
- `Resume(item)` MUST be represented consistently

For `Resume`, an implementation MUST choose one of these two models and use it
consistently:

1. treat it as an explicit self-edge transition and count it in `edge_flow`, or
2. exclude it from `edge_flow` entirely and document that `edge_flow` covers
   only stage-to-stage transitions, not same-stage resumptions

Mixing the two interpretations is forbidden.

## 3. Fan-out roots

`fanout_roots[root_id]` tracks subtree state for one logical root of emitted
work.

### Required semantics

`live_descendants` MUST mean:

- the number of in-flight logical descendants currently outstanding for that
  root

This counter MUST:

- increment when new residual or child work becomes live
- decrement when an in-flight item completes
- include split children
- include resumed work exactly when the implementation's declared `Resume`
  accounting model treats resumed work as live descendant work
- never go negative

An implementation MUST NOT update `live_descendants` using only one class of
emission if other continuation paths also create live work.

## 4. Forcing rollups

`forcings` contains coordinator-owned rollups of forced literals by stage.

```rust
pub struct ForcingRollups {
    pub stage_level: BTreeMap<(StageId, u16), u64>,
    pub stage_feature: BTreeMap<(StageId, u8), u64>,
}
```

### Required semantics

- `stage_level[(stage, level)]` = total forced literals attributed to `stage`
  at SAT decision level `level`
- `stage_feature[(stage, feature)]` = total forced literals attributed to
  `stage` caused by propagator family `feature`

The source event is `StageOutcome::forcings`.

### Attribution rule

A stage that performs solver work MUST attribute the forcing delta caused by
that stage's own action, not the cumulative solver history of the run.

### Consistency rule

If an adapter populates both axes from the same forcing events, then:

- sum over `stage_level` MUST equal sum over `stage_feature`

This equality assumes each forcing event is attributed exactly once to one
`(stage, level, feature)` bucket. If an implementation intentionally emits
multiple attributions for one logical event, it MUST document that explicitly
and MUST NOT claim this equality as an invariant.

## 5. Deferrals instead of timeouts

The framework contract is based on credited coverage plus residual work, not a
raw timeout flag.

When a handler exhausts budget it MUST return:

1. the mass it actually covered, and
2. a continuation describing the remainder

Telemetry MUST reflect both:

- credited mass appears in TTC fields
- remaining logical work appears in edge-flow / fan-out state

The same residual search space MUST NOT be counted both as covered and as fully
live remainder.

This is the telemetry-side form of the split/resume accounting rule in
`docs/TTC.md`.

## 6. Field population requirements

The universal schema allows partial implementation, but the status of each
field MUST be clear.

### Mandatory in every mode

- `elapsed`
- `covered_mass`
- `total_mass`
- `remaining_mass`
- `ttc`
- `quality`

### Mandatory when the engine exposes staged work

- `edge_flow`
- `fanout_roots`

For this purpose, "exposes staged work" means the run is represented to the
framework as one or more `StageHandler` executions, including the degenerate
case of a single stage wrapping a whole mode.

### Mandatory when adapters can attribute stage-local forcing deltas

- `forcings.stage_level`
- `forcings.stage_feature`

If a field is structurally present but semantically unpopulated, documentation
MUST say so explicitly.

## 7. Validation rules

Implementations SHOULD check:

1. `covered_mass <= 1.0`
2. `remaining_mass >= 0`
3. `fanout_roots.live_descendants >= 0`
4. forcing totals across both forcing axes agree when both are populated
5. edge-flow semantics for split/resume are internally consistent

## Part 2: Current implementation status

This section is descriptive, not normative.

## 8. Universal TTC status

Status snapshot last audited: April 24, 2026.

The current tree uses the fraction-based TTC contract from `docs/TTC.md`.

## 9. Forcing-rollup status

As of this tree:

- `[feature, level]` exists in `radical`
- the coordinator rollups `[stage, level]` and `[stage, feature]` are wired in
  the schema
- the MDD adapter stages (`mdd.solve_w`, `mdd.solve_wz`, `mdd.solve_z`)
  populate `StageOutcome::forcings` from their primary middle-solver's
  `propagations_by_kind_level()` delta
- inline XY-path solvers inside `process_solve_z` / `process_solve_wz`
  are not yet attributed — their forcings are structurally present but
  semantically absent, matching the "intentionally partial" policy in §6
- sync / cross / stochastic adapters still leave `StageOutcome::forcings`
  empty

Readers should therefore treat empty stage-based forcing tables as “not yet
populated”, not as proof that no forcings occurred.

## 10. Edge-flow / fan-out status

As of this tree:

- `edge_flow.spawned` is the primary populated lifecycle field
- `fanout_roots.live_descendants` tracks live subtree size: incremented
  by every emitted child, every `Continuation::Split` child, and every
  `Continuation::Resume` item; decremented on handler completion
- `Continuation::Split` children each contribute one `spawned` count on
  their (parent_stage, child_stage) edge
- **Resume model (this tree's choice):** `Continuation::Resume` is
  represented as an explicit self-edge on `(from_stage, from_stage)` and
  counts one `spawned` per resumption (option 1 in §2). This model lets
  resume volume surface in `edge_flow`; the coordinator's live-descendant
  accounting treats each queued resume as live work.

## Part 3: `--wz=sync` legacy telemetry blocks

The sync walker still emits mode-specific text blocks after a run. These blocks
are not part of the universal schema, but remain authoritative for sync-mode
analysis until equivalent detail is folded into universal telemetry.

Example invocation:

```bash
target/release/turyn --n=56 --wz=sync --sat-secs=30
```

## 11. Sync dashboard

Recommended KPIs:

1. TTC
2. effective coverage progress
3. timeout coverage quality
4. conjecture pruning activity when conjectures are enabled

Treat the rest as diagnostics.

## 12. Block 1: scalar summary

```
sync_walker(parallel x16): nodes=... cap_rejects=... tuple_rejects=...
    rule_rejects=... sat_unsat=... leaves=... max_lvl=...
    elapsed=... time_to_first_leaf=... avg_nogood=.../... (...x shrink)
    peer_imports=...
```

- `nodes`: DFS visits across workers
- `cap_rejects`: walker-side capacity rejects
- `tuple_rejects`: tuple-reachability rejects
- `rule_rejects`: canonical-rule rejects
- `sat_unsat`: propagate-only UNSAT returns
- `leaves`: frames that reached full depth
- `max_lvl`: deepest level reached
- `avg_nogood`: mean learnt-clause size before and after minimization
- `peer_imports`: imported peer clauses

## 13. Block 2: TTC projection

```
TTC projection (n=...):
  level  parent   child    b_eff   note
  ...
  N_total ~= ...
  rate (nodes/s, parallel) = ...
  TTC_serial   ~= ...s
  TTC_parallel ~= ...s
```

This is the walker's projected TTC based on effective branching factors.

## 14. Block 3: per-level table

```
Per-level: lvl |   nodes |  children | proc'd | cov% |   forced | f/node |   time(s) |  t/node
...
Per-level: cumulative root-coverage (product of cov) = ...  ->  direct TTC = elapsed / coverage
Per-level: total walker-var forcings = ...
```

- `nodes`: parents visited at this level
- `children`: generated siblings
- `proc'd`: children that survived to the next DFS frame
- `cov%`: `proc'd / children`
- `forced`: walker-var forcings triggered by SAT propagation
- `f/node`: forced per parent
- `time(s)`: cumulative inclusive wall time for frames rooted here
- `t/node`: time per node

The cumulative root-coverage line is a direct cross-check against Block 2.

## 15. Block 4: per-feature forcings

```
Per-feature forcings (total 12345678): clause=... quadpb=... pbseteq=...
```

This summarizes propagation by SAT propagator family.

## 16. Block 5: per-(level, feature) matrix

```
Per-level forcings by feature: lvl | clause | quadpb | pbseteq
...
```

This is the 2-D expansion of Block 4.

## 17. Practical reading rule

For sync runs:

1. use Block 2 TTC as the headline estimate
2. use Block 3 to locate width and coverage bottlenecks
3. use Block 4 and Block 5 to identify the propagator family and depth doing
   the work
4. compare projected TTC to direct TTC as a sanity check
