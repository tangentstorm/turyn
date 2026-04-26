# Turyn Solver Specification

This file is the top-level contract for future changes. It is intentionally
short: detailed rules live in `docs/TTC.md`, `docs/TELEMETRY.md`,
`docs/PIPELINE.md`, and `docs/CANONICAL.md`. If a refactor conflicts with this
file, the refactor is wrong unless this file is deliberately updated first.

## Completeness And Correctness

- A search mode is exhaustive unless it is explicitly labeled otherwise.
- No pruning rule, conjecture, cache, optimization, queue policy, or timeout
  path may silently remove a valid Turyn solution.
- Conjecture-restricted runs MUST be labeled as such in user-facing output and
  MUST NOT be presented as unconstrained coverage.
- Any optimization that changes the searched space must state whether it
  shrinks the denominator, increases covered mass, or improves coverage rate.
- Known canonical counts for `TT(n)` through `n=32` are mandatory sanity
  anchors:

| n | 2 | 4 | 6 | 8 | 10 | 12 | 14 | 16 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| classes | 1 | 1 | 4 | 6 | 43 | 127 | 186 | 739 |

| n | 18 | 20 | 22 | 24 | 26 | 28 | 30 | 32 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| classes | 675 | 913 | 3105 | 3523 | 3753 | 4161 | 4500 | 6292 |

The `TT(32)` count uses the complete local catalogue
`data/turyn-type-32`, including the 66 London additions noted in
`data/README.md`. The pre-addition original file has 6226 entries.

## Work And Scheduling

- Work may be split, resumed, deferred, reprioritized, or left incomplete by a
  cancelled run. In an exhaustive run, work MUST NOT be abandoned.
- Timeout-tainted residual work must re-enter the scheduler explicitly, or the
  run must be labeled incomplete. A timeout is not UNSAT and is not exact
  coverage.
- All ordinary solver workers are interchangeable. They pull from shared
  scheduler lanes; they do not own permanent stage-specific queues.
- The scheduler must preserve throughput: downstream work that can retire
  search mass should not sit idle behind upstream producer work.
- Experimental priority lanes, including a gold lane, may bias order but MUST
  NOT affect completeness, mass accounting, or replayable run interpretation.
- The coordinator/main thread owns global accounting: queue and buffer
  monitoring, TTC mass, pruned/UNSAT regions, progress snapshots, and final run
  status.

## Metrics And Accounting

- `docs/TTC.md` is the authoritative TTC contract. TTC mass is a normalized
  additive fraction in `[0, 1]`; older notes that describe summed
  `log2(|cube|)` mass are not authoritative.
- Exact credit requires a fully discharged region with no residual work.
- Partial credit must be in the same denominator as exact credit, must be
  bounded by the subproblem it came from, and must be credited exactly once.
- Covered mass must be monotone, must never exceed total mass, and must not
  double-count partial credit that is later subsumed by exact credit.
- Split and resume paths must conserve search mass: credited mass plus queued
  residual mass equals the incoming logical work.
- Telemetry counts logical work transitions, not arbitrary queue pushes.
- Quality labels (`Direct`, `Hybrid`, `Projected`) must describe the actual
  estimator. If in doubt, use the weaker label.

## Fragile Areas

These areas have been fixed more than once and must be treated as load-bearing:

- partial/exact TTC double-counting, especially timeout partial credit later
  subsumed by exact completion;
- timeout vs UNSAT attribution in W, Z, WZ, and XY paths;
- stale solver state and stale cache reuse across SAT calls;
- queue/fanout conservation, including split and resume self-edges;
- store ordering where a progress poll could briefly over-report coverage;
- conjecture and mode labels in progress and final summaries.

## Validation Anchors

Before trusting a long run, the implementation must preserve:

- known-solution acceptance through the relevant pipeline path;
- canonical-count sanity checks for catalogue-covered `n`;
- TTC invariants from `docs/TTC.md`;
- telemetry invariants from `docs/TELEMETRY.md`;
- honest mode/conjecture quality labels;
- reproducible fixed-work benchmarking when determinism controls are pinned.
