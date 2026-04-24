# TTC (Time to Cover): normative specification

This document is the canonical specification for the **TTC** metric used by
all search modes.

It is intentionally normative. Statements using **MUST**, **MUST NOT**,
**SHOULD**, and **MAY** define the required behavior of the implementation.
Mode-specific implementation notes or examples belong elsewhere.

## 1. Core contract

Every search mode MUST expose one uniform notion of progress:

- `total_search_mass`
- `covered_exact`
- `covered_partial`
- `covered_mass = covered_exact + covered_partial`
- `coverage_rate = covered_mass / elapsed`
- `remaining_mass = total_search_mass - covered_mass`
- `TTC = remaining_mass / coverage_rate`

Under the current universal contract:

- `total_search_mass MUST equal 1.0`
- all mass values MUST be fractions in `[0, 1]`
- `covered_mass MUST be additive over disjoint subproblems`

This normalization is part of the public metric contract. An adapter's
denominator is the full search space assigned to that adapter, normalized to
`1.0`; any per-adapter weighting or scaling is an internal implementation
detail.

Equivalent form:

- `TTC = elapsed * (total_search_mass - covered_mass) / covered_mass`

If `coverage_rate <= 0`, TTC MUST be reported as unavailable rather than as
an arbitrary sentinel.

## 2. Required semantic meaning

Each adapter MUST define:

1. a denominator: the full search space that adapter is responsible for,
2. an exact numerator: the fraction of that space fully discharged,
3. a partial numerator: fractional credit from interrupted work,
4. a rate derived from that same covered fraction.

The denominator and numerator MUST refer to the same search space. An adapter
MUST NOT compute its denominator in one unit and its numerator in another.

Examples of forbidden behavior:

- denominator = boundary count, numerator = solver decisions
- denominator = unconstrained problem mass, numerator = conjecture-restricted
  mass without explicit relabeling
- denominator = logical subproblems, numerator = scheduler events

## 3. Mass invariants

All implementations MUST satisfy these invariants:

1. `0 <= covered_exact <= total_search_mass`
2. `0 <= covered_partial <= total_search_mass - covered_exact`
3. `covered_mass = covered_exact + covered_partial`
4. `0 <= covered_mass <= total_search_mass`
5. `remaining_mass = max(total_search_mass - covered_mass, 0)`
6. `covered_mass` MUST be monotone non-decreasing over time
7. no completed subproblem may be credited more than once

In particular:

- exact credit and partial credit MUST be clamped so their sum never exceeds
  `1.0`
- if a residual subproblem is split or resumed, already-credited mass MUST NOT
  be re-credited when the residual work later completes

## 4. Exact vs partial coverage

### 4.1 `covered_exact`

`covered_exact` is the fraction of the search space that has been fully
resolved. A subproblem counts as exact coverage only when no residual work
remains for that subproblem.

Exact coverage MUST be additive over disjoint subproblems.

### 4.2 `covered_partial`

`covered_partial` is fractional credit from interrupted work, such as a SAT
timeout that still pruned part of a sub-cube before the budget was exhausted.

Partial credit MUST obey these rules:

1. it MUST be measured in the same fraction unit as `covered_exact`
2. it MUST represent only the eliminated portion of the interrupted subproblem
3. it MUST NOT include residual work that is re-queued, split, or resumed
4. it MUST be added exactly once per interrupted attempt
5. it MUST remain attributable even when one stage bundles many internal
   sub-attempts, per the bundled-stage rule in Section 5.3

If a stage internally executes multiple timeout-capable child solves, the
adapter MUST aggregate the partial credit from all of them before returning or
publishing a progress snapshot. It is not acceptable to credit only one
variant of a logically-equivalent path.

## 5. Split / resume semantics

The framework supports handlers that return residual work through splitting or
resumption. TTC accounting MUST follow the logical search mass, not queue
mechanics.

### 5.1 Split

When a handler splits a residual subproblem into child items:

- the parent MAY credit exact mass already eliminated
- the parent MAY credit partial mass already eliminated
- the residual children MUST represent only the uncredited remainder
- the sum of child residual mass plus credited parent mass MUST equal the
  parent's incoming mass

If the adapter cannot compute that equality exactly because it uses an
approximate weighting model, the approximation MUST still preserve the
monotonicity and non-double-counting rules above, and the adapter MUST label
the published TTC as `Hybrid` or `Projected`, not `Direct`.

### 5.2 Resume

When a handler resumes the same logical subproblem later:

- progress already credited before the resume MUST persist
- resumed work MUST NOT be treated as a fresh full-mass subproblem
- completion of the resumed item MUST credit only the remaining uncovered mass

### 5.3 Bundled stages

If one stage bundles multiple internal solves, the implementation MUST still
behave as though each internal solve contributed to the same global coverage
ledger. The stage boundary MUST NOT cause partial credit to disappear.

## 6. Quality labels

Every published TTC value MUST carry a quality label:

- `Direct`
- `Projected`
- `Hybrid`

Conservatism order is:

- `Direct` = strongest claim
- `Hybrid` = intermediate claim
- `Projected` = weakest claim

"Most conservative correct label" means the adapter MUST choose the weakest
label that is still true.

### 6.1 `Direct`

Use `Direct` only when published coverage is a real additive fraction of the
 search space.

### 6.2 `Projected`

Use `Projected` when the published coverage is estimate-only. The estimate MAY
be useful operationally, but consumers MUST treat mode-specific telemetry as
authoritative.

### 6.3 `Hybrid`

Use `Hybrid` when the published value combines:

- a direct exact fraction, and
- an estimated or approximate partial fraction

Adapters MUST choose the most conservative correct label. If there is doubt,
they SHOULD prefer `Hybrid` or `Projected` over `Direct`.

## 7. Per-mode specification

This section defines the required meaning for each active mode.

## 7.1 `--wz=cross`

### Work unit

- tuple shells

### Denominator

- the full tuple-shell search space assigned to the run

### Exact coverage

- fraction of tuple-shell mass fully processed

### Partial coverage

- if cross mode contains timeout-capable internal sub-solves that can report
  eliminated search mass, it MUST surface that mass as `covered_partial`
- if it does not surface such credit, the adapter MUST document that omission
  and its quality label MUST remain non-`Direct`

### Quality

- `Hybrid` unless tuple shells are weighted by true search mass
- cross MUST remain non-`Direct` until both tuple weighting and any timeout
  partial-credit path are direct in the same search-mass unit

Uniform tuple weighting is permitted as an approximation, but if used it MUST
be labeled as approximate and MUST NOT be described as a direct XY-work
fraction.

## 7.2 `--wz=apart` and `--wz=together`

These two modes MUST obey the same TTC contract, even if they route through
different stage topologies.

### Work unit

- live boundary-rooted subproblems

### Denominator

- the full seeded boundary mass for the run

### Exact coverage

- a boundary contributes exact coverage only when its entire descendant search
  has finished

### Partial coverage

- every timeout-capable XY attempt, regardless of which stage path triggered
  it, MUST contribute its partial credit to the same boundary-mass ledger
- this requirement applies equally to staged paths such as `SolveZ`, combined
  paths such as `SolveWZ`, and any future bundled solver path

### Quality

- `Hybrid` unless both base weights and timeout credits become direct
  search-mass fractions

If boundary weights are uniform rather than true subtree mass, the adapter
MUST describe that as an approximation.

## 7.3 `--wz=sync`

### Work unit

- projected fraction of the sync walker's search tree

### Denominator

- the whole sync-run search space

### Coverage

- the universal snapshot MAY publish a projected covered fraction derived from
  the walker's own estimator
- this fraction MUST be clearly labeled `Projected`
- the published projected fraction MUST still satisfy the universal monotonicity
  rule for `covered_mass`; if the underlying estimator can move backward as more
  samples arrive, the published value MUST clamp to the monotone envelope rather
  than decreasing

### Authoritative telemetry

- mode-specific sync telemetry remains authoritative for analysis of sync runs

The universal snapshot for sync exists for dashboard continuity, not to replace
the walker's direct diagnostics.

## 8. Search-space trimming

Any optimization that truly removes admissible search states MUST improve TTC
through at least one of these channels:

1. smaller denominator
2. larger covered fraction at fixed elapsed time
3. larger coverage rate

Examples:

- pruning before seeding reduces denominator mass
- stronger propagation may increase timeout coverage credit
- walker pruning may increase projected coverage growth

If a real pruning change improves neither denominator nor covered fraction nor
rate, the implementation SHOULD be treated as suspect.

## 9. Conjecture-constrained runs

When any `--conj-*` flag removes search states, the run MUST be labeled as
conjecture-constrained unless completeness of the restricted space is justified
independently.

Required reporting labels:

- `TTC (unconstrained baseline)`
- `TTC (conjecture-constrained)`

The implementation MUST NOT present constrained and unconstrained TTC values as
directly comparable without that qualifier.

These qualifiers are output-label requirements for user-facing reports and logs;
they are not additional fields on `ProgressSnapshot`.

If a conjecture changes the actual problem being searched, the denominator for
that run is the constrained search space for that run. Consumers comparing to
baseline MUST do so with the qualifier, not by pretending the spaces are
identical.

## 10. Required tests and checks

The implementation MUST include tests or assertions covering:

1. disjoint exact fractions sum to `1.0`
2. covered mass never exceeds `1.0`
3. covered mass is monotone
4. TTC is `None` when rate is zero
5. split/resume paths do not double-count credited mass
6. logically-equivalent timeout paths contribute partial credit uniformly
7. mode quality labels match the actual estimator semantics

## 11. Interpretation rule

When evaluating an optimization, TTC deltas MUST be decomposed into:

1. denominator change
2. covered-mass change
3. coverage-rate change

This is the required interpretation rule for performance analysis. Raw solves
per second or node throughput alone are not sufficient.
