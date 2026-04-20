# TTC (Time to Cover): implementation by solve path

This note is the canonical map of how every active search path computes
**TTC** today, and how to interpret it as one uniform metric.

## Uniform TTC contract

Across all modes, the intended metric is:

- `TTC = (total_search_mass - covered_search_mass) / coverage_rate`
- `coverage_rate = covered_search_mass / elapsed`

So equivalently:

- `TTC = elapsed * (total_search_mass - covered_search_mass) / covered_search_mass`

A mode is TTC-consistent if it defines:

1. a denominator (`total_search_mass`) representing the full search space
   that mode is responsible for,
2. a numerator (`covered_search_mass`) that gives full credit to solved
   subproblems and fractional credit to partially explored ones,
3. a rate derived from that same numerator.

## Path-by-path implementation

## 1) `--wz=cross`

### Work unit
- XY candidate SAT solves.

### Denominator (`total_search_mass`)
- `cross_estimated_total_xy(...)` in `xy_sat.rs`:
  - while tuple generation is still running: extrapolated total
    `xy_pushed * tuples_total / tuples_done`
  - once done: exact `xy_pushed`.

### Covered mass (`covered_search_mass`)
- `effective_xy_done(...)` in `xy_sat.rs`:
  - SAT + UNSAT each count as `1.0`
  - timeout counts as `xy_cover_micro / 1_000_000`.

### Timeout fractional coverage
- `xy_cover_micro(...)` in `xy_sat.rs`:
  - SAT/UNSAT => `1_000_000`
  - timeout => `log2(decisions + 1) / free_vars`, clamped `[0,1]`.

### TTC report site
- Progress snapshots and final summary in `mdd_pipeline.rs` (cross branch).

## 2) `--wz=apart` and `--wz=together`

These share the same TTC machinery in the MDD pipeline.

### Work unit
- MDD live ZW boundary paths ("walked boundaries"), with timeout
  shortfall correction from downstream XY solves.

### Denominator (`total_search_mass`)
- `live_zw_paths = mdd.count_live_paths()` in `mdd_pipeline.rs`.
- This is the MDD-pruned boundary space; if MDD construction or
  constraints remove boundaries, denominator shrinks accordingly.

### Covered mass (`covered_search_mass`)
- `effective_coverage_metric(...)` in `xy_sat.rs`:
  - start from completed boundaries (`stage_exit[0]`)
  - apply shortfall factor from XY timeout partial coverage.

### Timeout fractional coverage
- Same `xy_cover_micro(...)` logic as cross mode.

### TTC report site
- Progress snapshots and final summary in `mdd_pipeline.rs`
  (non-cross branch).

## 3) `--wz=sync`

Sync mode currently prints two TTC-style estimates from walker telemetry.

### A) Projected TTC (`project_ttc`)
- Uses per-level effective branching factors:
  `b_eff(L) = children_by_level[L] / nodes_by_level[L]`.
- Projects full tree size from the product of branching factors.
- Converts to TTC by dividing projected nodes by observed node rate.

### B) Direct TTC from coverage product
- Computes per-level coverage `cov(L) = processed_children / children`.
- Root coverage = `Π_L cov(L)`.
- TTC estimate: `elapsed / root_coverage`.

### TTC report sites
- `project_ttc(...)` and per-level telemetry formatting in
  `sync_walker.rs`.

## How search-space trimming affects TTC

Under the uniform contract, **any mechanism that removes admissible
search states should reduce denominator and/or increase covered fraction**:

- MDD/static pruning reduces `live_zw_paths` (apart/together denominator).
- Cross tuple/pair pruning reduces total XY candidates (cross denominator).
- SAT root propagation and forced vars reduce `free_vars`, which raises
  timeout coverage credit for a fixed decision budget.
- Sync-level forcing/pruning lowers effective branching or increases level
  coverage, reducing projected/direct TTC.

In short: if a change really trims search mass, TTC should improve even
when wall-clock throughput is unchanged.

## Contract gaps (what is still missing / non-uniform)

If we enforce the strict contract "TTC measures time to cover the full
remaining search space for this problem instance", these are the current
gaps:

1. **`--wz=cross` uses an extrapolated denominator before producer done.**
   - `cross_estimated_total_xy(...)` is a projection while tuples are still
     being enumerated, so `total_search_mass` is not exact until
     `cross_done=true`.
   - This is useful online telemetry, but strictly it is an estimate of TTC,
     not exact TTC.

2. **`--wz=apart|together` denominator is boundary-count only.**
   - `live_zw_paths` counts surviving ZW boundaries, but does not weight each
     boundary by the actual remaining XY subtree mass.
   - If one optimization forces many XY vars early (shrinking subtree mass)
     without changing boundary count, denominator does not drop accordingly.

3. **`effective_coverage_metric(...)` applies timeout shortfall globally.**
   - It uses an aggregate timeout shortfall factor over all XY solves.
   - That means coverage credit is approximate when timeout difficulty is
     highly non-uniform across boundaries.

4. **`--wz=sync` has two TTC estimators, not one canonical TTC.**
   - `project_ttc` (branching projection) and direct `elapsed / Πcov` are
     both estimates from partial traversal telemetry.
   - Neither is currently wired into the same denominator/numerator interface
     used by cross/apart/together final `Time to cover:` reporting.

5. **No common cross-mode mass unit yet.**
   - Cross uses "effective XY solves", apart/together use "effective
     boundaries", sync uses projected/covered nodes.
   - Algebra is shared, but unit definitions differ, so TTC is most reliable
     for within-mode comparisons.

## What currently *does* satisfy the contract

- Partial work from timeouts is credited (via `xy_cover_micro`) in cross and
  MDD modes, so covered mass is not binary SAT/UNSAT only.
- MDD/static pruning that removes full boundaries reduces denominator in
  apart/together.
- Sync pruning/forcing affects measured branching/coverage and therefore both
  sync TTC estimators.

## Tightening plan (to make TTC truly uniform)

1. Promote one explicit `SearchMass` interface in code:
   - `total_mass(problem, mode)`
   - `covered_mass(progress)`
   - `ttc = (total - covered) / (covered / elapsed)`
2. For apart/together, weight denominator by per-boundary XY mass estimate
   (or exact count where available), not just boundary cardinality.
3. For cross, label pre-`cross_done` output as `estimated TTC` explicitly,
   and switch to exact TTC when enumeration completes.
4. For sync, publish one canonical TTC field using the same interface
   (keep projection/direct as diagnostics).

## Practical notes on comparability

- Cross TTC units are XY-candidate solves.
- Apart/together TTC units are effective MDD boundaries.
- Sync TTC units are projected/covered walker nodes.

All three obey the same algebra (`remaining_mass / mass_rate`) but use
mode-specific mass definitions. For strict apples-to-apples comparison,
compare TTC **within a mode** at fixed `n` and comparable limits.

## Recommended interpretation rule

When evaluating an optimization, always decompose the TTC delta into:

1. denominator change (total search mass),
2. covered-mass change (credit model, especially timeout coverage),
3. rate change (covered mass per second).

This ensures "forced-variable" or pruning optimizations receive TTC
credit even when raw solves/sec is flat.


## Search-conjecture options and TTC impact

### Implementation status in this checkout

The current CLI/parser in this tree does **not** yet expose the
conjectural flags. Help + parser currently recognize the existing mode
and SAT tuning flags, and unknown flags error out.

So at this revision, `--tuple-mode`, `--xy-product-law`, and
`--zw-u-bound-tight` should be treated as **design-plan options**, not
runtime options.

### Planned conjecture knobs (from search-plan docs)

The conjecture-oriented plan files describe three optional search knobs:

- `--tuple-mode=signed|positive`
- `--xy-product-law`
- `--zw-u-bound-tight`

(See `best-search-plan.md` and the conjecture notes.)

### `--tuple-mode=positive`

Expected TTC effect:
- **Denominator drop** if positive tuples are treated as orbit
  representatives and the omitted signed tuples are provably redundant.
- If implemented as a pure "do less search" heuristic without a proof
  of full-orbit recovery, this changes the solved problem definition
  rather than just improving TTC.

Contract guidance:
- Only count as TTC improvement for the *same* problem when coverage of
  omitted signed shells is guaranteed by symmetry reconstruction.

### `--xy-product-law`

Expected TTC effect:
- Directly trims XY subspace by forcing mirror-product relations
  (`x_i y_i x_{n+1-i} y_{n+1-i} = -1` interior), so denominator should
  drop materially.
- In current instrumentation, this drop is only partially reflected:
  cross sees fewer candidates pushed; apart/together may not fully
  reflect per-boundary XY-mass reduction if boundary count is unchanged.

Contract risk:
- If conjectural law is false for some valid TT instances, TTC can look
  dramatically better while completeness is silently lost.

### `--zw-u-bound-tight`

Expected TTC effect:
- Adds high-lag ZW equality constraints derived from `U`, pruning ZW
  candidates earlier and increasing effective coverage rate.
- Should reduce denominator in modes where the pruned ZW boundaries are
  removed before XY solving.

Contract risk:
- As with `--xy-product-law`, this is conjectural. A wrong equality rule
  yields optimistic TTC by cutting away valid search mass.

### Recommendation for conjecture-mode TTC reporting

When any conjectural option is enabled, print TTC with an explicit mode
qualifier, e.g.:

- `TTC (conjecture-constrained)`
- `TTC (unconstrained baseline)`

and never compare those two as like-for-like unless a proof (or an
independent completeness argument) is provided.
