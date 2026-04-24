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

## Canonical metric set (keep this narrow)

To avoid metric sprawl, treat these as the **only primary metrics** for
optimization decisions:

1. **TTC (parallel)**
   - Main success metric (`Time to cover` in pipeline modes,
     `TTC_parallel`/direct parallel TTC in sync).
2. **Effective coverage progress**
   - `effective / total_mass` as reported in progress lines.
3. **Timeout coverage quality**
   - XY timeout rate + average timeout coverage credit (so TTC deltas are
     not confused with changed timeout behavior).
4. **Conjecture activity counters (only when enabled)**
   - Currently just `--conj-zw-bound rejects`.

Everything else (per-stage solve counts, propagator-family splits,
per-level tables) is **diagnostic-only** and should be consulted only
when one of the four primary metrics moves unexpectedly.

## Path-by-path implementation

All modes publish through the same `SearchMassModel` interface
(`src/search_framework/mass.rs`) and the same `MassSnapshot::ttc`
algebra. The numerator in every case is the sum of two fractions:

- `covered_exact` — fraction of the search space provably ruled out
  (SAT/UNSAT returned within the conflict budget).
- `covered_partial` — fractional credit from interrupted sub-cubes
  (XY timeouts where the SAT solver pruned part of the cube before
  the conflict limit fired).

`ProgressSnapshot.covered_mass = covered_exact + covered_partial`,
clamped to `total_mass = 1.0`.

## 1) `--wz=cross`

### Work unit
- Tuple shells (one `SumTuple` = one logical "work slot"). Each
  tuple fans out to all `Z × W` pairs in its shell.

### Denominator
- `total_mass = 1.0` (the whole search space).

### Numerator
- `covered_exact = tuples_done / tuples_total` — updated at the
  bottom of the tuple loop in `CrossEnumerateStage::handle`
  (`src/search_framework/mode_adapters/cross.rs`). `covered_partial`
  is not tracked in cross today (every XY attempt runs to SAT/
  UNSAT under a fixed conflict budget; timeouts fall through to
  the next pair rather than feed back as credit).

### Quality
- `Hybrid`: the tuple count is direct, but equating tuples with
  a uniform-weight fraction of the XY search space is a
  projection — tuple shells have different `(Z, W)` pair counts
  and XY-candidate depths. A per-tuple weight estimate is a
  follow-up.

## 2) `--wz=apart` and `--wz=together`

Both route through `MddStagesAdapter` (five stage handlers around
the MDD pipeline helpers: `process_boundary`, `process_solve_w`,
`process_solve_wz`, `process_solve_z`).

### Work unit
- Live MDD ZW boundary paths: one `BoundaryWork` per path, seeded
  upfront by `enumerate_live_boundaries` (or a single path via
  `mdd_navigate_to_outfix` when `--outfix` pins the boundary).

### Denominator
- `total_mass = 1.0`; each boundary represents `1 / N` of the
  search space where `N = seed_boundaries.len()`.

### Numerator
- `covered_exact = completed_boundaries / N`. A boundary is
  "complete" when every one of its descendants (SolveW → SolveZ
  → inline XY) has returned. Tracked by `BoundaryProgress` in
  `src/search_framework/mode_adapters/mdd_stages.rs` — a per-
  boundary pending-count map: decrement per completed handler
  call, increment per emitted child, and tick `completed` when
  the count hits zero. Additive over disjoint boundaries
  (unit test: `disjoint_fractions_sum_to_one` in
  `src/search_framework/mass.rs`).
- `covered_partial = Σ xy_cover_micro / (N × 1_000_000)`.
  `SolveZStage::handle` snapshots the global
  `flow_xy_timeout_cov_micro` counter before and after calling
  `process_solve_z`; the delta is per-call XY-timeout credit
  for this boundary. `BoundaryProgress::add_partial_cov_micro`
  sums it; `partial_fraction` divides by `N × 1_000_000` so a
  single fully-credited timeout is worth `1 / N` — the same
  unit as a fully-completed boundary. `apply_delta` clamps the
  sum so `covered_exact + covered_partial ≤ 1`.

### Quality
- `Hybrid`. The `covered_exact` stream is a real additive-over-
  disjoint boundary fraction (Direct-quality on its own), but
  `covered_partial` blends a branching-factor-style shortfall
  estimate onto the tail — so the published `covered_mass` is
  not strictly a count of what's been ruled out.

## 3) `--wz=sync`

Sync mode wraps the walker (`sync_walker::search_sync`) as a
single `SyncWalkStage` and surfaces the walker's own projected
TTC through the universal snapshot.

### Work unit
- Walker nodes visited.

### Denominator
- `total_mass = 1.0`.

### Numerator
- `covered_exact = 0.0` (the walker runs inside a single handler
  call and doesn't emit per-node stage transitions).
- `covered_partial = elapsed / TTC_parallel` (the fraction of
  projected wall-clock actually spent). Written to
  `SyncConfig::projected_fraction_ppm` from a monitor thread in
  `search_sync_parallel` every 250ms (mid-run) and once more
  from the walker's final aggregation. Read by
  `SyncWalkMassModel::covered_mass` / `covered_partial_mass`
  via the engine's per-tick poll. At n ≈ the walker's own
  Block-2/Block-3 telemetry is still the authoritative direct
  estimate; the universal fraction exists for dashboard
  continuity.

### Quality
- `Projected`. The fraction is a branching-factor extrapolation,
  not a count of provably-ruled-out nodes. Consumers should
  pair it with the walker's own per-level telemetry blocks
  documented below.

### Walker telemetry (authoritative per-mode)
The walker prints two TTC-style estimates after a run:

#### A) Projected TTC (`project_ttc`)
- Uses per-level effective branching factors:
  `b_eff(L) = children_by_level[L] / nodes_by_level[L]`.
- Projects full tree size from the product of branching factors.
- Converts to TTC by dividing projected nodes by observed node rate.

#### B) Direct TTC from coverage product
- Computes per-level coverage `cov(L) = processed_children / children`.
- Root coverage = `Π_L cov(L)`.
- TTC estimate: `elapsed / root_coverage`.

Both live in `project_ttc(...)` / `format_per_level_telemetry_with_ttc(...)` in `src/sync_walker.rs`.

## How search-space trimming affects TTC

Under the fraction-based contract, **any mechanism that removes
admissible search states should reduce the residual or increase
covered fraction**:

- MDD/static pruning reduces the live boundary set before it's
  seeded → each completed boundary is worth a larger fraction.
- Cross tuple/pair pruning shortens `tuples` → denominator shrinks.
- SAT root propagation and forced vars reduce `free_vars`, which
  raises `xy_cover_micro` per timeout → `covered_partial` grows
  faster.
- Sync-level forcing/pruning lowers effective branching or
  increases level coverage → projected fraction grows faster.

In short: if a change really trims search mass, TTC should improve
even when wall-clock throughput is unchanged.

## Contract gaps (what is still missing / non-uniform)

1. **`--wz=cross` weights tuples uniformly.** Each tuple shell is
   treated as `1 / tuples_total` of the search space, but tuple
   shells have different `(Z, W)` pair counts. Mass model is
   therefore `Hybrid`, not `Direct`. A per-tuple weight estimate
   (e.g. the cumulative XY attempts seen per tuple) is a follow-
   up.

2. **`--wz=apart|together` weights boundaries uniformly.** Same
   story: each boundary is worth `1 / N` regardless of how large
   its XY subtree is. An optimization that forces many XY vars
   early (shrinking the subtree without changing the boundary
   count) isn't reflected in the fraction. The `covered_partial`
   timeout credit does vary per boundary, which partially
   compensates, but the base weight is still uniform.

3. **`--wz=sync` publishes only the `projected_fraction` estimator
   through the universal snapshot.** The walker's per-level
   `project_ttc` and direct `elapsed / Πcov` blocks are still
   only emitted to stderr after the run; the universal
   `covered_mass` is driven by the branching-factor projection
   alone (quality = `Projected`). Sync mid-run `covered_mass`
   can lag the direct estimator because workers aggregate stats
   into the shared accumulator only at the end of their
   sub-walks.

## What currently *does* satisfy the contract

- All modes expose the same `SearchMassModel` interface
  (`total_mass`, `covered_mass`, `covered_partial_mass`,
  `quality`) and flow through `MassSnapshot::ttc`.
- Partial work from XY timeouts is credited via
  `covered_partial` in apart/together.
- MDD pruning reduces the seeded boundary count, which reduces
  the denominator directly.
- Sync pruning/forcing affects the walker's own branching
  factors, which feeds back into `projected_fraction` and
  therefore the universal `covered_mass`.

## Practical notes on comparability

All modes use the same fraction unit (`total_mass = 1.0`) and the
same `MassSnapshot::ttc` algebra, so numbers are structurally
comparable. But the semantic meaning of a "unit of covered mass"
differs per mode (a completed tuple shell, a completed boundary,
or a projected fraction of walker nodes), so compare TTC **within
a mode** at fixed `n` and comparable limits for the most useful
signal.

## Recommended interpretation rule

When evaluating an optimization, always decompose the TTC delta into:

1. denominator change (total search mass),
2. covered-mass change (credit model, especially timeout coverage),
3. rate change (covered mass per second).

This ensures "forced-variable" or pruning optimizations receive TTC
credit even when raw solves/sec is flat.


## Search-conjecture options and TTC impact

### Implementation status (April 20, 2026)

The conjectural search flags are now implemented and wired through the
CLI/parser:

- `--conj-xy-product` / `--no-conj-xy-product`
- `--conj-zw-bound` / `--no-conj-zw-bound`
- `--conj-tuple` / `--no-conj-tuple`

Current behavior by mode:

- `--conj-xy-product`: applied where an XY SAT template is built
  (`cross`, `apart`, `together`).
- `--conj-zw-bound`: applied as an XY-stage prefilter on candidate
  `(Z, W)` extensions (`cross`, `apart`, `together`), with explicit
  reject counts in pipeline summary.
- `--conj-tuple`: auto-picks one tuple (if `--test-tuple` is absent)
  and restricts tuple enumeration to that single shell.
- `--wz=sync`: currently ignores these conjecture toggles; sync TTC
  remains governed by walker telemetry (`project_ttc` and direct
  coverage-product TTC).

### Quick TTC sanity check (`n=18`, `--wz=apart`, `--mdd-k=7`, `--sat-secs=8`)

Single-sample runs (2 threads) showed:

- baseline: `Time to cover ≈ 1.3m`
- `--conj-xy-product`: `≈ 1.3m`
- `--conj-zw-bound`: `≈ 1.4m` (`--conj-zw-bound rejects: 0` in sample)
- `--conj-tuple`: `≈ 1.2m` with much larger reported progress
  (`~10%` vs `<1%` baseline)
- all three flags: `≈ 1.2m`

Interpretation: in `apart/together`, TTC denominator is still
`live_zw_paths`, so XY-only pruning mainly changes the rate term. Tuple
restriction can make progress look much faster while denominator still
references the unconstrained MDD boundary mass.

### Flag-by-flag TTC expectations

#### `--conj-tuple`

Expected effect:
- Strong cut in tuple-space work by restricting to one shell.
- In current TTC instrumentation this can inflate apparent progress if
  denominator is interpreted as unconstrained boundary mass.

Contract note:
- Treat this as **problem-restriction mode** unless you separately
  account for symmetry/completeness recovery over omitted tuples.

#### `--conj-xy-product`

Expected effect:
- Trims XY subspace via mirror-product equalities (`U_i = -U_{n+1-i}`),
  typically reducing candidate solves and/or SAT work per boundary.

Contract risk:
- If conjecture fails on valid instances, TTC may improve by excluding
  real solutions.

#### `--conj-zw-bound`

Expected effect:
- Adds high-lag equality checks tied to `U`, pruning `(Z,W)` candidates
  before expensive XY solve attempts.
- Telemetry includes `--conj-zw-bound rejects` to expose whether the
  rule is active at the sampled `n`/`k`.

Contract risk:
- Same as above: if incorrect, TTC becomes optimistic through invalid
  pruning.

### Reporting rule for conjecture runs

When any `--conj-*` option is enabled, report TTC with a qualifier:

- `TTC (conjecture-constrained)`
- `TTC (unconstrained baseline)`

Do not compare these as apples-to-apples unless completeness of the
constrained run is justified (proof, or independent reconstruction of
omitted search mass).
