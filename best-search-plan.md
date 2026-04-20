# Best Search Plan

This document describes the search strategy that currently looks most promising given:

- the existing MDD / SAT / spectral pipeline
- the BDKR canonical rules already implemented
- the new empirical `X/Y` product-law work from [codex-math-notes.md](./codex-math-notes.md)
- the tuple-coverage results from [`tuple_coverage`](./src/bin/tuple_coverage.rs)

The goal is to give an implementation-ready plan for an agent.

## Executive Summary

The best current direction is:

1. search a single positive tuple representative
2. keep the outside-in bounce order
3. treat `X,Y` structurally and `Z,W` spectrally
4. reparameterize `X,Y` as `(X,U)` where `U_i = x_i y_i`
5. impose the hypothetical `U` law early at the boundary
6. optionally impose a high-lag `ZW` tightness rule derived from `U`
7. match `XY` and `ZW` branches by outer norm coefficients
8. leave SAT as a late completion tool, not the primary driver

Short version:

- use **structural pruning on `XY`**
- use **spectral/norm pruning on `ZW`**
- use an optional **high-lag `U`-derived tight bound on `ZW`**
- meet in the middle on the norm coefficients

## Why This Plan

### 1. Tuple layer is highly compressible

For `n >= 20`, the data says:

- canonical tuples alone do not cover the full signed shell
- canonical tuples plus their `T3` images do cover the full signed shell

So it is plausible that search only needs:

- one positive tuple representative per `T1/T3/T4`-style shell class

This does not remove many bits by itself, but it is a clean constant-factor improvement and simplifies the search.

### 2. `X,Y` are structurally special

The strongest new empirical law is:

- define `U_i := x_i y_i`
- in canonical reps, likely
  - `U_1 = U_n = +1`
  - `U_i = -U_{n+1-i}` for `2 <= i <= n-1`

Equivalent form:

- `x_i y_i x_{n+1-i} y_{n+1-i} = -1` for interior mirror pairs

Consequences:

- `X · Y = 2` in canonical form
- `|X · Y| = 2` orbit-invariant
- `XY` column-type counts are forced by `(n, σX, σY)`
- this cuts `XY` search by about `n/2 - 1` bits if the full law is enforced

This is boundary-native and non-spectral. It should be exploited in the combinatorial search, not deferred to SAT.

### 3. `Z,W` do not show an analogous law

The corpus does **not** show a comparable `ZW` inner-product or product-sequence law.

So:

- `XY` should be searched using structural rules
- `ZW` should continue to be searched using the existing norm/spectral machinery

That asymmetry is central.

## Core Search Strategy

## Step 1: Tuple choice

Search only one positive tuple representative:

- `σX >= 0`
- `σY >= 0`
- `σZ >= 0`
- `σW > 0`

Optionally also normalize by `X/Y` tuple swap:

- enforce `σX >= σY`

Rationale:

- empirical tuple coverage suggests that canonical reps plus `T3` cover the full shell from `n >= 20`
- positive tuples appear to suffice as shell representatives in that regime

Implementation note:

- this is a hypothesis-driven optimization
- keep it behind a flag initially
- fallback should preserve the current signed-tuple behavior

Suggested flag:

- `--tuple-mode=signed|positive`

## Step 2: Split the search into `XY` and `ZW`

Do **not** search all four sequences symmetrically.

Instead:

- `XY` branch:
  - structural / product-law / canonical search
- `ZW` branch:
  - current norm / spectral / MDD search

Then join by outer norm coefficients.

That is the most important architecture change.

## Step 3: Reparameterize `XY` as `(X,U)`

Define:

- `U_i := x_i y_i`

Then:

- `Y_i = X_i * U_i`

So searching `(X,Y)` can be replaced by searching:

- `X`
- `U`

This is beneficial because `U` appears much more structured than `Y`.

### Hypothetical `U` law

Assume, optionally:

- `U_1 = U_n = +1`
- `U_i = -U_{n+1-i}` for `2 <= i <= n-1`

Equivalent Boolean constraint if `true = +1`, `false = -1`:

- `X_i XOR Y_i XOR X_{n+1-i} XOR Y_{n+1-i} = 1`

Equivalent product form:

- `x_i y_i x_{n+1-i} y_{n+1-i} = -1`

Suggested flag:

- `--xy-product-law`

Even if full proof is not available yet, this is the right hypothetical feature to A/B.

## Step 3b: Add the `ZW` high-lag `U`-bound conjecture

This should be treated as a separate hypothetical rule from the full product law.

Let:

- `U_i := x_i y_i`
- `N_A(s)` be the aperiodic autocorrelation at lag `s`

Then the support-splitting argument gives the exact bound

- `|N_Z(s) + N_W(s)| <= ((n - s) + N_U(s)) / 2`

where `N_U(s) = sum_i U_i U_{i+s}`.

Empirical corpus result:

- for every known TT in the corpus, equality holds at
  - `s = n - 1`
  - `s = n - 2`
  - `s = n - 3`
- equality also holds about 60% of the time at
  - `s = n - 4`
  - `s = n - 5`

So the recommended hypothetical version is:

- if `--zw-u-bound-tight` is enabled, enforce
  - `|N_Z(s) + N_W(s)| = ((n - s) + N_U(s)) / 2`
  - for `s in {n - 1, n - 2, n - 3}`

This is attractive because:

- it acts on the `ZW` side rather than `XY`
- it is boundary-native and strongest exactly at the outer lags
- it composes naturally with either ordinary `XY` search or `(X,U)` search
- it does not require assuming the full interior product-skew law

Suggested flag:

- `--zw-u-bound-tight`

## Step 4: Keep the outside-in bounce order

The current bounce order is still the right one.

Why:

- BDKR least-index rules are boundary-oriented
- norm coefficients are determined from the outside inward
- the `U` law is also mirror-pair / boundary-oriented

So:

- do not replace the bounce order
- strengthen the state carried by the bounce

## Search State Design

The current state should be extended to carry enough information for:

- tuple sums remaining
- outer norm coefficients already determined
- least-index canonical rule progress
- partial `U` assignments
- product-law consistency
- `ZW` high-lag `U`-bound consistency when enabled

### `XY` state

At minimum, the `XY` search state should include:

- remaining `σX`
- remaining `σY`
- partial outer norm coefficients contributed by `X,Y`
- rule-state for BDKR (ii), (iii), (vi)
- assigned boundary bits of `X`
- assigned boundary bits of `U`

`Y` should be recovered lazily from `X * U`.

### `ZW` state

Keep the existing `ZW` machinery largely intact:

- remaining `σZ`
- remaining `σW`
- current spectral bound state
- current outer norm coefficients
- canonical rule-state for Z/W rules
- if `--zw-u-bound-tight` is enabled:
  - enough `U` boundary data to compute `N_U(s)` at already-closed outer lags
  - and a check that `|N_Z(s) + N_W(s)| = ((n - s) + N_U(s)) / 2` for `s in {n-1,n-2,n-3}` once those lags are determined

### Join key

The join between `XY` and `ZW` should be on:

- outer norm coefficient vector up to current depth

Equivalently:

- `C_X(s) + C_Y(s)` must match `-2(C_Z(s) + C_W(s))`

for all already-determined outer lags.

That lets the two searches proceed mostly independently until they must agree.

If `--zw-u-bound-tight` is enabled, the join can be strengthened:

- once `N_U(s)` is known at high outer lags, reject any `ZW` branch whose `|N_Z(s) + N_W(s)|` is not exactly the implied bound

## How To Build `XY` Using `(X,U)`

At each bounce step, assign:

- `x_L, x_R`
- `u_L, u_R`

and derive:

- `y_L = x_L * u_L`
- `y_R = x_R * u_R`

If the full product law is enabled, then for interior mirror pairs:

- `u_R = -u_L`

so only one of `u_L, u_R` is free once the pair is closed.

This halves the `XY` branching at each completed interior mirror pair.

### Per-step branching effect

Ignoring all other pruning:

- without the law, `XY` contributes `2^4 = 16` assignments per new left/right step
- with the product law, only `8` survive

So:

- one completed mirror pair removes `1` bit
- total full-law savings: `n/2 - 1` bits

For `n=56`, that is:

- `27` bits

## Norm handling

Do not delay norm logic to SAT.

Instead:

- as each outer pair is assigned, update the already-determined outer coefficients
- prune immediately if the partial `XY` or `ZW` coefficient vector is impossible to complete

This is already the right idea in the current MDD pipeline and should remain.

The architecture change is:

- now `XY` should contribute coefficients using `(X,U)` rather than raw `(X,Y)`

## SAT role

SAT should remain a late completion tool.

Do not move the new rules into SAT only.

Best use:

- after aggressive boundary pruning in `XY`
- after aggressive spectral/norm pruning in `ZW`
- SAT resolves the thin surviving middles

### SAT integration points

If `--xy-product-law` is enabled, SAT should also receive the corresponding clauses:

- for each interior mirror pair `i`
  - `x_i y_i x_{n+1-i} y_{n+1-i} = -1`

But the main value is earlier:

- in the boundary walker / DFS / MDD

`--zw-u-bound-tight` is different:

- it is primarily a boundary / MDD / DFS rule
- it should not be the first thing pushed into SAT
- the value is in early rejection of `ZW` branches once the top lags are determined

## Implementation Plan

## Phase 1: Instrumentation only

Before changing the search architecture, add measurement.

Needed metrics:

- per-depth branching before/after canonical rules
- per-depth branching before/after hypothetical product-law filtering
- per-depth branching before/after `--zw-u-bound-tight`
- per-depth outer-coefficient survival
- number of states grouped by join key

This tells us whether the reparameterization is actually worth the code complexity.

## Phase 2: Hypothetical SAT + boundary filter

Minimal first implementation:

- keep the current `XY` representation
- add the hypothetical product-law as an optional filter in:
  - boundary walker
  - SAT encoding
- add `--zw-u-bound-tight` as an optional `ZW` high-lag boundary filter

This is easy to A/B.

Suggested goal:

- validate the predicted `2^(n/2-1)` combinatorial reduction at the `XY` boundary level

## Phase 3: True `(X,U)` search

After the filter version is working:

- refactor `XY` search state to use `(X,U)`
- derive `Y` on the fly

This is the real architectural change.

Expected gains:

- smaller branching factor
- cleaner rule propagation
- easier expression of the conjectured law

## Phase 4: Separate `XY` and `ZW` builders

Once `(X,U)` is in place:

- run `XY` and `ZW` boundary searches as distinct engines
- join by outer norm coefficient vectors

This is likely the best long-term architecture.

## Suggested code-level milestones

1. Add `--xy-product-law` as a hypothesis flag.
2. Add `--zw-u-bound-tight` as a separate hypothesis flag.
3. Enforce `--xy-product-law` in SAT and the existing boundary walker.
4. Enforce `--zw-u-bound-tight` in the existing `ZW` boundary logic.
5. Add instrumentation for per-depth survival.
6. Introduce a lightweight `U` helper representation.
7. Replace raw `XY` branching with `(X,U)` branching.
8. Split `XY` and `ZW` search frontiers and join on coefficient keys.
9. Benchmark against current `apart/together/sync` modes.

## Validation

Every step should preserve a fallback mode.

Required A/B checks:

- correctness:
  - known solutions still found when the flag is off
  - if the flag is on, the current known solutions satisfy it
- search reduction:
  - per-depth branching reduction matches expectation
- end-to-end:
  - time-to-first-solution
  - fixed-budget coverage

Suggested benchmark matrix:

- `n = 20, 22, 24, 26, 28, 32`
- compare:
  - current search
  - current + product-law filter
  - current + `--zw-u-bound-tight`
  - current + both hypothetical filters
  - `(X,U)` search if implemented

## Risk Notes

### 1. The product law is still hypothetical

It is strongly supported by data and partially proved, but not fully proved yet.

Therefore:

- keep it optional
- do not make it the only path until enough evidence accumulates

### 1b. `--zw-u-bound-tight` is also hypothetical

The exact high-lag equality

- `|N_Z(s) + N_W(s)| = ((n - s) + N_U(s)) / 2`

is strongly supported at `s = n-1,n-2,n-3` on the known corpus, but it is not proved.

Therefore:

- keep it optional
- benchmark it separately from `--xy-product-law`
- treat it as a distinct conjectural filter

### 2. Positive-tuple-only is also still an empirical strategy

The tuple coverage data supports it from `n >= 20` in the current corpus, but it is not a theorem.

So:

- also keep this behind a flag initially

### 3. `ZW` may remain the harder side

There is no comparable `ZW` product law.

So do not expect symmetry between the two halves.

## Recommended Initial Build

If an agent is implementing only the first useful version, the best target is:

- keep the current solver architecture
- add `--xy-product-law`
- add `--zw-u-bound-tight`
- enforce the `XY` boundary rule directly in the current `XY` walker and SAT layer
- enforce the `ZW` high-lag rule directly in the current `ZW` boundary logic
- add per-depth instrumentation

That gives immediate experimental value with relatively low code risk.

The full `(X,U)` refactor should come only after that A/B result is in hand.
