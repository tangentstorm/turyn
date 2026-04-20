# Positive Tuple Hypothesis

This note records the current tuple-level search hypothesis:

- it may be sufficient to search only one positive tuple representative

for each Turyn sum-shell class, rather than all signed tuples.

This is a search hypothesis, not a theorem.

## Statement

For `TT(n)`, define the ordinary signed sum tuple:

- `(\sigma_X, \sigma_Y, \sigma_Z, \sigma_W)`

where:

- `\sigma_X = sum X`
- `\sigma_Y = sum Y`
- `\sigma_Z = sum Z`
- `\sigma_W = sum W`

and the tuple satisfies the standard shell equation:

- `\sigma_X^2 + \sigma_Y^2 + 2\sigma_Z^2 + 2\sigma_W^2 = 6n - 2`

The hypothesis used in the search plan is:

- restrict tuple search to one positive representative, for example
  - `\sigma_X >= 0`
  - `\sigma_Y >= 0`
  - `\sigma_Z >= 0`
  - `\sigma_W > 0`

and optionally also:

- `\sigma_X >= \sigma_Y`

to quotient by `X/Y` tuple swap.

## Motivation

There are two reasons to take this seriously as a search rule.

### 1. BDKR’s empirical shell-surjectivity observation

This idea is closely related to a remark from Đoković, Kotsireas, and
Reboul (BDKR). In their paper they write:

> “It is noteworthy that our computation shows that for all even n ≤ 32,
> any choice of four squares A(1)^2, B(1)^2, C(1)^2, D(1)^2 satisfying this
> equation can be realized by some TT(n).”

Interpreted in this project’s notation, that says:

- every algebraically admissible absolute-value tuple up to `n <= 32`
  appears in some actual Turyn orbit

This is not yet the same as the positive-tuple-only search rule, but it is strong evidence that the tuple shell is unusually well covered by actual solutions.

### 2. Canonical-plus-T3 coverage in the current corpus

The current tuple-coverage analysis in this repo shows:

- canonical tuples alone do not cover the full signed shell
- canonical tuples plus their `T3` images do cover the full signed shell for every even `n` from `20` through `32`

So empirically:

- once `T3` is taken into account, the signed shell appears to collapse to a much smaller representative set

This supports the practical search heuristic:

- search one positive tuple representative and rely on symmetry / alternation to cover the rest

## What Is Known Empirically Here

Using [src/bin/tuple_coverage.rs](../src/bin/tuple_coverage.rs) on the restored corpus:

- `n=20`: canonical plus `T3` covers `120 / 120`
- `n=22`: `168 / 168`
- `n=24`: `144 / 144`
- `n=26`: `192 / 192`
- `n=28`: `168 / 168`
- `n=30`: `180 / 180`
- `n=32`: `240 / 240`

Also:

- no all-positive stragglers appeared among the tuples missed by canonical form alone
- for `n >= 22`, every canonical-only straggler had `\sigma_X < 0`

So the positive side of the shell appears to be the right side to keep.

## What This Would Buy

The gain is only at the tuple layer, not the raw bit layer.

For example, at `n = 56`:

- full signed tuple space has `336` elements
- all-positive tuple space has `24`
- all-positive tuples modulo `X/Y` swap has `12`

So the reduction is:

- factor `14` for positive-only
- factor `28` for positive-only plus `X/Y`-swap normalization

This is useful, but much smaller than the projected gain from the `XY` product law.

## Why This Is Still Only A Hypothesis

The BDKR observation is about:

- absolute-value tuple coverage up to `n <= 32`

The repo observation is about:

- canonical-plus-`T3` signed tuple coverage up to `n <= 32`

Neither one proves:

- positive tuples suffice for all even `n`

So the correct status is:

- strong empirical support
- good search heuristic
- not a theorem

## Search Flag

This is the tuple-layer hypothesis used in the search plan:

- `--tuple-mode=positive`

with fallback:

- `--tuple-mode=signed`

until more evidence is available.
