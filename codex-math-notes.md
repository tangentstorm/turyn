# Codex Math Notes

## Scope

These notes summarize the mathematical lines explored so far for Turyn-type sequences, with an emphasis on what appears to generalize beyond the `n = 18` case study.

## Core Identities

For `TT(n)` with sequences `X, Y, Z` of length `n` and `W` of length `n-1`:

- Aperiodic correlation identity:
  - `C_X(s) + C_Y(s) + 2 C_Z(s) + 2 C_W(s) = 0` for `1 <= s <= n-1`
- Sum shell:
  - `s_X^2 + s_Y^2 + 2 s_Z^2 + 2 s_W^2 = 6n - 2`
- Alternating-sum shell:
  - `a_X^2 + a_Y^2 + 2 a_Z^2 + 2 a_W^2 = 6n - 2`
- Lag-1 run identity:
  - if `r_S` is the number of sign changes in `S`, then
  - `r_X + r_Y + 2 r_Z + 2 r_W = 3n - 4`

These are general and hold for all `n`.

## What Did Not Look Strong Enough

The following ideas produced real constraints, but did not look decisive even for `n = 18`:

- Outer-lag recursion alone
- Root-of-unity norm constraints at `t = -1`
- `t = i`
- `t = ω` (primitive cube root)
- direct `t = ζ_12`
- run-count feasibility by itself

For `n = 18`, these constraints organized the search but did not come close to forcing a unique object.

## The Most Promising General Line: `P = X + Y`, `Q = X - Y`

Define:

- `P = X + Y`
- `Q = X - Y`

Then `P, Q` are ternary-valued sequences in `{ -2, 0, 2 }`, with complementary support at each coordinate:

- if `P_i != 0`, then `Q_i = 0`
- if `Q_i != 0`, then `P_i = 0`

Also:

- `N_P + N_Q + 4 N_Z + 4 N_W = 0` at nonzero lags

This reformulation seems to carry more structure than the raw `X, Y` view.

### Important Structural Identity

For every lag pair `(i, j)`:

- `x_i x_j + y_i y_j = (P_i P_j + Q_i Q_j) / 2`

Since at each coordinate exactly one of `P_i, Q_i` is nonzero, this has a strong consequence:

- if position `i` is an `agree` site (`x_i = y_i`, so `P_i != 0, Q_i = 0`)
- and position `j` is a `disagree` site (`x_j = -y_j`, so `P_j = 0, Q_j != 0`)
- then
  - `x_i x_j + y_i y_j = 0`

So the `X/Y` contribution to each lag comes only from same-support pairs:

- agree-agree pairs contribute through `P`
- disagree-disagree pairs contribute through `Q`
- agree-disagree cross-pairs contribute exactly `0`

This is a genuinely structural fact, not just a norm bound, and it looks like the best candidate so far for a theorem-sized reduction.

## XY Column-Type Model

At each coordinate, the pair `(x_i, y_i)` is one of four types:

- `a = (+,+)`
- `b = (-,-)`
- `c = (+,-)`
- `d = (-,+)`

Global counts satisfy:

- `a + b + c + d = n`
- `a - b + c - d = s_X`
- `a - b - c + d = s_Y`

So the `XY` type counts are always a one-parameter family:

- `a = n/2 + s_Y/2 - d`
- `b = n/2 - s_X/2 - d`
- `c = d + s_X/2 - s_Y/2`

This is general and seems worth promoting to a primary search coordinate system.

## General Empirical Observation

The parity / residue-class structure of `XY` types stays surprisingly small across the known corpus.

### Parity-Split Count

Number of feasible parity splits of the four `XY` types, using only shell data:

- `n=4: 1`
- `6: 2`
- `8: 1`
- `10: 1`
- `12: 2`
- `14: 3`
- `16: 3`
- `18: 2`
- `20: 4`
- `22: 5`
- `24: 3`
- `26: 4`
- `34: 7`
- `40: 8`
- `42: 6`
- `44: 9`

This grows with `n`, but very slowly.

### Exact mod-4 XY-Type Pattern Count

Using shell data plus the exact `|P(i)|^2, |Q(i)|^2` from known solutions:

- `n=4: 2`
- `6: 4`
- `8: 4`
- `10: 1`
- `12: 4`
- `14: 8`
- `16: 8`
- `18: 7`
- `20: 8`
- `22: 16`
- `24: 8`
- `26: 8`
- `34: 8`
- `40: 4`
- `42: 16`
- `44: 2`

### Exact mod-3 XY-Type Pattern Count

Using shell data plus the exact `|P(ω)|^2, |Q(ω)|^2`:

- `n=4: 2`
- `6: 12`
- `8: 3`
- `10: 4`
- `12: 6`
- `14: 6`
- `16: 8`
- `18: 12`
- `20: 6`
- `22: 4`
- `24: 6`
- `26: 6`
- `34: 16`
- `40: 8`
- `42: 12`
- `44: 6`

Again, these counts stay in a very small range.

## `n = 18` Case Study

For the known `TT(18)` in `known_solutions.txt`:

- signed sums:
  - `(s_X, s_Y, s_Z, s_W) = (10, -2, 0, -1)`
- alternating sums:
  - `(a_X, a_Y, a_Z, a_W) = (-4, -8, 2, 3)`
- `XY` type counts:
  - `(a, b, c, d) = (7, 3, 7, 1)`

In that case:

- feasible `XY` parity splits: `2`
- feasible exact mod-4 `XY` type distributions: `16`
- feasible exact mod-4 `P/Q` sum patterns after `|P(i)|^2, |Q(i)|^2`: `7`
- feasible exact mod-3 `P/Q` sum patterns after `|P(ω)|^2, |Q(ω)|^2`: `12`

### Outer-Shell Filtering for `n = 18`

Using the signed shell, alternating shell, and lag equations through shift `14`:

- base outer-shell survivors: `16280`

Additional arithmetic filters reduced that as follows:

- exact run-count feasibility: `16059`
- `P/Q` mod-4 sum-pattern filter: `15300`
- `P/Q` mod-3 sum-pattern filter: `13130`
- `XY` type parity filter: `13088`
- combined arithmetic filters (`XY` parity + `P/Q` mod-3 + `P/Q` mod-4): `10316`
- exact mod-4 `XY` type distribution filter alone: `12648`

Conclusion:

- these are cumulative and real
- but not remotely strong enough yet to force `TT(18)`

## Current Conclusion

The strongest mathematical direction found so far is:

1. work with `XY` column types
2. refine them by parity / residue classes
3. connect them to `P = X + Y`, `Q = X - Y`
4. combine those with outer-lag recursion

More specifically, the most promising next theorem is probably about the support sets:

- `A = { i : x_i = y_i }`
- `D = { i : x_i = -y_i }`

because the identity above shows that the `X/Y` lag contribution splits cleanly over `A` and `D`, with no cross-interaction.

The root-of-unity norms by themselves do not seem strong enough. Their best use is as residue-class constraints layered onto the `XY/PQ` representation.

## Full-Corpus Upgrade From The Kharaghani Data

After restoring `data/` and decoding the full Kharaghani catalogue up to `n = 32`, one empirical fact became much stronger:

- every listed solution satisfies `X · Y = 2` in the catalogue's sign convention

Since negating one of `X` or `Y` preserves the TT equations and flips the sign of the inner product, the natural theorem-sized conjecture is:

- for every Turyn-type quadruple, `|X · Y| = 2`

This is much stronger than the earlier "small support pattern" observations, because it holds across the full classified corpus, not just the short `known_solutions.txt` list.

### Stronger Product-Sequence Conjecture

The corpus suggests an even stronger law in the Kharaghani orientation.

If

- `U_i = x_i y_i`

then every decoded solution up to `n = 32` satisfies:

- `U_1 = U_n = +1`
- `U_i = -U_{n+1-i}` for every interior index `2 <= i <= n-1`

So the product sequence has `+` endpoints and is skew under reversal on the interior.

This immediately implies `sum U_i = 2`, hence `X · Y = 2`.

Equivalently:

- for every interior position `i`, exactly one of the mirrored pair `i, n+1-i` is an agree site and the other is a disagree site

or in support-set language:

- interior reversal swaps `A` and `D`

An equivalent pointwise form is:

- `x_i x_{n+1-i} = - y_i y_{n+1-i}` for every interior `2 <= i <= n-1`

or equivalently

- `x_i y_{n+1-i} = - x_{n+1-i} y_i`

So mirrored interior pairs cancel in the reversed mixed inner product. That explains the additional corpus observation that the Kharaghani representatives also satisfy a fixed value of `X · reverse(Y)`:

- the interior terms cancel in mirrored pairs
- only the endpoint pair survives

This is the strongest exact-looking structural law seen so far in the corpus. It deserves to be treated as a serious conjecture for canonical representatives.

### Consequences Of `X · Y = 2`

Let

- `a = #(+,+)`
- `b = #(-,-)`
- `c = #(+, -)`
- `d = #(-, +)`

Then

- `a + b + c + d = n`
- `a - b + c - d = s_X`
- `a - b - c + d = s_Y`
- `a + b - c - d = X · Y = 2`

So the four `XY` column-type counts are no longer a one-parameter family. They are forced:

- `a = (n + s_X + s_Y + 2) / 4`
- `b = (n - s_X - s_Y + 2) / 4`
- `c = (n + s_X - s_Y - 2) / 4`
- `d = (n - s_X + s_Y - 2) / 4`

Equivalently, if

- `A = { i : x_i = y_i }`
- `D = { i : x_i = -y_i }`

then

- `|A| = a + b = n/2 + 1`
- `|D| = c + d = n/2 - 1`

So in the Kharaghani orientation the `P = X + Y` support has size `n/2 + 1` and the `Q = X - Y` support has size `n/2 - 1`.

This is the cleanest exact structural law found so far.

### Product-Sequence View

Define the binary product sequence

- `U_i = x_i y_i`

Then

- `U_i = +1` on `A`
- `U_i = -1` on `D`
- `sum U_i = X · Y = 2`

So the support split is encoded by a single binary sequence with fixed sum `2`.

Its autocorrelation controls the support geometry exactly. If

- `C_U(s) = sum_{i=1}^{n-s} U_i U_{i+s}`

then

- `same_support(s) = #{ i : U_i = U_{i+s} } = ((n - s) + C_U(s)) / 2`
- `cross_support(s) = #{ i : U_i != U_{i+s} } = ((n - s) - C_U(s)) / 2`

This rewrites the `A/D` support statistics in a very compact way.

### XY Contribution Bound From `U`

Using

- `x_i x_j + y_i y_j = x_i x_j (1 + U_i U_j)`

or equivalently

- `x_i x_j + y_i y_j = (P_i P_j + Q_i Q_j) / 2`

the `X/Y` lag contribution uses only same-support pairs. Therefore

- `|C_X(s) + C_Y(s)| <= 2 * same_support(s) = (n - s) + C_U(s)`

and since TT gives

- `C_X(s) + C_Y(s) = -2 (C_Z(s) + C_W(s))`

we get the exact necessary bound

- `|C_Z(s) + C_W(s)| <= same_support(s) = ((n - s) + C_U(s)) / 2`

So any candidate `U` imposes a hard lag-by-lag cap on the admissible `Z/W` correlation.

## What The Full Corpus Says About The Remaining Freedom

The exact global `XY` structure is now much clearer than before:

- `X · Y = 2` across the full catalogue
- the four global `XY` type counts are forced by `(n, s_X, s_Y)`
- the support sizes are always `n/2 + 1` and `n/2 - 1`

What remains nontrivial is how those forced global counts split by parity and residue class.

### Parity Split Still Small

Given

- `n`
- `(s_X, s_Y)`
- `(a_X, a_Y)`
- and `X · Y = 2`

the number of feasible odd/even splits of the four `XY` types stays small in the full corpus:

- up to `n = 32`, the count never exceeded `8`

So the parity-refined `XY` state space is still finite and small enough to feel theorem-like.

### But Low-Lag `U` Profiles Are Not Tiny

The low-lag autocorrelation prefix of `U` does not stay in a tiny catalogue.

For the first four lags, the number of distinct `U` profiles in the full corpus grows quickly:

- `n=10: 8`
- `12: 14`
- `16: 57`
- `20: 180`
- `24: 485`
- `28: 973`
- `32: 1677`

So the support-autocorrelation profile is not itself a tiny finite-state object. The exact invariant is global (`X · Y = 2`), while the detailed low-lag shape still has substantial freedom.

### The `U`-Bound Is Sharp Near The Boundary

Although the full low-lag `U` profile is not tiny, the support bound

- `|C_Z(s) + C_W(s)| <= ((n - s) + C_U(s)) / 2`

is not merely formal.

Across the full Kharaghani corpus:

- it is always sharp at the top three lags `s = n-3, n-2, n-1`
- it is still sharp for roughly `60%` of solutions at `s = n-4` and `s = n-5`

So the `U`-support geometry is weak in the middle of the sequence, but genuinely rigid near the outer boundary. That suggests the best use of this line is not as a full classification tool, but as an outer-shell theorem or pruning principle.

## Next Questions

- Can the `XY` type counts by residue class be expressed directly in terms of shell data plus a very small number of free parameters?
- Can the outer-lag recursion be rewritten in terms of `XY` types, rather than `X` and `Y` bits separately?
- Can the support sets `A` and `D` be characterized by a small family of admissible lag-difference statistics?
- Is there a mod-12 `XY/PQ` residue-class theorem that combines the mod-3 and mod-4 restrictions in a manageable way?
- Are there monotonic inequalities on these type counts that would prune entire shell families for general `n`?
