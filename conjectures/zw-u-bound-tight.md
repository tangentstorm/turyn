# ZW U-Bound Tightness

This note records the high-lag `ZW`-side conjecture that emerged from the corpus analysis and from Claude’s math notes.

Credit:

- the underlying `U`-bound perspective is now integrated with the `XY` product-law work in [codex-math-notes.md](../codex-math-notes.md)
- the search-conjecture version of the high-lag equality is inspired by the `claude-math-notes.md` line of modular / boundary constraints

In the search plan this is the conjectural flag:

- `--zw-u-bound-tight`

## Statement

Let:

- `U_i := x_i y_i`
- `N_A(s)` denote the aperiodic autocorrelation at lag `s`

Then the Turyn identities imply the bound

- `|N_Z(s) + N_W(s)| <= ((n - s) + N_U(s)) / 2`

where:

- `N_U(s) = sum_i U_i U_{i+s}`

The conjecture is that this bound is actually tight at the outermost lags:

- `|N_Z(s) + N_W(s)| = ((n - s) + N_U(s)) / 2`

for:

- `s = n - 1`
- `s = n - 2`
- `s = n - 3`

There is also a more aggressive version that would additionally include:

- `s = n - 4`
- `s = n - 5`

but that version is much less stable empirically and should not be treated as the default conjecture.

## Why The Bound Exists

The key identity on the `XY` side is:

- `x_i x_j + y_i y_j = x_i x_j (1 + U_i U_j)`

So:

- if `U_i != U_j`, then `x_i x_j + y_i y_j = 0`
- only same-support pairs contribute to `N_X(s) + N_Y(s)`

The number of same-support lag-`s` pairs is:

- `((n - s) + N_U(s)) / 2`

Therefore:

- `|N_X(s) + N_Y(s)| <= (n - s) + N_U(s)`

Using the Turyn identity

- `N_X(s) + N_Y(s) = -2(N_Z(s) + N_W(s))`

gives the bound

- `|N_Z(s) + N_W(s)| <= ((n - s) + N_U(s)) / 2`

This bound itself is exact and proved.

What is conjectural is:

- equality at the top few lags

## Empirical Support

In the known corpus, the bound is extremely sharp near the boundary.

Observed:

- equality holds for every known TT at
  - `s = n - 1`
  - `s = n - 2`
  - `s = n - 3`
- equality holds roughly 60% of the time at
  - `s = n - 4`
  - `s = n - 5`

So the conservative search conjecture is:

- enforce tightness only for `n - 1, n - 2, n - 3`

## Why This Is Useful

This is attractive as a search rule because:

- it acts on the `ZW` side, not the `XY` side
- it is boundary-native
- it is strongest exactly where the MDD / bounce search starts
- it composes with either ordinary `XY` search or the stronger `(X,U)` product-law search

In particular, it gives an additional coupling channel:

- once enough of `U` is known to compute `N_U(s)` at outer lags
- any `ZW` branch whose `|N_Z(s) + N_W(s)|` does not match the implied value can be rejected immediately

## Relationship To The XY Product Law

This conjecture is weaker than the full `XY` product law.

It does not require proving:

- `U_i = -U_{n+1-i}` for all interior `i`

Instead, it only uses:

- the derived high-lag bound from `U`
- plus the empirical observation that the bound is saturated at the top boundary

So it should be treated as:

- a separate conjectural search filter
- not as a corollary already proved from the product law

## Search Flag

Recommended search flag:

- `--zw-u-bound-tight`

Recommended semantics:

- enforce tightness only at `s in {n-1, n-2, n-3}`

Possible future aggressive mode:

- `--zw-u-bound-tight=5`

meaning also enforce `s = n - 4, n - 5`

but that should stay experimental unless the corpus support or proof story improves.
