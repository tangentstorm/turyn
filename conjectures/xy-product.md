# XY Product Law

This note records the current informal proof program for the `XY` product-law conjecture for Turyn-type sequences.

The conjecture is motivated by the known corpus and by the high-lag parity structure of the Turyn equations. It is not yet fully proved. The goal of this file is to make the current state precise enough that a future proof attempt, Lean formalization, or solver implementation has a stable target.

## Statement

Let `(X, Y, Z, W)` be a `TT(n)` quadruple, with:

- `X, Y, Z` of length `n`
- `W` of length `n - 1`
- entries in `{+1, -1}`

and satisfying the aperiodic Turyn identities:

- `N_X(s) + N_Y(s) + 2 N_Z(s) + 2 N_W(s) = 0` for `1 <= s <= n - 1`

Define the product sequence:

- `U_i := x_i y_i`

The conjectural canonical-form law is:

- `U_1 = U_n = +1`
- `U_i = -U_{n+1-i}` for `2 <= i <= n - 1`

Equivalently:

- `x_i y_i x_{n+1-i} y_{n+1-i} = -1` for `2 <= i <= n - 1`

This implies:

- `<X, Y> = sum_i x_i y_i = 2`

and the orbit-invariant version would be:

- `|<X, Y>| = 2`

since negating exactly one of `X` or `Y` flips the sign of `U`.

## Why This Looks Plausible

Empirically, the Kharaghani corpus up to `n = 32` satisfies:

- `U_1 = U_n = +1`
- `U_i = -U_{n+1-i}` for every interior index

This immediately forces:

- `sum_i U_i = 2`

because the interior terms cancel in mirrored pairs.

This law also compresses the `XY` half of the search significantly:

- the interior mirror pairs of `U` are no longer independent
- this removes `n/2 - 1` bits from the `XY` search if enforced exactly

## The Parity Hammer

Fix a high lag `s = n - k`, where `1 <= k <= n - 1`.

At this lag:

- `N_Z(s)` has `k` terms
- `N_W(s)` has `k - 1` terms
- so `N_Z(s) + N_W(s)` is a sum of `2k - 1` signs

Therefore:

- `N_Z(s) + N_W(s)` is always odd

Using the Turyn identity,

- `N_X(s) + N_Y(s) + 2(N_Z(s) + N_W(s)) = 0`

it follows that:

- `N_X(s) + N_Y(s) ≡ 2 (mod 4)`

for every high lag `s = n - k`.

This is the basic parity input behind the conjectured induction.

## Rewriting the XY Side Using U

Since `U_i = x_i y_i`, we can write:

- `y_i = U_i x_i`

and therefore:

- `y_i y_j = U_i U_j x_i x_j`

So for any lag `s`,

- `N_X(s) + N_Y(s) = sum_i (x_i x_{i+s} + y_i y_{i+s})`
- `= sum_i x_i x_{i+s} (1 + U_i U_{i+s})`

In particular, at lag `s = n - k`,

- `T_k := N_X(n-k) + N_Y(n-k)`
- `= sum_{i=1}^k x_i x_{n-k+i} (1 + U_i U_{n-k+i})`

Each summand lies in `{0, +2, -2}`.

This makes the mod-4 condition visible:

- `T_k ≡ 2 (mod 4)`

but it does not by itself force the next skew relation. The proof has to use more structure than parity alone.

## What Is Already Proved

The first two interior skew identities can be derived from the top-lag equations and the standard canonical boundary rules.

### Step 1

The relation

- `U_{n-1} = -U_2`

is proved from:

- the `s = n - 2` Turyn equation
- the standard canonical top-boundary rules
- the already-fixed endpoint values

### Step 2

The relation

- `U_{n-2} = -U_3`

is also derivable from the `s = n - 3` equation.

After simplification, the `XY` side is forced into a `±2` pattern compatible with the parity hammer, and under the local canonical rules this is equivalent to the second skew step.

So the conjecture is no longer purely empirical:

- the first two interior mirror-product identities are genuinely proved

## The Intended Induction

The target induction statement is:

- assume `U_{n+1-j} = -U_j` for all `2 <= j < k`
- prove `U_{n+1-k} = -U_k`

The correct object to study is:

- `T_k = N_X(n-k) + N_Y(n-k)`

which satisfies:

- `T_k ≡ 2 (mod 4)`

The naive argument would be:

- "all interior terms must vanish, so only the endpoint pair matters"

but this is not proved and is too strong as stated.

The more plausible route is:

1. write `T_k` in the `U`-expanded form
2. group the terms by mirror indices `i` and `k + 1 - i`
3. use the already-proved skew relations for smaller indices
4. show the grouped interior contribution is always `0 (mod 4)`
5. show the remaining endpoint contribution is `2 (mod 4)` exactly when `U_k = -U_{n+1-k}`

This would make the next skew relation the unique way to satisfy the mod-4 condition.

## Why Pairing Terms Looks Right

At lag `s = n - k`, the `i`th term uses the pair:

- `(i, n - k + i)`

If we pair index `i` with `k + 1 - i`, then:

- `n - k + (k + 1 - i) = n + 1 - i`

so the second paired term naturally touches the mirror of `i`.

That is the right indexing pattern for a proof of:

- `U_i = -U_{n+1-i}`

The main unresolved task is to simplify the paired sum cleanly enough that the mod-4 condition isolates the new mirror relation.

## Current Gap

The missing lemma is essentially:

- under the previously established skew relations near the boundary,
- the lag-`n-k` `XY` contribution satisfies
  - `T_k ≡ 2 (mod 4)` if and only if `U_k = -U_{n+1-k}`

This has been checked locally for small depths by explicit boundary-state enumeration, but it has not yet been proved in general.

So the present status is:

- base cases: proved for the first two interior mirror-product relations
- induction pattern: strongly suggested
- general step: still open

## Solver Interpretation

If the full law is assumed as a hypothetical search rule, it can be encoded as:

- `x_i y_i x_{n+1-i} y_{n+1-i} = -1` for `2 <= i <= n - 1`

or in Boolean form with `true = +1`, `false = -1`:

- `X_i XOR Y_i XOR X_{n+1-i} XOR Y_{n+1-i} = 1`

This is a structural, non-spectral constraint on the `XY` side.

## Relationship to the ZW Side

The `XY` product law also induces a useful bound on the `ZW` side.

Since:

- `x_i x_j + y_i y_j = x_i x_j (1 + U_i U_j)`

only same-support pairs contribute to the `XY` lag sum.

This yields the exact bound:

- `|N_Z(s) + N_W(s)| <= ((n - s) + N_U(s)) / 2`

Empirically, equality holds for all known examples at:

- `s = n - 1`
- `s = n - 2`
- `s = n - 3`

This is a separate, weaker conjectural search rule, documented in the search plan as:

- `--zw-u-bound-tight`

## Next Proof Tasks

The most concrete next steps are:

1. derive a symbolic paired-term formula for `T_k`
2. isolate the dependence on `U_k` and `U_{n+1-k}`
3. prove the interior paired contribution is always `0 (mod 4)`
4. close the induction

If that works, the product law becomes a theorem rather than a corpus pattern.
