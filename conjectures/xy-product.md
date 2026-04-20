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

Empirically, the current published data corpus up to `n = 32` satisfies:

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

## Minimal Canonical Assumptions

The argument below appears to need only the endpoint part of the canonical orientation:

- `x_1 = y_1 = x_n = y_n = +1`

Equivalently:

- `U_1 = U_n = +1`

No use is made of the deeper least-index BDKR rules in the induction step itself.

This is stronger than originally expected: if the derivation is correct, the interior skew law is a consequence of the Turyn identities plus the endpoint normalization.

## Base Cases

The induction starts at `k = 2`.

### Base case k = 2

At lag `s = n - 2`:

- `T_2 = N_X(n-2) + N_Y(n-2)`
- `= x_{n-1}(1 + U_{n-1}) + x_2(1 + U_2)`

There are no interior terms yet.

By the endpoint-pair analysis from the induction step:

- `T_2 ≡ 2 (mod 4)` if and only if `U_{n-1} = -U_2`

But the parity hammer gives:

- `T_2 ≡ 2 (mod 4)`

Hence:

- `U_{n-1} = -U_2`

### Base case k = 3

At lag `s = n - 3`:

- `T_3 = x_{n-2}(1 + U_{n-2}) + x_2 x_{n-1}(1 + U_2 U_{n-1}) + x_3(1 + U_3)`

From the `k = 2` base case:

- `U_{n-1} = -U_2`

so the middle term is exactly:

- `x_2 x_{n-1}(1 - U_2^2) = 0`

Therefore:

- `T_3 = x_{n-2}(1 + U_{n-2}) + x_3(1 + U_3)`

and again:

- `T_3 ≡ 2 (mod 4)` if and only if `U_{n-2} = -U_3`

Using the parity hammer:

- `T_3 ≡ 2 (mod 4)`

Hence:

- `U_{n-2} = -U_3`

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

## Paired-Term Derivation

The key quantity is:

- `T_k = N_X(n-k) + N_Y(n-k)`
- `= sum_{i=1}^k x_i x_{n-k+i} (1 + U_i U_{n-k+i})`

Assume inductively that:

- `U_{n+1-j} = -U_j` for every `2 <= j < k`

We now separate `T_k` into:

- the endpoint terms `i = 1` and `i = k`
- interior pairs `i` and `k + 1 - i`
- if `k` is odd, the middle term `i = (k + 1)/2`

### Interior pair formula

For `2 <= i <= k - 1`, pair term `i` with term `k + 1 - i`.

Define:

- `P_{i,k} := x_i x_{n-k+i}(1 + U_i U_{n-k+i})`
- `+ x_{k+1-i} x_{n+1-i}(1 + U_{k+1-i} U_{n+1-i})`

By the induction hypothesis:

- `U_{n+1-i} = -U_i`
- `U_{n-k+i} = U_{n+1-(k+1-i)} = -U_{k+1-i}`

So:

- `P_{i,k}`
- `= x_i x_{n-k+i}(1 - U_i U_{k+1-i})`
- `+ x_{k+1-i} x_{n+1-i}(1 - U_{k+1-i} U_i)`
- `= (1 - U_i U_{k+1-i}) (x_i x_{n-k+i} + x_{k+1-i} x_{n+1-i})`

Now:

- `1 - U_i U_{k+1-i}` is either `0` or `2`
- `x_i x_{n-k+i} + x_{k+1-i} x_{n+1-i}` is in `{-2, 0, 2}`

Therefore:

- every interior pair `P_{i,k}` is a multiple of `4`

### Middle term when k is odd

If `k` is odd, let `m = (k + 1)/2`.

Then the middle summand is:

- `x_m x_{n+1-m} (1 + U_m U_{n+1-m})`

Since `m < k` for `k >= 3`, the induction hypothesis gives:

- `U_{n+1-m} = -U_m`

Hence:

- `1 + U_m U_{n+1-m} = 1 - U_m^2 = 0`

So the middle term vanishes exactly.

### Endpoint pair

The remaining terms are:

- `E_k := x_1 x_{n+1-k}(1 + U_{n+1-k}) + x_k x_n(1 + U_k)`

In the canonical orientation:

- `x_1 = x_n = +1`

so:

- `E_k = x_{n+1-k}(1 + U_{n+1-k}) + x_k(1 + U_k)`

Each factor `1 + U_*` is either:

- `0` if `U_* = -1`
- `2` if `U_* = +1`

Thus:

- if `U_{n+1-k} = -U_k`, then exactly one of the two endpoint terms is active, so `E_k = ±2`, hence `E_k ≡ 2 (mod 4)`
- if `U_{n+1-k} = U_k = -1`, then `E_k = 0`
- if `U_{n+1-k} = U_k = +1`, then `E_k = 2x_{n+1-k} + 2x_k`, which is `0` or `4`, hence `E_k ≡ 0 (mod 4)`

So in every case:

- `E_k ≡ 2 (mod 4)` if and only if `U_{n+1-k} = -U_k`

### Conclusion of the induction step

The full sum `T_k` is:

- `T_k = E_k +` (sum of interior pairs) `+` (optional middle term)

and:

- every interior pair is `0 (mod 4)`
- the middle term, when present, is exactly `0`

Therefore:

- `T_k ≡ E_k (mod 4)`

But by the parity hammer:

- `T_k ≡ 2 (mod 4)`

Hence:

- `E_k ≡ 2 (mod 4)`

and therefore:

- `U_{n+1-k} = -U_k`

This is exactly the next skew step.

So modulo the base cases and the canonical endpoint assumptions, the induction is complete.

## Updated Status

The proof picture is now:

- base cases: explicit at `k = 2` and `k = 3`
- general induction step: given by the paired-term derivation above
- assumptions used: currently just the canonical endpoint pins `x_1 = y_1 = x_n = y_n = +1`

So the main remaining task is no longer algebraic discovery. It is proof cleanup:

1. rewrite the whole argument as a single clean induction theorem
2. check all indexing carefully in one convention
3. verify there is no hidden use of stronger BDKR rules

If that all survives, the product law is no longer conjectural in canonical orientation.

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

At this point the next task is not discovery but cleanup.

## Clean Theorem Shape

The statement that now looks provable is:

> **Theorem candidate.**
> Let `(X, Y, Z, W)` be a Turyn quadruple with
> `x_1 = y_1 = x_n = y_n = +1`.
> Define `U_i = x_i y_i`.
> Then for every `2 <= i <= n - 1`,
> `U_i = -U_{n+1-i}`.

### Proof skeleton

1. For each `k >= 2`, define
   - `T_k := N_X(n-k) + N_Y(n-k)`.
2. By the parity hammer,
   - `T_k ≡ 2 (mod 4)`.
3. Base case `k = 2` gives
   - `U_{n-1} = -U_2`.
4. Base case `k = 3` gives
   - `U_{n-2} = -U_3`.
5. For the induction step:
   - assume `U_{n+1-j} = -U_j` for `2 <= j < k`
   - decompose `T_k` into endpoint terms, interior mirror-pairs, and the optional middle term
   - interior pairs are all `0 (mod 4)`
   - the middle term is exactly `0`
   - so `T_k ≡ E_k (mod 4)`
   - and `E_k ≡ 2 (mod 4)` if and only if `U_{n+1-k} = -U_k`
   - hence `U_{n+1-k} = -U_k`

This proves the full interior skew law.

## What Should Be Checked Next

The remaining checks are:

1. convert everything to one indexing convention, preferably 0-based to match the Rust code or 1-based to match BDKR, but not both
2. verify the theorem really uses only:
   - the Turyn lag identities
   - the sequence lengths
   - the endpoint normalization
3. test the proof statement against a few known examples in both indexing conventions
4. then formalize the theorem in Lean

So the next serious move is:

- write the proof once in a fully clean, minimal theorem-proof format

rather than continue exploratory algebra.
