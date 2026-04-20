# XY Product Law Proof Sketch

This note rewrites the `XY` product-law argument in one indexing convention and in theorem-proof form, separate from the exploratory discussion in [xy-product.md](./xy-product.md).

The goal is to isolate the exact statement that should next be checked carefully and then formalized.

## Indexing Convention

Use 1-based indexing throughout.

- `X = (x_1, ..., x_n)`
- `Y = (y_1, ..., y_n)`
- `Z = (z_1, ..., z_n)`
- `W = (w_1, ..., w_{n-1})`

For a sequence `A`, write:

- `N_A(s) = sum_{i=1}^{len(A)-s} a_i a_{i+s}`

for the aperiodic autocorrelation at lag `s >= 1`.

Assume `(X, Y, Z, W)` is a Turyn quadruple, so:

- `N_X(s) + N_Y(s) + 2N_Z(s) + 2N_W(s) = 0`

for every `1 <= s <= n - 1`.

Define:

- `U_i := x_i y_i`

Assume only the endpoint normalization:

- `x_1 = y_1 = x_n = y_n = +1`

Equivalently:

- `U_1 = U_n = +1`

## Theorem Candidate

> **Claim.**
> For every `2 <= i <= n - 1`,
> `U_i = -U_{n+1-i}`.

Equivalently:

- `x_i y_i x_{n+1-i} y_{n+1-i} = -1`

for every interior index `i`.

## Step 1: The Parity Hammer

Fix `k` with `2 <= k <= n - 1`, and set:

- `s = n - k`

Then:

- `N_Z(s)` has `k` terms
- `N_W(s)` has `k - 1` terms

So `N_Z(s) + N_W(s)` is a sum of `2k - 1` signs, hence is odd.

Using the Turyn identity,

- `N_X(s) + N_Y(s) = -2(N_Z(s) + N_W(s))`

therefore:

- `N_X(n-k) + N_Y(n-k) ≡ 2 (mod 4)`

for every `2 <= k <= n - 1`.

Define:

- `T_k := N_X(n-k) + N_Y(n-k)`

Then:

- `T_k ≡ 2 (mod 4)`

for every `k >= 2`.

## Step 2: Rewrite T_k Using U

Since `U_i = x_i y_i`, we have:

- `y_i = U_i x_i`

Hence:

- `y_i y_j = U_i U_j x_i x_j`

So:

- `x_i x_j + y_i y_j = x_i x_j (1 + U_i U_j)`

Applying this at lag `n-k` gives:

- `T_k = sum_{i=1}^k x_i x_{n-k+i}(1 + U_i U_{n-k+i})`

Each summand lies in `{0, +2, -2}`.

## Step 3: Base Case k = 2

At lag `n - 2`:

- `T_2 = x_1 x_{n-1}(1 + U_1 U_{n-1}) + x_2 x_n(1 + U_2 U_n)`

Since `x_1 = x_n = U_1 = U_n = +1`, this becomes:

- `T_2 = x_{n-1}(1 + U_{n-1}) + x_2(1 + U_2)`

Now:

- if `U_{n-1} = -U_2`, exactly one term is active, so `T_2 = ±2`, hence `T_2 ≡ 2 (mod 4)`
- if `U_{n-1} = U_2 = -1`, then `T_2 = 0`
- if `U_{n-1} = U_2 = +1`, then `T_2 = 2x_{n-1} + 2x_2`, which is `0` or `4`

Therefore:

- `T_2 ≡ 2 (mod 4)` if and only if `U_{n-1} = -U_2`

But the parity hammer gives `T_2 ≡ 2 (mod 4)`, so:

- `U_{n-1} = -U_2`

## Step 4: Base Case k = 3

At lag `n - 3`:

- `T_3`
- `= x_1 x_{n-2}(1 + U_1 U_{n-2})`
- `+ x_2 x_{n-1}(1 + U_2 U_{n-1})`
- `+ x_3 x_n(1 + U_3 U_n)`

Using `x_1 = x_n = U_1 = U_n = +1`, this is:

- `T_3 = x_{n-2}(1 + U_{n-2}) + x_2 x_{n-1}(1 + U_2 U_{n-1}) + x_3(1 + U_3)`

From the base case `k = 2`:

- `U_{n-1} = -U_2`

So:

- `1 + U_2 U_{n-1} = 1 - U_2^2 = 0`

Thus:

- `T_3 = x_{n-2}(1 + U_{n-2}) + x_3(1 + U_3)`

Exactly as in the `k = 2` case:

- `T_3 ≡ 2 (mod 4)` if and only if `U_{n-2} = -U_3`

Using the parity hammer:

- `T_3 ≡ 2 (mod 4)`

hence:

- `U_{n-2} = -U_3`

## Step 5: Induction Step

Fix `k >= 4`.

Induction hypothesis:

- `U_{n+1-j} = -U_j` for every `2 <= j < k`

We will prove:

- `U_{n+1-k} = -U_k`

Start from:

- `T_k = sum_{i=1}^k x_i x_{n-k+i}(1 + U_i U_{n-k+i})`

Split this sum into:

- the endpoint terms `i = 1` and `i = k`
- interior mirror-pairs `i` and `k + 1 - i`
- if `k` is odd, the middle term `i = (k + 1)/2`

### Interior mirror-pairs

Take `i` with `2 <= i <= k - 1`, and pair term `i` with term `k + 1 - i`.

Their contribution is:

- `P_{i,k} := x_i x_{n-k+i}(1 + U_i U_{n-k+i})`
- `+ x_{k+1-i} x_{n+1-i}(1 + U_{k+1-i} U_{n+1-i})`

By the induction hypothesis:

- `U_{n+1-i} = -U_i`
- and since `n-k+i = n+1-(k+1-i)`, also
- `U_{n-k+i} = -U_{k+1-i}`

So:

- `P_{i,k}`
- `= x_i x_{n-k+i}(1 - U_i U_{k+1-i})`
- `+ x_{k+1-i} x_{n+1-i}(1 - U_{k+1-i} U_i)`
- `= (1 - U_i U_{k+1-i})(x_i x_{n-k+i} + x_{k+1-i} x_{n+1-i})`

Now:

- `1 - U_i U_{k+1-i}` is either `0` or `2`
- `x_i x_{n-k+i} + x_{k+1-i} x_{n+1-i}` is in `{-2, 0, 2}`

Hence:

- every interior pair `P_{i,k}` is a multiple of `4`

### Middle term when k is odd

If `k` is odd, let `m = (k + 1)/2`.

The middle summand is:

- `x_m x_{n+1-m}(1 + U_m U_{n+1-m})`

Since `m < k`, the induction hypothesis gives:

- `U_{n+1-m} = -U_m`

Therefore:

- `1 + U_m U_{n+1-m} = 1 - U_m^2 = 0`

So the middle term vanishes exactly.

### Endpoint pair

The endpoint contribution is:

- `E_k := x_1 x_{n+1-k}(1 + U_1 U_{n+1-k}) + x_k x_n(1 + U_k U_n)`

Using `x_1 = x_n = U_1 = U_n = +1`, this becomes:

- `E_k = x_{n+1-k}(1 + U_{n+1-k}) + x_k(1 + U_k)`

Now:

- if `U_{n+1-k} = -U_k`, exactly one term is active, so `E_k = ±2`, hence `E_k ≡ 2 (mod 4)`
- if `U_{n+1-k} = U_k = -1`, then `E_k = 0`
- if `U_{n+1-k} = U_k = +1`, then `E_k = 2x_{n+1-k} + 2x_k`, which is `0` or `4`

Therefore:

- `E_k ≡ 2 (mod 4)` if and only if `U_{n+1-k} = -U_k`

### Finish the induction

The full decomposition of `T_k` shows:

- `T_k = E_k +` (sum of interior pairs) `+` (optional middle term)

where:

- every interior pair is `0 (mod 4)`
- the middle term, if present, is exactly `0`

Hence:

- `T_k ≡ E_k (mod 4)`

By the parity hammer:

- `T_k ≡ 2 (mod 4)`

So:

- `E_k ≡ 2 (mod 4)`

and therefore:

- `U_{n+1-k} = -U_k`

This closes the induction.

## Conclusion

Under the Turyn identities and the endpoint normalization

- `x_1 = y_1 = x_n = y_n = +1`

we obtain:

- `U_i = -U_{n+1-i}` for every `2 <= i <= n - 1`

Equivalently:

- `x_i y_i x_{n+1-i} y_{n+1-i} = -1`

for every interior index.

Summing over all indices gives:

- `<X, Y> = sum_i x_i y_i = 2`

in this canonical orientation.

## Remaining Verification Tasks

Before treating this as settled, the following should still be checked carefully:

1. verify that the aperiodic lag indexing above matches the codebase conventions exactly
2. check the decomposition for small `k` by hand one more time
3. confirm that no hidden appeal to stronger BDKR rules slipped into the argument
4. formalize the theorem in Lean

The algebraic discovery phase, however, appears complete.
