# Steps Informal Proof

This note gives an informal, mathematician-readable proof of the standalone
pipeline

`TurynType n -> TSequence (3*n - 1) -> IntMat (4*(3*n - 1))`.

It is meant to match the structure of

- [BaseSequence.lean](/C:/ver/turyn/lean/Turyn/BaseSequence.lean)
- [TSequence.lean](/C:/ver/turyn/lean/Turyn/TSequence.lean)
- [GoethalsSeidel.lean](/C:/ver/turyn/lean/Turyn/GoethalsSeidel.lean)
- [GSArrayBridge.lean](/C:/ver/turyn/lean/Turyn/GSArrayBridge.lean)

without relying on [Hadamard.lean](/C:/ver/turyn/lean/Turyn/Hadamard.lean).

## References

- Segura Ugalde and Piza Volio, *Turyn Type Sequences*:
  <https://www.scielo.sa.cr/scielo.php?pid=S1409-24332019000200253&script=sci_arttext>
- Sage `T_sequences` documentation:
  <https://doc.sagemath.org/html/en/reference/combinat/sage/combinat/t_sequences.html>
- Goethals and Seidel, *Orthogonal matrices with zero diagonal*:
  <https://doi.org/10.4153/CJM-1967-091-8>
- Seberry and Yamada, survey on Hadamard matrices and sequences:
  <https://citeseerx.ist.psu.edu/document?doi=1be6cc24ca39006726f43756dbd9130593a8a365&repid=rep1&type=pdf>

## Notation

For a finite sequence `u = (u_0, ..., u_{m-1})`, write

`N_u(s) = sum_{i=0}^{m-1-s} u_i u_{i+s}`

for the aperiodic autocorrelation at shift `s`, and

`P_u(s) = sum_{i=0}^{m-1} u_i u_{i+s mod m}`

for the periodic autocorrelation.

For four sequences `u, v, w, t`, write

`N(u,v,w,t; s) = N_u(s) + N_v(s) + N_w(s) + N_t(s)`

and similarly

`P(u,v,w,t; s) = P_u(s) + P_v(s) + P_w(s) + P_t(s)`.

The defining property of a Turyn quadruple `(X,Y,Z,W)` of lengths
`(n,n,n,n-1)` is

`N_X(s) + N_Y(s) + 2N_Z(s) + 2N_W(s) = 0`

for every `1 <= s < n`.

## Main theorem

From every Turyn quadruple `(X,Y,Z,W)` of length pattern `(n,n,n,n-1)`, one can
construct a Hadamard matrix of order `4(3n-1)`.

The proof proceeds in four stages.

## Stage 1: from Turyn quadruples to base sequences

Define

- `A = Z || W`
- `B = Z || (-W)`
- `C = X`
- `D = Y`

where `||` denotes concatenation.

Then

- `|A| = |B| = 2n-1`,
- `|C| = |D| = n`.

We claim that `(A,B,C,D)` is a base-sequence quadruple, meaning that

`N_A(s) + N_B(s) + N_C(s) + N_D(s) = 0`

for every `s >= 1`.

### Proof

Expand `N_A(s)` and `N_B(s)` using the decomposition of a concatenated sequence.
For a fixed shift `s`, each of these contains three kinds of terms:

1. terms entirely inside the `Z` block,
2. terms entirely inside the `W` block,
3. cross terms that start in `Z` and land in `W`.

The first kind contributes `N_Z(s)` to both `N_A(s)` and `N_B(s)`.
The second kind contributes `N_W(s)` to both `N_A(s)` and `N_B(s)`.

The cross terms appear with opposite sign in `A` and `B`, because in `B` the
entire `W` block has been negated. Therefore those cross terms cancel when
`N_A(s)` and `N_B(s)` are added.

Hence

`N_A(s) + N_B(s) = 2N_Z(s) + 2N_W(s)`.

Adding `N_C(s) + N_D(s) = N_X(s) + N_Y(s)` gives

`N_A(s) + N_B(s) + N_C(s) + N_D(s)
 = N_X(s) + N_Y(s) + 2N_Z(s) + 2N_W(s)`.

If `1 <= s < n`, this is zero by the Turyn identity.

If `s >= n`, then `N_X(s) = N_Y(s) = N_Z(s) = 0`, and also `N_W(s) = 0`,
because the shift is at least the length of each sequence involved.

Therefore `(A,B,C,D)` is a base-sequence quadruple. `square`

## Stage 2: from base sequences to a T-sequence

Let `m = 3n - 1`. Define four sequences of length `m` by

- `a = A || 0_n`
- `b = 0_n || B`
- `c = 0_(2n-1) || (C + D)/2`
- `d = 0_(2n-1) || (C - D)/2`

This is the standard construction appearing in the T-sequence literature and in
the Sage documentation.

After substituting the particular base sequences from Stage 1, these become

- `a = Z || 0_(2n-1)`
- `b = 0_n || W || 0_n`
- `c = 0_(2n-1) || (X + Y)/2`
- `d = 0_(2n-1) || (X - Y)/2`

which is the form already used in the standalone Lean code.

### Lemma 2.1: support condition

For every index `i`, exactly one of `a_i, b_i, c_i, d_i` is nonzero, and that
nonzero value is `±1`.

### Proof

Split into three index ranges.

If `0 <= i < n`, then

- `a_i = Z_i`,
- `b_i = c_i = d_i = 0`.

Since `Z_i = ±1`, the claim follows.

If `n <= i < 2n-1`, then

- `b_i = W_{i-n}`,
- `a_i = c_i = d_i = 0`.

Since `W_{i-n} = ±1`, the claim follows.

If `2n-1 <= i < 3n-1`, write `j = i - (2n-1)`, so `0 <= j < n`. Then

- `a_i = b_i = 0`,
- `c_i = (X_j + Y_j)/2`,
- `d_i = (X_j - Y_j)/2`.

Because `X_j, Y_j` are each `±1`, there are only four cases:

- `(1,1)`, giving `(c_i,d_i) = (1,0)`,
- `(1,-1)`, giving `(0,1)`,
- `(-1,1)`, giving `(0,-1)`,
- `(-1,-1)`, giving `(-1,0)`.

So exactly one of `c_i, d_i` is nonzero and it is `±1`. `square`

### Lemma 2.2: periodic vanishing

For every `1 <= s < m`,

`P(a,b,c,d; s) = 0`.

### Proof

Use the identity

`P_u(s) = N_u(s) + N_u(m-s)`

valid for any sequence `u` of length `m` and any `1 <= s < m`.

Therefore it is enough to prove

`N(a,b,c,d; t) = 0`

for every `t >= 1`.

Now

- appending or prepending zeros does not change the relevant aperiodic
  autocorrelations,
- and
  `N_{(C+D)/2}(t) + N_{(C-D)/2}(t) = N_C(t) + N_D(t)`
  because the mixed terms cancel when the products are expanded.

So

`N(a,b,c,d; t) = N_A(t) + N_B(t) + N_C(t) + N_D(t) = 0`

by Stage 1. Hence `P(a,b,c,d; s) = 0`. `square`

## Stage 3: from a T-sequence to four ±1 sequences

Let `(a,b,c,d)` now be any T-sequence of common length `m`. Define

- `x1 = a + b + c + d`
- `x2 = a + b - c - d`
- `x3 = a - b + c - d`
- `x4 = a - b - c + d`

coordinatewise.

These are obtained by applying the `4 x 4` Hadamard sign matrix

```text
[ 1  1  1  1 ]
[ 1  1 -1 -1 ]
[ 1 -1  1 -1 ]
[ 1 -1 -1  1 ]
```

to the column vector `(a_i,b_i,c_i,d_i)^T` at each coordinate `i`.

### Lemma 3.1: each `xk` is ±1-valued

For every `i`, each of `x1_i, x2_i, x3_i, x4_i` is `±1`.

### Proof

At the index `i`, exactly one of `a_i,b_i,c_i,d_i` is nonzero and equals `±1`.
Substituting into the four linear combinations shows that each `xk_i` is
just `±` that same nonzero value. Hence each `xk_i` is `±1`. `square`

### Lemma 3.2: GS periodic identity

For every shift `s`,

`P_x1(s) + P_x2(s) + P_x3(s) + P_x4(s)
 = 4(P_a(s) + P_b(s) + P_c(s) + P_d(s))`.

### Proof

Fix `s`. At the summand level, expand

`x1_i x1_{i+s} + x2_i x2_{i+s} + x3_i x3_{i+s} + x4_i x4_{i+s}`.

Every mixed term, such as `a_i b_{i+s}` or `c_i d_{i+s}`, appears twice with
sign `+` and twice with sign `-`, so all mixed terms cancel. Each square term
survives four times. Thus the summand equals

`4(a_i a_{i+s} + b_i b_{i+s} + c_i c_{i+s} + d_i d_{i+s})`.

Summing over `i` modulo `m` gives the formula. `square`

### Corollary 3.3

For every `1 <= s < m`,

`P_x1(s) + P_x2(s) + P_x3(s) + P_x4(s) = 0`.

### Proof

Apply Lemma 3.2 and the T-sequence identity from Stage 2. `square`

## Stage 4: the Goethals-Seidel array

Let `X1, X2, X3, X4` be the circulant matrices generated by
`x1, x2, x3, x4`, and let `R` be the back-diagonal permutation matrix.

Using one of the standard Goethals-Seidel sign conventions, define

```text
H =
[ X1     X2 R    X3 R    X4 R  ]
[ -X2 R  X1     -X4^T R  X3^T R ]
[ -X3 R  X4^T R  X1     -X2^T R ]
[ -X4 R -X3^T R  X2^T R  X1     ].
```

We claim that `H` is a Hadamard matrix of order `4m`.

### Lemma 4.1: entrywise ±1

Every entry of `H` is `±1`.

### Proof

Each `Xk` is circulant with entries taken from a `±1` sequence. Reversal,
transpose, and multiplication by `-1` preserve the set `{±1}`. `square`

### Lemma 4.2: circulant row inner products

If `row_i(X)` and `row_j(X)` are rows of the circulant matrix generated by a
length-`m` sequence `x`, then

`<row_i(X), row_j(X)> = P_x((j-i) mod m)`

up to the chosen indexing convention.

### Proof

A circulant row is a cyclic shift of the base sequence. Reindex the dot product
sum by shifting the summation variable, and the result is exactly the periodic
autocorrelation at the relative shift between the two rows. `square`

### Lemma 4.3: effect of reversal and transpose blocks

The dot products of rows involving `XR`, `X^T R`, or `-XR` can be rewritten in
terms of the same periodic autocorrelation expressions, with only the shift and
overall sign changed.

### Proof

Reversal and transpose do not create new algebra; they only change which cyclic
shift is being compared to which other cyclic shift. A direct index substitution
shows that every such row dot product is still a periodic autocorrelation term
of the underlying generating sequence. An overall minus sign changes only the
sign of the dot product. `square`

### Lemma 4.4: same block-row, different offset

If two distinct rows of `H` lie in the same block-row, then their inner product
is

`P_x1(s) + P_x2(s) + P_x3(s) + P_x4(s)`

for some nonzero shift `s`.

### Proof

Write the row as a concatenation of four block rows. The inner product splits
as the sum of four block inner products. Apply Lemmas 4.2 and 4.3 blockwise.
Because all four blocks are compared at the same relative row offset, the four
terms combine into exactly the displayed periodic sum. Since the rows are
distinct, the relative shift `s` is nonzero. `square`

### Lemma 4.5: different block-rows

If two rows of `H` lie in different block-rows, then their inner product is
again

`P_x1(s) + P_x2(s) + P_x3(s) + P_x4(s)`

for some shift `s`, with the signs arranged by the GS pattern.

### Proof

Again split the inner product into four block contributions. The sign pattern
and transpose/reversal pattern in the GS array are chosen precisely so that the
block contributions simplify to the same periodic-autocorrelation sum as in
Lemma 4.4. This is the classical Goethals-Seidel computation. `square`

### Lemma 4.6: off-diagonal orthogonality

If two distinct rows of `H` are chosen, their inner product is `0`.

### Proof

Apply Lemma 4.4 or Lemma 4.5, then use Corollary 3.3. `square`

### Lemma 4.7: diagonal norm

Each row of `H` has self-dot-product `4m`.

### Proof

Each row has exactly `4m` entries, each equal to `±1`. Therefore the sum of
squares of its entries is `4m`. `square`

### Theorem 4.8

`H` is a Hadamard matrix of order `4m`.

### Proof

By Lemma 4.1, every entry is `±1`. By Lemma 4.6, distinct rows are orthogonal.
By Lemma 4.7, each row has norm `4m`. Therefore

`H H^T = 4m I`,

so `H` is Hadamard. `square`

## Conclusion

Starting from a Turyn quadruple `(X,Y,Z,W)` of order `n`:

1. Stage 1 produces base sequences `(A,B,C,D)`.
2. Stage 2 produces a T-sequence `(a,b,c,d)` of length `m = 3n-1`.
3. Stage 3 produces four `±1` sequences `(x1,x2,x3,x4)` of length `m`.
4. Stage 4 applies the Goethals-Seidel construction to obtain a Hadamard matrix
   of order `4m = 4(3n-1)`.

Therefore every Turyn quadruple of order `n` yields a Hadamard matrix of order
`4(3n-1)`.

## Lean-oriented refinement of Stage 4

The GS stage should be formalized in three layers.

### Layer A: sequence algebra

Target lemmas:

1. accessor formulas for `tseqCombine1` to `tseqCombine4`;
2. `±1`-valuedness of each combined sequence;
3. the GS periodic identity from Lemma 3.2;
4. the vanishing corollary 3.3.

Argument:

All of these are direct expansions using the T-sequence support identity and
simple algebraic cancellation. No matrix reasoning is needed here.

### Layer B: circulant representation

Target lemmas:

5. dot product of two circulant rows equals periodic autocorrelation;
6. reversal/transposition/sign bookkeeping lemmas;
7. entrywise `±1` and row-length facts for the final GS matrix.

Argument:

These are index manipulations. The content is only that circulant rows are
cyclic shifts, and reversal/transposition merely alter the indexing formula.

### Layer C: block orthogonality

Target lemmas:

8. same block-row, different offset;
9. different block-rows;
10. diagonal norm.

Argument:

Each block inner product is reduced by Layer B to a periodic-autocorrelation
term, and the GS sign pattern is designed so the total collapses to the sum from
Corollary 3.3. Once those reductions are proved, the final Hadamard theorem is
just a wrapper.

## Main warning

The raw array built directly from the `{0, ±1}` T-sequences is not the final
Hadamard matrix. The final theorem must target the GS array built from the
derived `±1` sequences `x1, x2, x3, x4`.
