# Canonicalization of Turyn sequences

## The symmetry group

A Turyn 4-tuple `(X, Y, Z, W)` of ±1 sequences has a natural symmetry
group whose orbits define equivalent solutions.  The generators (per
**Best, Đoković, Kharaghani, Ramp — "Turyn type sequences: classification,
enumeration, and construction", 2012**) are:

| Generator | Action                                                     | Size |
|-----------|------------------------------------------------------------|------|
| **T1**    | Negate any *one* of X, Y, Z, W (4 independent generators)  | 2⁴ = 16 |
| **T2**    | Reverse any *one* of X, Y, Z, W (4 independent generators) | 2⁴ = 16 |
| **T3**    | Simultaneously alternate all four (`a[i] ↦ (-1)^i·a[i]`)   | 2    |
| **T4**    | Interchange X ↔ Y                                          | 2    |

Each generator preserves the aperiodic autocorrelation identity

    N_X(s) + N_Y(s) + 2·N_Z(s) + 2·N_W(s) = 0   for all s ≥ 1

so every element of the group sends a Turyn solution to another Turyn
solution.  The full group has size at most 16·16·2·2 = **1024** (orbits
may have stabilisers, so actual orbit sizes divide 1024).

Prior to this work the codebase only broke T1 (a factor-16 reduction),
leaving the remaining factor ~64 on the table.

## Canonical form (BDKR §2, 6 rules)

Using 1-indexed notation with `(a, b, c, d) = (X, Y, Z, W)`, `len(a)=len(b)=len(c)=n`,
`len(d)=n-1`:

1. **(i)** `a[1] = a[n] = b[1] = b[n] = c[1] = d[1] = +1`
2. **(ii)** If `i` is the least index with `a[i] ≠ a[n+1-i]`, then `a[i] = +1`.
3. **(iii)** Same as (ii), for `b`.
4. **(iv)** If `i` is the least index with `c[i] == c[n+1-i]` *(note `==`, not `≠`)*, then `c[i] = +1`.
5. **(v)**  If `i` is the least index with `d[i]·d[n-i] ≠ d[n-1]`, then `d[i] = +1`.
6. **(vi)** Assume `n > 2`.  If `a[2] ≠ b[2]`, then `a[2] = +1`.  Otherwise (`a[2] = b[2]`), `a[n-1] = +1` *and* `b[n-1] = -1`.

BDKR show these six rules identify a unique representative in every orbit,
so applying them during search costs nothing and prunes ≈1024/|stabiliser|.

An additional consequence of the full rule set: **`c[n] = -1` for `n > 1`.**

## What the codebase enforces

### Currently enforced (post-2026-04 update)

| Rule(s) | Site                                 | What is added                                  |
|---------|--------------------------------------|------------------------------------------------|
| (i)     | `build_sat_xy_clauses`               | `x[0]=x[n-1]=y[0]=y[n-1]=+1` unit clauses       |
| (i)     | `sat_encode`                         | same, plus `z[0]=w[0]=+1`                       |
| (i)     | `sat_encode_quad_pb_unified`         | same as above, gated on `fixed.is_none()`       |
| (i)     | MDD builder (`src/mdd_zw_first.rs`)  | XY sub-MDD: branch `0b11` pinned at positions `0` and `2k-1` (⇒ `x[0]=y[0]=x[n-1]=y[n-1]=+1`); ZW half: position 0 pinned (⇒ `z[0]=w[0]=+1`) |
| (ii)    | `build_sat_xy_clauses`, `sat_encode` | palindromic-break chain on X via aux `diff_j ↔ x[j]⊕x[n-1-j]`, start `j=1` |
| (iii)   | `build_sat_xy_clauses`, `sat_encode` | palindromic-break chain on Y (same shape as ii) |
| (iv)    | `sat_encode`                         | palindromic-EQ-break chain on Z (equality polarity, start `j=0`) |
| (v)     | `sat_encode`                         | alternation-break chain on W via `v_k ↔ d[k]⊕d[m-1-k]⊕d[m-1]` |
| (vi)    | `build_sat_xy_clauses`, `sat_encode` | 5 clauses encoding the conditional X↔Y swap break |
| tuple-level | `SumTuple::norm_key`             | `|σ_X|, |σ_Y|, |σ_Z|, |σ_W|` only (no X↔Y sort — rule (vi) breaks T4). Factor 16. |

The palindromic/alternation/swap-break encoding is shared across the
XY template and the legacy full encoder via `add_palindromic_break`,
`add_alternation_break`, and `add_swap_break` helpers near the top of
`src/main.rs`.  Aux vars are allocated contiguously above the
sequence variable block so they don't collide with XNOR / quad-PB
aux blocks.

### Test-suite status

All 26 tests pass under the full rule set (i)–(vi).  Five tests were adjusted to operate
on canonical-orbit data:

- `sat_solves_tt2`: uses the T3-alternated canonical form
  `Z=[+,-], W=[+]` ⇒ `X=Y=[+,+]` (the original `Z=[+,+], W=[+]` ⇒
  `X=Y=[+,-]` pair violates rule i).
- `sat_xy_solves_known_tt36_zw`: alternates the hardcoded TT(36) in
  the test body (a[i] ↦ (-1)^i·a[i] on all four sequences) so
  `x[35]=y[35]=+1` in the canonical orbit.
- `hybrid_finds_tt4`, `benchmark_profile_n4_finds_solution_fast`,
  `hybrid_finds_tt6`: switched from Cross mode to Apart mode.
  The Cross-mode spectral pair filter is tight enough at n=4, 6 to
  reject the one canonical `(Z,W)` pair that satisfies rule (i);
  the Apart (MDD-walker) path uses per-lag SAT constraints and
  recovers the canonical TT cleanly.

### Follow-up work

Rules (ii), (iii), (iv), (v), (vi) are now wired into the SAT
encoders.  What's still *not* done:

- **Rules (iv)/(v) in the MDD middle-SAT solvers** (`src/sat_z_middle.rs`,
  `src/sat_w_middle.rs`).  The middle solver only sees middle vars,
  so boundary-boundary palindrome pairs must be enforced at MDD-walk
  time and boundary-middle propagation would need threading through
  the `LagTemplate`.  A more mechanical refactor.
- **MDD pruning for rules (ii)/(iii) at boundary positions.**  For
  palindrome pairs (j, n-1-j) that fall wholly inside the boundary
  (j < k), the first-violation rule can be evaluated at MDD gen
  time.  Could shrink the XY sub-MDD further.

### Original encoding sketches (for the record)

#### Rules (ii), (iii), (iv) — palindromic-break chain

For each sequence `s` of length `n` and each position `i ∈ 2..⌊n/2⌋+1`, introduce an auxiliary variable

    diff_i ↔ (s[i] XOR s[n-1-i])         // 4 binary clauses defining diff_i

Then for each `i`, add the implication

    diff_2 ∨ diff_3 ∨ … ∨ diff_{i-1} ∨ (s[i] = +1) ∨ (s[n-1-i] = -1)      // rule ii / iii
    diff_2 ∨ diff_3 ∨ … ∨ diff_{i-1} ∨ (s[i] = +1) ∨ (s[n-1-i] = +1)      // rule iv (note polarity)

Total ≈ `n²/4` clauses + `n/2` aux vars per rule.  For `n=56` this is ~784 main clauses and 28 aux vars per rule — small relative to the ~`n³`-sized autocorrelation encoding, so the SAT impact is negligible; the *pruning* effect is what we're buying.

In the MDD, rules (iv) for Z can be partially enforced at the boundary positions the MDD navigates (i=1..k-1 and i=n-k..n-1).  The "middle" positions must remain a SAT-side obligation, since the MDD only knows the boundary.

#### Rule (v) — alternation-break for W

`d[i]·d[n-i] ≠ d[n-1]` is the "d is not alternation-symmetric at lag `(n-1)-i+i = n-1`".  Let `ref = d[n-1]` (the last element of W).  For each `i ∈ 1..(n-1)/2`, define

    alt_i ↔ (d[i]·d[n-i] == ref)     // encoded via two aux XOR clauses

Then:

    ¬alt_1 ∨ ¬alt_2 ∨ … ∨ ¬alt_{i-1} ∨ alt_i ∨ (d[i] = +1)

#### Rule (vi) — conditional swap break

This is a 2-clause gadget on the XY encoding:

    (x_var(1) ∨ ¬y_var(1))                    // forbid a[2]=-1, b[2]=+1
    (x_var(1) ∨ x_var(n-2))                   // if ¬(a[2]=+1 ∧ b[2]=-1), a[n-1]=+1
    (¬y_var(1) ∨ x_var(n-2))
    (x_var(1) ∨ ¬y_var(n-2))                  // if ¬(a[2]=+1 ∧ b[2]=-1), b[n-1]=-1
    (¬y_var(1) ∨ ¬y_var(n-2))

(In 0-indexed terms `a[2]→index 1`, `a[n-1]→index n-2`.)

#### MDD pruning

`gen_mdd` could bake in rule (iv)'s partial form (at boundary positions of Z) and the implication `c[n]=-1` (pinning the last Z branch at position `n-1`).  This shrinks the on-disk MDD directly — roughly a factor 2 saving on node count.  Requires regenerating all `mdd-*.bin` artefacts.

## Benchmarking the reduction

See `docs/OPTIMIZATION_LOG.md` for the measured impact of rule (i).  The
expected speed-up from the full 6-rule set is **up to ~64×** on
exhaustion-bound searches (the MDD walker + SAT together prune the
group's orbit of size 1024 instead of the current orbit of size 16).
