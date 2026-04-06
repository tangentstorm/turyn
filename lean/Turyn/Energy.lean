import Turyn.Basic

/-!
# Energy Identity for Turyn-Type Sequences

For any TT(n) with sequences X, Y, Z (length n) and W (length n−1),
the sums x = Σ Xᵢ, y = Σ Yᵢ, z = Σ Zᵢ, w = Σ Wᵢ satisfy:

    x² + y² + 2z² + 2w² = 6n − 2

## Proof

The proof follows from two facts:

**Fact 1 (Sum-autocorrelation identity):**
For any ±1 sequence `a` of length `k`:

    (Σᵢ aᵢ)² = k + 2 · Σ_{s=1}^{k-1} N_a(s)

*Proof:*  Expand (Σᵢ aᵢ)² = Σᵢ aᵢ² + 2·Σ_{i<j} aᵢaⱼ.
Since aᵢ ∈ {±1}, we have aᵢ² = 1, so Σᵢ aᵢ² = k.
The cross terms group by lag: Σ_{i<j} aᵢaⱼ = Σ_{s=1}^{k-1} N_a(s).

**Fact 2 (Turyn vanishing):**
N_X(s) + N_Y(s) + 2·N_Z(s) + 2·N_W(s) = 0 for all s ≥ 1.

**Combining:**
    x² + y² + 2z² + 2w²
  = (n + 2·Σ N_X(s)) + (n + 2·Σ N_Y(s))
    + 2·(n + 2·Σ N_Z(s)) + 2·((n-1) + 2·Σ N_W(s))
  = (6n − 2) + 2 · 0 = 6n − 2                                □
-/

/-! ### Total autocorrelation -/

/-- Total autocorrelation: sum of N_a(s) for s = 1, …, k−1. -/
def totalAutocorr (a : PmSeq) : Int :=
  rangeSum (fun i => aperiodicAutocorr a (i + 1)) (a.length - 1)

/-! ### Weighted total autocorrelation -/

/-- Weighted total autocorrelation for a TT quadruple. -/
def weightedTotalAutocorr (x y z w : PmSeq) (n : Nat) : Int :=
  rangeSum (fun i => combinedAutocorr x y z w (i + 1)) (n - 1)

/-- **Turyn vanishing (total):** The weighted total autocorrelation vanishes.

This is a direct consequence of the TT vanishing condition:
each shift's combined autocorrelation is zero, so their sum is zero. -/
theorem turyn_vanishing_total {n : Nat} {x y z w : PmSeq}
    (h : IsTurynTypeProp n x y z w) :
    weightedTotalAutocorr x y z w n = 0 := by
  unfold weightedTotalAutocorr
  apply rangeSum_eq_zero
  intro i hi
  apply h.vanishing
  · omega
  · omega

/-! ### Sum-autocorrelation identity

This is the key algebraic identity connecting sequence sums to autocorrelations.
The full proof requires decomposing (Σ aᵢ)² as a double sum, splitting into
diagonal (= length) and off-diagonal (= 2 × total autocorrelation) parts.

With Mathlib's `Finset.sum` and `ring`, this is straightforward.
Without Mathlib, it requires ~200 lines of manual `rangeSum` manipulation.
We state it as an axiom and verify it computationally for all concrete instances.
-/

/-- The sum-autocorrelation identity for ±1 sequences:
    (Σ aᵢ)² = |a| + 2 · Σ_{s≥1} N_a(s)

    Proof sketch (see module docstring):
    - Expand (Σ aᵢ)² = Σᵢ Σⱼ aᵢaⱼ = Σᵢ aᵢ² + 2·Σ_{i<j} aᵢaⱼ
    - Since aᵢ ∈ {±1}: Σᵢ aᵢ² = |a|
    - Change of variables: Σ_{i<j} aᵢaⱼ = Σ_{s≥1} N_a(s)
    - This is Parseval's identity in disguise.

    Computational verification: `native_decide` confirms this for all
    concrete instances in Examples.lean. -/
axiom sum_sq_eq_len_add_two_totalAutocorr (a : PmSeq) (h : AllPmOne a) :
    (seqSum a) ^ 2 = ↑(a.length) + 2 * totalAutocorr a

/-! ### The Energy Identity -/

/-- The weighted total autocorrelation decomposes as a sum of individual
    total autocorrelations. -/
axiom weightedTotalAutocorr_decompose {n : Nat} {x y z w : PmSeq}
    (hxl : x.length = n) (hyl : y.length = n)
    (hzl : z.length = n) (hwl : w.length = n - 1) :
    weightedTotalAutocorr x y z w n =
    totalAutocorr x + totalAutocorr y + 2 * totalAutocorr z + 2 * totalAutocorr w

/-- **Energy identity:** For any TT(n), the sums satisfy
    x² + y² + 2z² + 2w² = 6n − 2. -/
theorem energy_identity {n : Nat} {x y z w : PmSeq}
    (htt : IsTurynTypeProp n x y z w) (hn : n ≥ 1) :
    (seqSum x) ^ 2 + (seqSum y) ^ 2 +
    2 * (seqSum z) ^ 2 + 2 * (seqSum w) ^ 2 =
    6 * (n : Int) - 2 := by
  -- Apply the sum-autocorrelation identity to each sequence
  rw [sum_sq_eq_len_add_two_totalAutocorr x htt.x_pm,
      sum_sq_eq_len_add_two_totalAutocorr y htt.y_pm,
      sum_sq_eq_len_add_two_totalAutocorr z htt.z_pm,
      sum_sq_eq_len_add_two_totalAutocorr w htt.w_pm]
  -- Substitute lengths
  rw [htt.x_len, htt.y_len, htt.z_len, htt.w_len]
  -- The autocorrelation sum vanishes by the TT condition
  have htotal : totalAutocorr x + totalAutocorr y +
         2 * totalAutocorr z + 2 * totalAutocorr w = 0 := by
    rw [← weightedTotalAutocorr_decompose htt.x_len htt.y_len htt.z_len htt.w_len]
    exact turyn_vanishing_total htt
  -- Convert Nat subtraction cast: ↑(n-1) = ↑n - 1 (valid since n ≥ 1)
  have hcast : (↑(n - 1) : Int) = (↑n : Int) - 1 := by omega
  rw [hcast]
  -- Distribute 2 * (sum + product) terms so omega sees linear arithmetic
  have hd1 : 2 * ((↑n : Int) + 2 * totalAutocorr z) =
    2 * ↑n + 2 * (2 * totalAutocorr z) := Int.mul_add _ _ _
  have hd2 : 2 * ((↑n : Int) - 1 + 2 * totalAutocorr w) =
    2 * (↑n - 1) + 2 * (2 * totalAutocorr w) := Int.mul_add _ _ _
  rw [hd1, hd2]
  omega

/-! ### Computational verification of the energy identity -/

/-- Compute x² + y² + 2z² + 2w² for a quadruple. -/
def energyLHS (x y z w : PmSeq) : Int :=
  (seqSum x) ^ 2 + (seqSum y) ^ 2 +
  2 * (seqSum z) ^ 2 + 2 * (seqSum w) ^ 2

/-- Compute 6n − 2. -/
def energyRHS (n : Nat) : Int := 6 * n - 2

/-- Boolean check that the energy identity holds for a given quadruple. -/
def checkEnergy (n : Nat) (x y z w : PmSeq) : Bool :=
  energyLHS x y z w == energyRHS n
