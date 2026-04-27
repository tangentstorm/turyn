import Turyn.TurynType
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open Finset
open BigOperators

/-!
# Energy Identity for Turyn-Type Sequences

For any TT(n) with sequences X, Y, Z (length n) and W (length n−1),
the sums x = Σ Xᵢ, y = Σ Yᵢ, z = Σ Zᵢ, w = Σ Wᵢ satisfy:

    x² + y² + 2z² + 2w² = 6n − 2

## Proof

The proof follows from two facts:

Fact 1 (Sum-autocorrelation identity):
For any ±1 sequence `a` of length `k`:

    (Σᵢ aᵢ)² = k + 2 · Σ (s=1…k−1) Nₐ(s)

Proof: Expand (Σᵢ aᵢ)² = Σᵢ aᵢ² + 2·Σ (i < j) aᵢaⱼ.
Since aᵢ = ±1, we have aᵢ² = 1, so Σᵢ aᵢ² = k.
The cross terms group by lag: Σ (i < j) aᵢaⱼ = Σ (s=1…k−1) Nₐ(s).

Fact 2 (Turyn vanishing):
N_X(s) + N_Y(s) + 2·N_Z(s) + 2·N_W(s) = 0 for all s ≥ 1.

Combining:
    x² + y² + 2z² + 2w²
  = (n + 2·Σ N_X(s)) + (n + 2·Σ N_Y(s))
    + 2·(n + 2·Σ N_Z(s)) + 2·((n−1) + 2·Σ N_W(s))
  = (6n − 2) + 2 · 0 = 6n − 2                                □
-/

/-! ### Total autocorrelation -/

/-- Total autocorrelation: sum of N_a(s) for s = 1, …, k−1. -/
def totalAutocorr (a : List Int) : Int :=
  ∑ i ∈ range (a.length - 1), aperiodicAutocorr a (i + 1)

/-! ### Weighted total autocorrelation -/

/-- Weighted total autocorrelation for a TT quadruple. -/
def weightedTotalAutocorr (x y z w : List Int) (n : Nat) : Int :=
  ∑ i ∈ range (n - 1), combinedAutocorr x y z w (i + 1)

/-- **Turyn vanishing (total):** The weighted total autocorrelation vanishes.

This is a direct consequence of the TT vanishing condition:
each shift's combined autocorrelation is zero, so their sum is zero. -/
theorem turyn_vanishing_total {n : Nat} (T : TurynType n) :
    weightedTotalAutocorr T.X.data T.Y.data T.Z.data T.W.data n = 0 := by
  unfold weightedTotalAutocorr
  exact sum_eq_zero (fun i hi => T.vanishing (i + 1) (by omega) (by rw [mem_range] at hi; omega))

/-! ### Sum-autocorrelation identity

This is the key algebraic identity connecting sequence sums to autocorrelations:

    (Σ aᵢ)² = k + 2 · Σ_{s=1}^{k-1} N_a(s)

The proof decomposes (Σ aᵢ)² as a double sum, splitting into diagonal
(= length, since aᵢ² = 1) and off-diagonal (= 2 × total autocorrelation) parts.
-/

theorem sum_sq_expand (n : Nat) (a : Nat → Int) :
    (∑ i ∈ range n, a i) ^ 2 = (∑ i ∈ range n, a i ^ 2) + 2 * ∑ s ∈ range (n - 1), ∑ i ∈ range (n - 1 - s), a i * a (i + s + 1) := by
  induction n with
  | zero =>
    simp
  | succ k ih =>
    rw [sum_range_succ, add_sq, ih, sum_range_succ (fun i => a i ^ 2)]
    have h1 : ∑ s ∈ range k, ∑ i ∈ range (k - s), a i * a (i + s + 1) =
              ∑ s ∈ range (k - 1), ∑ i ∈ range (k - 1 - s), a i * a (i + s + 1) +
              ∑ i ∈ range k, a i * a k := by
      cases k with
      | zero => rfl
      | succ j =>
        have heq : j + 1 - 1 = j := by omega
        rw [heq, sum_range_succ]
        have h_inner : ∀ s ∈ range j, ∑ i ∈ range (j + 1 - s), a i * a (i + s + 1) =
                       ∑ i ∈ range (j - s), a i * a (i + s + 1) + a (j - s) * a (j + 1) := by
          intro s hs
          have hs_lt : s < j := mem_range.mp hs
          have eq_inner : j + 1 - s = j - s + 1 := by omega
          rw [eq_inner, sum_range_succ]
          have eq_idx : j - s + s + 1 = j + 1 := by omega
          rw [eq_idx]
        rw [sum_congr rfl h_inner, sum_add_distrib]
        have h_tail : ∑ i ∈ range (j + 1 - j), a i * a (i + j + 1) = a 0 * a (j + 1) := by
          have : j + 1 - j = 1 := by omega
          rw [this, sum_range_succ, sum_range_zero, zero_add]
          have : 0 + j + 1 = j + 1 := by omega
          rw [this]
        rw [h_tail]
        have h_sum_rev : (∑ s ∈ range j, a (j - s) * a (j + 1)) + a 0 * a (j + 1) = ∑ i ∈ range (j + 1), a i * a (j + 1) := by
          have h0 : a 0 = a (j - j) := by rw [Nat.sub_self]
          rw [h0]
          have hlhs : (∑ s ∈ range j, a (j - s) * a (j + 1)) + a (j - j) * a (j + 1) = ∑ s ∈ range (j + 1), a (j - s) * a (j + 1) := by
            exact (sum_range_succ (fun s => a (j - s) * a (j + 1)) j).symm
          rw [hlhs]
          have hrefl := sum_range_reflect (fun s => a s * a (j + 1)) (j + 1)
          have h_idx : ∀ s ∈ range (j + 1), a (j - s) * a (j + 1) = a (j + 1 - 1 - s) * a (j + 1) := by
            intro s _
            have hj : j - s = j + 1 - 1 - s := by omega
            rw [hj]
          rw [sum_congr rfl h_idx]
          exact hrefl
        rw [add_assoc, h_sum_rev]
    have hk_minus : k + 1 - 1 = k := by omega
    rw [hk_minus, h1]
    have h_final : (2 * ∑ i ∈ range k, a i) * a k = 2 * ∑ i ∈ range k, a i * a k := by
      calc
        (2 * ∑ i ∈ range k, a i) * a k = 2 * ((∑ i ∈ range k, a i) * a k) := by ring
        _ = 2 * ∑ i ∈ range k, a i * a k := by rw [sum_mul]
    rw [h_final]
    ring

theorem sum_w_ext {n : Nat} {w : List Int} (hwl : w.length = n - 1) :
    ∑ i ∈ range (n - 1), aperiodicAutocorr w (i + 1) =
    ∑ i ∈ range (n - 1 - 1), aperiodicAutocorr w (i + 1) := by
  cases n with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ j =>
      have hw : aperiodicAutocorr w (j + 1) = 0 := by
        unfold aperiodicAutocorr
        have hlen : j + 1 ≥ w.length := by omega
        split
        · rfl
        · contradiction
      have heq1 : j + 1 + 1 - 1 = j + 1 := by omega
      rw [heq1]
      rw [sum_range_succ]
      have heq2 : j + 1 - 1 = j := by omega
      rw [heq2, hw]
      omega

theorem weightedTotalAutocorr_decompose {n : Nat} {x y z w : List Int}
    (hxl : x.length = n) (hyl : y.length = n)
    (hzl : z.length = n) (hwl : w.length = n - 1) :
    weightedTotalAutocorr x y z w n =
    totalAutocorr x + totalAutocorr y + 2 * totalAutocorr z + 2 * totalAutocorr w := by
  unfold weightedTotalAutocorr totalAutocorr combinedAutocorr
  simp only [sum_add_distrib, ← mul_sum]
  rw [hxl, hyl, hzl]
  have hw_ext := sum_w_ext hwl
  rw [hw_ext]
  rw [hwl]

theorem sum_sq_eq_finset (a : List Int) (h : AllPmOne a) :
    (∑ i ∈ range a.length, a.getD i 0) ^ 2 = (a.length : Int) + 2 * ∑ i ∈ range (a.length - 1), aperiodicAutocorr a (i + 1) := by
  have h_sq : ∀ i ∈ range a.length, (a.getD i 0) ^ 2 = 1 := by
    intro i hi
    have hi_lt : i < a.length := mem_range.mp hi
    have eq_get : a.getD i 0 = a[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_lt]
      rfl
    rw [eq_get]
    have hall := h (a[i]) (List.getElem_mem hi_lt)
    rcases hall with h1 | hm1
    · rw [h1]; rfl
    · rw [hm1]; rfl
  have h_diag : ∑ i ∈ range a.length, (a.getD i 0) ^ 2 = (a.length : Int) := by
    rw [sum_congr rfl h_sq, sum_const, card_range, nsmul_one]
  rw [sum_sq_expand a.length (fun i => a.getD i 0)]
  rw [h_diag]
  have h_cross : ∀ s ∈ range (a.length - 1),
      ∑ i ∈ range (a.length - 1 - s), a.getD i 0 * a.getD (i + s + 1) 0 =
      aperiodicAutocorr a (s + 1) := by
    intro s hs
    have hs_lt : s < a.length - 1 := mem_range.mp hs
    unfold aperiodicAutocorr
    split
    · next h_if =>
      omega
    · next =>
      have eq_sum : a.length - (s + 1) = a.length - 1 - s := by omega
      rw [eq_sum]
      apply sum_congr rfl
      intro i _
      have eq_idx : i + s + 1 = i + (s + 1) := by omega
      rw [eq_idx]
  rw [sum_congr rfl h_cross]

theorem sum_sq_eq_len_add_two_totalAutocorr (a : List Int) (h : AllPmOne a) :
    (seqSum a) ^ 2 = ↑(a.length) + 2 * totalAutocorr a := by
  rw [seqSum, totalAutocorr]
  exact sum_sq_eq_finset a h

/-- **Energy identity:** For any TT(n), the sums satisfy
    x² + y² + 2z² + 2w² = 6n − 2. -/
theorem energy_identity {n : Nat} (T : TurynType n) (hn : n ≥ 1) :
    (seqSum T.X.data) ^ 2 + (seqSum T.Y.data) ^ 2 +
    2 * (seqSum T.Z.data) ^ 2 + 2 * (seqSum T.W.data) ^ 2 =
    6 * (n : Int) - 2 := by
  rw [sum_sq_eq_len_add_two_totalAutocorr T.X.data T.X.pm,
      sum_sq_eq_len_add_two_totalAutocorr T.Y.data T.Y.pm,
      sum_sq_eq_len_add_two_totalAutocorr T.Z.data T.Z.pm,
      sum_sq_eq_len_add_two_totalAutocorr T.W.data T.W.pm]
  rw [T.X.len, T.Y.len, T.Z.len, T.W.len]
  have htotal : totalAutocorr T.X.data + totalAutocorr T.Y.data +
         2 * totalAutocorr T.Z.data + 2 * totalAutocorr T.W.data = 0 := by
    rw [← weightedTotalAutocorr_decompose T.X.len T.Y.len T.Z.len T.W.len]
    exact turyn_vanishing_total T
  have hcast : (↑(n - 1) : Int) = (↑n : Int) - 1 := by omega
  rw [hcast]
  have hd1 : 2 * ((↑n : Int) + 2 * totalAutocorr T.Z.data) =
    2 * ↑n + 2 * (2 * totalAutocorr T.Z.data) := Int.mul_add _ _ _
  have hd2 : 2 * ((↑n : Int) - 1 + 2 * totalAutocorr T.W.data) =
    2 * (↑n - 1) + 2 * (2 * totalAutocorr T.W.data) := Int.mul_add _ _ _
  rw [hd1, hd2]
  omega

/-! ### Computational verification of the energy identity -/

/-- Compute x² + y² + 2z² + 2w² for a quadruple. -/
def energyLHS (x y z w : List Int) : Int :=
  (seqSum x) ^ 2 + (seqSum y) ^ 2 +
  2 * (seqSum z) ^ 2 + 2 * (seqSum w) ^ 2

/-- Compute 6n − 2. -/
def energyRHS (n : Nat) : Int := 6 * n - 2

/-- Boolean check that the energy identity holds for a given quadruple. -/
def checkEnergy (n : Nat) (x y z w : List Int) : Bool :=
  energyLHS x y z w == energyRHS n
