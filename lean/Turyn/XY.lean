import Turyn.Equivalence

namespace Turyn

/-- Product of A and B entries at 1-indexed position `i`. -/
def uAt {n : Nat} (S : TurynTypeSeq n) (i : Nat) : Int := aAt S i * bAt S i

/-- `uAt S i` is ±1 for valid indices. -/
lemma uAt_pm {n : Nat} (S : TurynTypeSeq n) (i : Nat) (hi1 : 1 ≤ i) (hi2 : i ≤ n) :
    uAt S i = 1 ∨ uAt S i = -1 := by
  unfold uAt aAt bAt
  have hAlen := S.isTuryn.x_len
  have hBlen := S.isTuryn.y_len
  have hiA : i - 1 < S.A.length := by omega
  have hiB : i - 1 < S.B.length := by omega
  have ha := pm_entry_of_getD S.isTuryn.x_pm hiA
  have hb := pm_entry_of_getD S.isTuryn.y_pm hiB
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    · rw [ha, hb]; decide

/-- Under `Canonical1`, the first entry of `u` is 1. -/
lemma uAt_one_of_canonical1_head {n : Nat} {S : TurynTypeSeq n}
    (hc : Canonical1 n S) : uAt S 1 = 1 := by
  unfold uAt
  have ha1 := hc.1
  have hb1 := hc.2.2.1
  rw [ha1, hb1]; ring

/-- Under `Canonical1`, the last entry of `u` is 1. -/
lemma uAt_one_of_canonical1_tail {n : Nat} {S : TurynTypeSeq n}
    (_hn : 1 ≤ n) (hc : Canonical1 n S) : uAt S n = 1 := by
  unfold uAt
  have han := hc.2.1
  have hbn := hc.2.2.2.1
  rw [han, hbn]; ring

/-- `uAt S i` squares to 1 for valid indices. -/
lemma uAt_sq {n : Nat} (S : TurynTypeSeq n) (i : Nat) (hi1 : 1 ≤ i) (hi2 : i ≤ n) :
    uAt S i * uAt S i = 1 := by
  have h := uAt_pm S i hi1 hi2
  rcases h with h | h <;> rw [h] <;> ring

theorem aperiodicAutocorr_A_via_aAt {n : Nat} (S : TurynTypeSeq n) (s : Nat) (hs : s < n) :
    aperiodicAutocorr S.A s = ∑ i ∈ Finset.range (n - s), aAt S (i + 1) * aAt S (i + 1 + s) := by
  unfold aperiodicAutocorr
  rw [if_neg (by rw [S.isTuryn.x_len]; omega)]
  rw [show S.A.length - s = n - s from by rw [S.isTuryn.x_len]]
  apply Finset.sum_congr rfl
  intro i _
  unfold aAt
  simp

theorem aperiodicAutocorr_B_via_aAt {n : Nat} (S : TurynTypeSeq n) (s : Nat) (hs : s < n) :
    aperiodicAutocorr S.B s = ∑ i ∈ Finset.range (n - s), bAt S (i + 1) * bAt S (i + 1 + s) := by
  unfold aperiodicAutocorr
  rw [if_neg (by rw [S.isTuryn.y_len]; omega)]
  rw [show S.B.length - s = n - s from by rw [S.isTuryn.y_len]]
  apply Finset.sum_congr rfl
  intro i _
  unfold bAt
  simp

lemma aAt_sq {n : Nat} (S : TurynTypeSeq n) (i : Nat) (hi1 : 1 ≤ i) (hi2 : i ≤ n) :
    aAt S i * aAt S i = 1 := by
      -- Apply the lemma that states the product of a number with itself is 1 if the number is either 1 or -1.
      have h_sq : aAt S i = 1 ∨ aAt S i = -1 := by
        apply pm_entry_of_getD; exact S.isTuryn.x_pm; exact (by
        rw [ S.isTuryn.x_len ] ; omega)
      exact h_sq.elim (fun h => by rw [h]; norm_num) (fun h => by rw [h]; norm_num)

lemma bAt_eq_aAt_mul_uAt {n : Nat} (S : TurynTypeSeq n) (i : Nat)
    (hi1 : 1 ≤ i) (hi2 : i ≤ n) :
    bAt S i = aAt S i * uAt S i := by
      unfold uAt;
      rw [ ← mul_assoc, aAt_sq S i hi1 hi2, one_mul ]

private lemma summand_identity {n : Nat} (S : TurynTypeSeq n) (i : Nat)
    (hi1 : 1 ≤ i) (hi2 : i ≤ n) (j : Nat) (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    aAt S i * aAt S j + bAt S i * bAt S j =
    aAt S i * aAt S j * (1 + uAt S i * uAt S j) := by
      -- Apply the lemma to rewrite the bAt terms in the LHS.
      have h_lhs_rewrite : aAt S i * aAt S j + bAt S i * bAt S j = aAt S i * aAt S j + (aAt S i * aAt S j) * (aAt S i * aAt S i) * (uAt S i * uAt S j) := by
        rw [ bAt_eq_aAt_mul_uAt, bAt_eq_aAt_mul_uAt ];
        · rw [ show aAt S i * aAt S i = 1 by exact aAt_sq S i hi1 hi2 ] ; ring;
        · linarith;
        · lia;
        · linarith;
        · linarith;
      rw [ h_lhs_rewrite, aAt_sq S i hi1 hi2 ] ; ring

theorem T_k_as_U_sum {n : Nat} (S : TurynTypeSeq n) (k : Nat) (hk : 2 ≤ k) (hkn : k ≤ n - 1) :
    aperiodicAutocorr S.A (n - k) + aperiodicAutocorr S.B (n - k) =
    ∑ i ∈ Finset.range k,
      aAt S (i + 1) * aAt S (i + 1 + (n - k)) * (1 + uAt S (i + 1) * uAt S (i + 1 + (n - k))) := by
        have h1 : aperiodicAutocorr S.A (n - k) = ∑ i ∈ Finset.range k, aAt S (i + 1) * aAt S (i + 1 + (n - k)) := by
          convert aperiodicAutocorr_A_via_aAt S ( n - k ) _ using 1;
          · rw [ Nat.sub_sub_self ( by omega ) ];
          · omega
        have h2 : aperiodicAutocorr S.B (n - k) = ∑ i ∈ Finset.range k, bAt S (i + 1) * bAt S (i + 1 + (n - k)) := by
          convert aperiodicAutocorr_B_via_aAt S ( n - k ) _ using 1;
          · rw [ Nat.sub_sub_self ( by omega ) ];
          · omega;
        rw [ h1, h2, ← Finset.sum_add_distrib ];
        -- Apply the summand_identity to each term in the sum.
        apply Finset.sum_congr rfl
        intro i hi
        apply summand_identity;
        · linarith;
        · linarith [ Finset.mem_range.mp hi, Nat.sub_add_cancel ( show 1 ≤ n from by omega ) ];
        · omega;
        · linarith [ Finset.mem_range.mp hi, Nat.sub_add_cancel ( show k ≤ n from hkn.trans ( Nat.pred_le _ ) ) ]

end Turyn
