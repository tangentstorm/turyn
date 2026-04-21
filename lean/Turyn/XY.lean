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

end Turyn
