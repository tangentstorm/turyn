import Turyn.Step3
import Turyn.GoethalsSeidel

namespace Turyn

/-- Convert a length-`n` list into a typed vector on `Fin n`. -/
def listToIntVec {n : Nat} (xs : List Int) (hxs : xs.length = n) : IntVec n :=
  fun i => xs.getD i.1 0

@[simp] theorem listToIntVec_apply {n : Nat} (xs : List Int) (hxs : xs.length = n) (i : Fin n) :
    listToIntVec xs hxs i = xs.getD i.1 0 := rfl

/-- Convert a typed matrix row into a concrete list. -/
def matrixRow {n : Nat} (M : IntMat n) (i : Fin n) : List Int :=
  List.ofFn fun j : Fin n => M i j

@[simp] theorem matrixRow_length {n : Nat} (M : IntMat n) (i : Fin n) :
    (matrixRow M i).length = n := by
  simp [matrixRow]

lemma matrixRow_getD {n : Nat} (M : IntMat n) (i : Fin n) {j : Nat} (hj : j < n) :
    (matrixRow M i).getD j 0 = M i ⟨j, hj⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa [matrixRow] using hj)]
  simp [matrixRow]

lemma matrixRow_dot_eq_mul_transpose {n : Nat} (M : IntMat n) (i j : Fin n) :
    listDotProduct (matrixRow M i) (matrixRow M j) = (M * Matrix.transpose M) i j := by
  rw [listDotProduct_eq_sum (by simp [matrixRow]), matrixRow_length, Matrix.mul_apply]
  trans ∑ k ∈ Finset.range n, if hk : k < n then M i ⟨k, hk⟩ * M j ⟨k, hk⟩ else 0
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    rw [matrixRow_getD M i hk', matrixRow_getD M j hk']
    simp [hk']
  · simpa [Matrix.transpose_apply] using
      (Fin.sum_univ_eq_sum_range (n := n)
        (f := fun k : Nat => if hk : k < n then M i ⟨k, hk⟩ * M j ⟨k, hk⟩ else 0)).symm

lemma circulant_list_entry {n : Nat} (xs : List Int) (hxs : xs.length = n) (i j : Fin n) :
    circulant (listToIntVec xs hxs) i j = (circulantRow n xs i.1).getD j.1 0 := by
  rw [circulant_apply, listToIntVec_apply, circulantRow_getD (x := xs) (r := i.1) (hc := j.2)]
  rw [Fin.sub_def]
  have hi : i.1 ≤ n := Nat.le_of_lt i.2
  have hidx : (n - i.1 + j.1) % n = (j.1 + n - i.1) % n := by
    rw [Nat.add_sub_assoc hi]
    ac_rfl
  simp [hidx]

lemma circulant_mul_reversal_list_entry {n : Nat} (xs : List Int) (hxs : xs.length = n)
    (i j : Fin n) :
    (circulant (listToIntVec xs hxs) * reversalMatrix n) i j =
      (applyR (circulantRow n xs i.1)).getD j.1 0 := by
  rw [mul_reversalMatrix_apply, circulant_list_entry]
  rw [applyR_getD (row := circulantRow n xs i.1) (hk := by simpa [circulantRow] using j.2)]
  simp [revFin, circulantRow]

lemma trCirculant_list_entry {n : Nat} (xs : List Int) (hxs : xs.length = n) (i j : Fin n) :
    trCirculant (listToIntVec xs hxs) i j = (trRow (m := n) xs i.1).getD j.1 0 := by
  unfold trCirculant
  rw [mul_reversalMatrix_apply, circulant_transpose_apply, listToIntVec_apply]
  rw [trRow_getD (x := xs) (r := i.1) (hk := j.2)]
  rw [Fin.sub_def]
  have hj' : n - 1 - j.1 < n := by omega
  have hi' : n - 1 - i.1 < n := by omega
  have hleft : n - (n - 1 - j.1) = j.1 + 1 := by omega
  have hright' : j.1 + n - (n - 1 - i.1) = j.1 + (i.1 + 1) := by omega
  have hidx : (n - (n - 1 - j.1) + i.1) % n = (j.1 + n - (n - 1 - i.1)) % n := by
    rw [hleft]
    rw [hright']
    ac_rfl
  simp [revFin, hidx]

lemma neg_circulant_mul_reversal_list_entry {n : Nat} (xs : List Int) (hxs : xs.length = n)
    (i j : Fin n) :
    (-(circulant (listToIntVec xs hxs) * reversalMatrix n)) i j =
      (negRow (applyR (circulantRow n xs i.1))).getD j.1 0 := by
  have h := congrArg Neg.neg (circulant_mul_reversal_list_entry xs hxs i j)
  simpa [negRow] using h

lemma neg_trCirculant_list_entry {n : Nat} (xs : List Int) (hxs : xs.length = n) (i j : Fin n) :
    (-trCirculant (listToIntVec xs hxs)) i j =
      (negRow (trRow (m := n) xs i.1)).getD j.1 0 := by
  have h := congrArg Neg.neg (trCirculant_list_entry xs hxs i j)
  simpa [negRow] using h

lemma typed_periodicAutocorr_eq_list {n : Nat} (xs : List Int) (hxs : xs.length = n) (s : Fin n) :
    Turyn.periodicAutocorr (listToIntVec xs hxs) s = _root_.periodicAutocorr xs s.1 := by
  by_cases hn : n = 0
  · subst hn
    exact (Nat.not_lt_zero _ s.2).elim
  · rw [_root_.periodicAutocorr_eq_sum_of_length (a := xs) (m := n) (s := s.1) hxs hn]
    unfold Turyn.periodicAutocorr
    change
      ∑ i : Fin n, xs.getD i.1 0 * xs.getD ((i.1 + s.1) % n) 0 =
        ∑ i ∈ Finset.range n, xs.getD i 0 * xs.getD ((i + s.1) % n) 0
    simpa [listToIntVec] using
      (Fin.sum_univ_eq_sum_range (n := n)
        (f := fun i : Nat => xs.getD i 0 * xs.getD ((i + s.1) % n) 0))

lemma typed_combinedPeriodic_eq_list {m : Nat} (Q : GSSequenceQuad m) (s : Fin m) :
    Turyn.periodicAutocorr (listToIntVec Q.x1 Q.x1_len) s +
      Turyn.periodicAutocorr (listToIntVec Q.x2 Q.x2_len) s +
      Turyn.periodicAutocorr (listToIntVec Q.x3 Q.x3_len) s +
      Turyn.periodicAutocorr (listToIntVec Q.x4 Q.x4_len) s =
      _root_.combinedPeriodicAutocorr Q.x1 Q.x2 Q.x3 Q.x4 s.1 := by
  unfold _root_.combinedPeriodicAutocorr
  rw [typed_periodicAutocorr_eq_list Q.x1 Q.x1_len s,
      typed_periodicAutocorr_eq_list Q.x2 Q.x2_len s,
      typed_periodicAutocorr_eq_list Q.x3 Q.x3_len s,
      typed_periodicAutocorr_eq_list Q.x4 Q.x4_len s]

/-- Turn the standalone `GSSequenceQuad` data into certified typed GS input. -/
def gsDataOfQuad {m : Nat} (Q : GSSequenceQuad m) : CertifiedGSData m :=
  { x1 := listToIntVec Q.x1 Q.x1_len
    x2 := listToIntVec Q.x2 Q.x2_len
    x3 := listToIntVec Q.x3 Q.x3_len
    x4 := listToIntVec Q.x4 Q.x4_len
    x1_pm := by
      intro i
      simpa [listToIntVec] using Q.x1_pm i.1 i.2
    x2_pm := by
      intro i
      simpa [listToIntVec] using Q.x2_pm i.1 i.2
    x3_pm := by
      intro i
      simpa [listToIntVec] using Q.x3_pm i.1 i.2
    x4_pm := by
      intro i
      simpa [listToIntVec] using Q.x4_pm i.1 i.2
    periodic_vanishing := by
      intro s hs
      have hs1 : 1 ≤ s.1 := by
        omega
      have hslt : s.1 < m := s.2
      change
        Turyn.periodicAutocorr (listToIntVec Q.x1 Q.x1_len) s +
          Turyn.periodicAutocorr (listToIntVec Q.x2 Q.x2_len) s +
          Turyn.periodicAutocorr (listToIntVec Q.x3 Q.x3_len) s +
          Turyn.periodicAutocorr (listToIntVec Q.x4 Q.x4_len) s = 0
      rw [typed_combinedPeriodic_eq_list Q s]
      simpa
        using Q.periodic_vanishing s.1 hs1 hslt }

/-- Typed GS input extracted from a T-sequence. -/
def gsDataOfTSequence {m : Nat} (T : TSequence m) : CertifiedGSData m :=
  gsDataOfQuad (gsSequenceQuadOfTSequence T)

/-- The typed GS matrix attached to a T-sequence. -/
def typedGsMatrixOfTSequence {m : Nat} (T : TSequence m) : IntMat (4 * m) :=
  gsMatrix (gsDataOfTSequence T).toGSData

lemma step3GsRow_length {m : Nat} (T : TSequence m) (i : Fin (4 * m)) :
    ((gsMatrixOfTSequence T).rows.getD i.1 []).length = 4 * m := by
  have h_row_length :
      ∀ (L : List (List Int)), allRowsLength L (4 * m) = true →
        ∀ (k : Nat), k < L.length → List.length (L.getD k []) = 4 * m := by
    intro L hL k hk
    have := hL
    simp_all +decide [allRowsLength]
  exact h_row_length _ (gsMatrixOfTSequence_allRowsLength T) _ (by
    simpa [gsMatrixOfTSequence_dim] using i.2)

private lemma gsRow0_getD_block0 {m : Nat} (x1 x2 x3 x4 : List Int) {i j : Nat}
    (hj : j < m) :
    (gsRow0 (m := m) x1 x2 x3 x4 i).getD j 0 =
      (circulantRow m x1 i).getD j 0 := by
  rw [gsRow0]
  rw [List.getD_eq_getElem?_getD]
  simp [List.getElem?_append, hj]

private lemma gsRow0_getD_block1 {m : Nat} (x1 x2 x3 x4 : List Int) {i j : Nat}
    (hj1 : m ≤ j) (hj2 : j < 2 * m) :
    (gsRow0 (m := m) x1 x2 x3 x4 i).getD j 0 =
      (applyR (circulantRow m x2 i)).getD (j - m) 0 := by
  rw [gsRow0]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  have hnot : ¬ j < m := Nat.not_lt.mpr hj1
  have hmid : j - m < m := by omega
  simp [List.getElem?_append, hnot, hmid, applyR_length, circulantRow]

private lemma gsRow0_getD_block2 {m : Nat} (x1 x2 x3 x4 : List Int) {i j : Nat}
    (hj1 : 2 * m ≤ j) (hj2 : j < 3 * m) :
    (gsRow0 (m := m) x1 x2 x3 x4 i).getD j 0 =
      (applyR (circulantRow m x3 i)).getD (j - 2 * m) 0 := by
  rw [gsRow0]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  have hnot1 : ¬ j < m := by omega
  have hnot2 : ¬ j - m < m := by omega
  have hthird : j - m - m < m := by omega
  have hthird' : j - 2 * m < m := by omega
  have hidx : j - m - m = j - 2 * m := by omega
  simp [List.getElem?_append, hnot1, hnot2, hthird, hthird', hidx, applyR_length, circulantRow]

private lemma gsRow0_getD_block3 {m : Nat} (x1 x2 x3 x4 : List Int) {i j : Nat}
    (hj1 : 3 * m ≤ j) (hj2 : j < 4 * m) :
    (gsRow0 (m := m) x1 x2 x3 x4 i).getD j 0 =
      (applyR (circulantRow m x4 i)).getD (j - 3 * m) 0 := by
  rw [gsRow0]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  have hnot1 : ¬ j < m := by omega
  have hnot2 : ¬ j - m < m := by omega
  have hnot3 : ¬ j - 2 * m < m := by omega
  have hnot3' : ¬ j - m - m < m := by omega
  have hfourth : j - 3 * m < m := by omega
  have hidx : j - m - m - m = j - 3 * m := by omega
  simp [List.getElem?_append, hnot1, hnot2, hnot3, hnot3', hfourth, hidx,
    applyR_length, circulantRow]

private lemma gsRow1_getD_block0 {m : Nat} (x1 x2 x3 x4 : List Int) {i j : Nat}
    (hj : j < m) :
    (gsRow1 (m := m) x1 x2 x3 x4 i).getD j 0 =
      (negRow (applyR (circulantRow m x2 i))).getD j 0 := by
  rw [gsRow1]
  rw [List.getD_eq_getElem?_getD]
  simp [List.getElem?_append, hj]

private lemma gsRow1_getD_block1 {m : Nat} (x1 x2 x3 x4 : List Int) {i j : Nat}
    (hj1 : m ≤ j) (hj2 : j < 2 * m) :
    (gsRow1 (m := m) x1 x2 x3 x4 i).getD j 0 =
      (circulantRow m x1 i).getD (j - m) 0 := by
  rw [gsRow1]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  have hnot : ¬ j < m := Nat.not_lt.mpr hj1
  have hmid : j - m < m := by omega
  simp [List.getElem?_append, hnot, hmid, applyR_length, circulantRow, trRow]

private lemma gsRow1_getD_block2 {m : Nat} (x1 x2 x3 x4 : List Int) {i j : Nat}
    (hj1 : 2 * m ≤ j) (hj2 : j < 3 * m) :
    (gsRow1 (m := m) x1 x2 x3 x4 i).getD j 0 =
      (trRow (m := m) x4 i).getD (j - 2 * m) 0 := by
  rw [gsRow1]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  have hnot1 : ¬ j < m := by omega
  have hnot2 : ¬ j - m < m := by omega
  have hthird : j - m - m < m := by omega
  have hthird' : j - 2 * m < m := by omega
  have hidx : j - m - m = j - 2 * m := by omega
  simp [List.getElem?_append, hnot1, hnot2, hthird, hthird', hidx, applyR_length,
    circulantRow, trRow]

private lemma gsRow1_getD_block3 {m : Nat} (x1 x2 x3 x4 : List Int) {i j : Nat}
    (hj1 : 3 * m ≤ j) (hj2 : j < 4 * m) :
    (gsRow1 (m := m) x1 x2 x3 x4 i).getD j 0 =
      (negRow (trRow (m := m) x3 i)).getD (j - 3 * m) 0 := by
  rw [gsRow1]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  have hnot1 : ¬ j < m := by omega
  have hnot2 : ¬ j - m < m := by omega
  have hnot3 : ¬ j - 2 * m < m := by omega
  have hnot3' : ¬ j - m - m < m := by omega
  have hfourth : j - 3 * m < m := by omega
  have hidx : j - m - m - m = j - 3 * m := by omega
  simp [List.getElem?_append, hnot1, hnot2, hnot3, hnot3', hfourth, hidx,
    applyR_length, circulantRow, trRow]

private lemma gsRow2_getD_block0 {m : Nat} (x1 x2 x3 x4 : List Int) {i j : Nat}
    (hj : j < m) :
    (gsRow2 (m := m) x1 x2 x3 x4 i).getD j 0 =
      (negRow (applyR (circulantRow m x3 i))).getD j 0 := by
  rw [gsRow2]
  rw [List.getD_eq_getElem?_getD]
  simp [List.getElem?_append, hj]

private lemma gsRow2_getD_block1 {m : Nat} (x1 x2 x3 x4 : List Int) {i j : Nat}
    (hj1 : m ≤ j) (hj2 : j < 2 * m) :
    (gsRow2 (m := m) x1 x2 x3 x4 i).getD j 0 =
      (negRow (trRow (m := m) x4 i)).getD (j - m) 0 := by
  rw [gsRow2]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  have hnot : ¬ j < m := Nat.not_lt.mpr hj1
  have hmid : j - m < m := by omega
  simp [List.getElem?_append, hnot, hmid, applyR_length, circulantRow, trRow]

private lemma gsRow2_getD_block2 {m : Nat} (x1 x2 x3 x4 : List Int) {i j : Nat}
    (hj1 : 2 * m ≤ j) (hj2 : j < 3 * m) :
    (gsRow2 (m := m) x1 x2 x3 x4 i).getD j 0 =
      (circulantRow m x1 i).getD (j - 2 * m) 0 := by
  rw [gsRow2]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  have hnot1 : ¬ j < m := by omega
  have hnot2 : ¬ j - m < m := by omega
  have hthird : j - m - m < m := by omega
  have hthird' : j - 2 * m < m := by omega
  have hidx : j - m - m = j - 2 * m := by omega
  simp [List.getElem?_append, hnot1, hnot2, hthird, hthird', hidx, applyR_length,
    circulantRow, trRow]

private lemma gsRow2_getD_block3 {m : Nat} (x1 x2 x3 x4 : List Int) {i j : Nat}
    (hj1 : 3 * m ≤ j) (hj2 : j < 4 * m) :
    (gsRow2 (m := m) x1 x2 x3 x4 i).getD j 0 =
      (trRow (m := m) x2 i).getD (j - 3 * m) 0 := by
  rw [gsRow2]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  have hnot1 : ¬ j < m := by omega
  have hnot2 : ¬ j - m < m := by omega
  have hnot3 : ¬ j - 2 * m < m := by omega
  have hnot3' : ¬ j - m - m < m := by omega
  have hfourth : j - 3 * m < m := by omega
  have hidx : j - m - m - m = j - 3 * m := by omega
  simp [List.getElem?_append, hnot1, hnot2, hnot3, hnot3', hfourth, hidx,
    applyR_length, circulantRow, trRow]

private lemma gsRow3_getD_block0 {m : Nat} (x1 x2 x3 x4 : List Int) {i j : Nat}
    (hj : j < m) :
    (gsRow3 (m := m) x1 x2 x3 x4 i).getD j 0 =
      (negRow (applyR (circulantRow m x4 i))).getD j 0 := by
  rw [gsRow3]
  rw [List.getD_eq_getElem?_getD]
  simp [List.getElem?_append, hj]

private lemma gsRow3_getD_block1 {m : Nat} (x1 x2 x3 x4 : List Int) {i j : Nat}
    (hj1 : m ≤ j) (hj2 : j < 2 * m) :
    (gsRow3 (m := m) x1 x2 x3 x4 i).getD j 0 =
      (trRow (m := m) x3 i).getD (j - m) 0 := by
  rw [gsRow3]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  have hnot : ¬ j < m := Nat.not_lt.mpr hj1
  have hmid : j - m < m := by omega
  simp [List.getElem?_append, hnot, hmid, applyR_length, circulantRow, trRow]

private lemma gsRow3_getD_block2 {m : Nat} (x1 x2 x3 x4 : List Int) {i j : Nat}
    (hj1 : 2 * m ≤ j) (hj2 : j < 3 * m) :
    (gsRow3 (m := m) x1 x2 x3 x4 i).getD j 0 =
      (negRow (trRow (m := m) x2 i)).getD (j - 2 * m) 0 := by
  rw [gsRow3]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  have hnot1 : ¬ j < m := by omega
  have hnot2 : ¬ j - m < m := by omega
  have hthird : j - m - m < m := by omega
  have hthird' : j - 2 * m < m := by omega
  have hidx : j - m - m = j - 2 * m := by omega
  simp [List.getElem?_append, hnot1, hnot2, hthird, hthird', hidx, applyR_length,
    circulantRow, trRow]

private lemma gsRow3_getD_block3 {m : Nat} (x1 x2 x3 x4 : List Int) {i j : Nat}
    (hj1 : 3 * m ≤ j) (hj2 : j < 4 * m) :
    (gsRow3 (m := m) x1 x2 x3 x4 i).getD j 0 =
      (circulantRow m x1 i).getD (j - 3 * m) 0 := by
  rw [gsRow3]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  have hnot1 : ¬ j < m := by omega
  have hnot2 : ¬ j - m < m := by omega
  have hnot3 : ¬ j - 2 * m < m := by omega
  have hnot3' : ¬ j - m - m < m := by omega
  have hfourth : j - 3 * m < m := by omega
  have hidx : j - m - m - m = j - 3 * m := by omega
  simp [List.getElem?_append, hnot1, hnot2, hnot3, hnot3', hfourth, hidx,
    applyR_length, circulantRow, trRow]

private lemma mod_eq_self_of_div_eq_zero {m j : Nat} (hm : m ≠ 0) (hdiv : j / m = 0) :
    j % m = j := by
  have h := Nat.mod_add_div j m
  rw [hdiv, Nat.mul_zero, Nat.add_zero] at h
  exact h

private lemma mod_eq_sub_of_div_eq_one {m j : Nat} (hdiv : j / m = 1) :
    j % m = j - m := by
  have h := Nat.mod_add_div j m
  rw [hdiv, Nat.mul_one] at h
  omega

private lemma mod_eq_sub_two_mul_of_div_eq_two {m j : Nat} (hdiv : j / m = 2) :
    j % m = j - 2 * m := by
  have h := Nat.mod_add_div j m
  rw [hdiv] at h
  omega

private lemma mod_eq_sub_three_mul_of_div_eq_three {m j : Nat} (hdiv : j / m = 3) :
    j % m = j - 3 * m := by
  have h := Nat.mod_add_div j m
  rw [hdiv] at h
  omega

private lemma div_eq_one_of_block1 {m j : Nat} (hm : 0 < m) (hj1 : m ≤ j) (hj2 : j < 2 * m) :
    j / m = 1 := by
  have hlow : 1 ≤ j / m := by
    have hmul : 1 * m ≤ j := by simpa using hj1
    exact (Nat.le_div_iff_mul_le hm).2 hmul
  have hhigh : j / m < 2 := by
    exact (Nat.div_lt_iff_lt_mul hm).2 hj2
  omega

private lemma div_eq_two_of_block2 {m j : Nat} (hm : 0 < m) (hj1 : 2 * m ≤ j) (hj2 : j < 3 * m) :
    j / m = 2 := by
  have hlow : 2 ≤ j / m := by
    simpa [two_mul] using (Nat.le_div_iff_mul_le hm).2 hj1
  have hhigh : j / m < 3 := by
    exact (Nat.div_lt_iff_lt_mul hm).2 hj2
  omega

private lemma div_eq_three_of_block3 {m j : Nat} (hm : 0 < m) (hj1 : 3 * m ≤ j) (hj2 : j < 4 * m) :
    j / m = 3 := by
  have hlow : 3 ≤ j / m := by
    simpa using (Nat.le_div_iff_mul_le hm).2 hj1
  have hhigh : j / m < 4 := by
    exact (Nat.div_lt_iff_lt_mul hm).2 hj2
  omega

private lemma lt_of_div_eq_zero {m j : Nat} (hm : m ≠ 0) (hdiv : j / m = 0) :
    j < m := by
  rcases (Nat.div_eq_zero_iff).mp hdiv with h | h
  · contradiction
  · exact h

private lemma block1_bounds_of_div_eq_one {m j : Nat} (hm : 0 < m) (hdiv : j / m = 1) :
    m ≤ j ∧ j < 2 * m := by
  have hlow : 1 ≤ j / m := by simpa [hdiv]
  have hj1 : 1 * m ≤ j := (Nat.le_div_iff_mul_le hm).mp hlow
  have hhigh : j / m < 2 := by simpa [hdiv]
  have hj2 : j < 2 * m := (Nat.div_lt_iff_lt_mul hm).mp hhigh
  simpa [one_mul] using And.intro hj1 hj2

private lemma block2_bounds_of_div_eq_two {m j : Nat} (hm : 0 < m) (hdiv : j / m = 2) :
    2 * m ≤ j ∧ j < 3 * m := by
  have hlow : 2 ≤ j / m := by simpa [hdiv]
  have hj1 : 2 * m ≤ j := (Nat.le_div_iff_mul_le hm).mp hlow
  have hhigh : j / m < 3 := by simpa [hdiv]
  have hj2 : j < 3 * m := (Nat.div_lt_iff_lt_mul hm).mp hhigh
  exact And.intro hj1 hj2

private lemma block3_bounds_of_div_eq_three {m j : Nat} (hm : 0 < m) (hdiv : j / m = 3) :
    3 * m ≤ j ∧ j < 4 * m := by
  have hlow : 3 ≤ j / m := by simpa [hdiv]
  have hj1 : 3 * m ≤ j := (Nat.le_div_iff_mul_le hm).mp hlow
  have hhigh : j / m < 4 := by simpa [hdiv]
  have hj2 : j < 4 * m := (Nat.div_lt_iff_lt_mul hm).mp hhigh
  exact And.intro hj1 hj2

private lemma typedGsMatrix_row0_block0 {m : Nat} (T : TSequence m)
    (i j : Fin (4 * m)) (hi0 : i.1 < m) (hj0 : j.1 < m) :
    typedGsMatrixOfTSequence T i j =
      (circulantRow m (gsSequenceQuadOfTSequence T).x1 i.1).getD j.1 0 := by
  let Q := gsSequenceQuadOfTSequence T
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hi0
  have hdi : i.1 / m = 0 := Nat.div_eq_of_lt hi0
  have hdj : j.1 / m = 0 := Nat.div_eq_of_lt hj0
  have hmi : i.1 % m = i.1 := mod_eq_self_of_div_eq_zero hm0 hdi
  have hmj : j.1 % m = j.1 := mod_eq_self_of_div_eq_zero hm0 hdj
  let ii : Fin m := ⟨i.1, hi0⟩
  let jj : Fin m := ⟨j.1, hj0⟩
  simpa [typedGsMatrixOfTSequence, gsDataOfTSequence, gsDataOfQuad, Q,
    gsMatrix, gsMatrixEntry, gsA, gsB, gsC, gsD, hdi, hdj, hmi, hmj, ii, jj]
    using circulant_list_entry Q.x1 Q.x1_len ii jj

private lemma typedGsMatrix_row0_block1 {m : Nat} (T : TSequence m)
    (i j : Fin (4 * m)) (hi0 : i.1 < m) (hj1 : m ≤ j.1) (hj2 : j.1 < 2 * m) :
    typedGsMatrixOfTSequence T i j =
      (applyR (circulantRow m (gsSequenceQuadOfTSequence T).x2 i.1)).getD (j.1 - m) 0 := by
  let Q := gsSequenceQuadOfTSequence T
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hi0
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hdi : i.1 / m = 0 := Nat.div_eq_of_lt hi0
  have hdj : j.1 / m = 1 := div_eq_one_of_block1 hmpos hj1 hj2
  have hmi : i.1 % m = i.1 := mod_eq_self_of_div_eq_zero hm0 hdi
  have hmj : j.1 % m = j.1 - m := mod_eq_sub_of_div_eq_one hdj
  let ii : Fin m := ⟨i.1, hi0⟩
  let jj : Fin m := ⟨j.1 - m, by omega⟩
  simpa [typedGsMatrixOfTSequence, gsDataOfTSequence, gsDataOfQuad, Q,
    gsMatrix, gsMatrixEntry, gsA, gsB, gsC, gsD, hdi, hdj, hmi, hmj, ii, jj]
    using circulant_mul_reversal_list_entry Q.x2 Q.x2_len ii jj

private lemma typedGsMatrix_row0_block2 {m : Nat} (T : TSequence m)
    (i j : Fin (4 * m)) (hi0 : i.1 < m) (hj1 : 2 * m ≤ j.1) (hj2 : j.1 < 3 * m) :
    typedGsMatrixOfTSequence T i j =
      (applyR (circulantRow m (gsSequenceQuadOfTSequence T).x3 i.1)).getD (j.1 - 2 * m) 0 := by
  let Q := gsSequenceQuadOfTSequence T
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hi0
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hdi : i.1 / m = 0 := Nat.div_eq_of_lt hi0
  have hdj : j.1 / m = 2 := div_eq_two_of_block2 hmpos hj1 hj2
  have hmi : i.1 % m = i.1 := mod_eq_self_of_div_eq_zero hm0 hdi
  have hmj : j.1 % m = j.1 - 2 * m := mod_eq_sub_two_mul_of_div_eq_two hdj
  let ii : Fin m := ⟨i.1, hi0⟩
  let jj : Fin m := ⟨j.1 - 2 * m, by omega⟩
  simpa [typedGsMatrixOfTSequence, gsDataOfTSequence, gsDataOfQuad, Q,
    gsMatrix, gsMatrixEntry, gsA, gsB, gsC, gsD, hdi, hdj, hmi, hmj, ii, jj]
    using circulant_mul_reversal_list_entry Q.x3 Q.x3_len ii jj

private lemma typedGsMatrix_row0_block3 {m : Nat} (T : TSequence m)
    (i j : Fin (4 * m)) (hi0 : i.1 < m) (hj1 : 3 * m ≤ j.1) (hj2 : j.1 < 4 * m) :
    typedGsMatrixOfTSequence T i j =
      (applyR (circulantRow m (gsSequenceQuadOfTSequence T).x4 i.1)).getD (j.1 - 3 * m) 0 := by
  let Q := gsSequenceQuadOfTSequence T
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hi0
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hdi : i.1 / m = 0 := Nat.div_eq_of_lt hi0
  have hdj : j.1 / m = 3 := div_eq_three_of_block3 hmpos hj1 hj2
  have hmi : i.1 % m = i.1 := mod_eq_self_of_div_eq_zero hm0 hdi
  have hmj : j.1 % m = j.1 - 3 * m := mod_eq_sub_three_mul_of_div_eq_three hdj
  let ii : Fin m := ⟨i.1, hi0⟩
  let jj : Fin m := ⟨j.1 - 3 * m, by omega⟩
  simpa [typedGsMatrixOfTSequence, gsDataOfTSequence, gsDataOfQuad, Q,
    gsMatrix, gsMatrixEntry, gsA, gsB, gsC, gsD, hdi, hdj, hmi, hmj, ii, jj]
    using circulant_mul_reversal_list_entry Q.x4 Q.x4_len ii jj

private lemma typedGsMatrix_row1_block0 {m : Nat} (T : TSequence m)
    (i j : Fin (4 * m)) (hi1 : m ≤ i.1) (hi2 : i.1 < 2 * m) (hj0 : j.1 < m) :
    typedGsMatrixOfTSequence T i j =
      (negRow (applyR (circulantRow m (gsSequenceQuadOfTSequence T).x2 (i.1 - m)))).getD j.1 0 := by
  let Q := gsSequenceQuadOfTSequence T
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hi2
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hdi : i.1 / m = 1 := div_eq_one_of_block1 hmpos hi1 hi2
  have hdj : j.1 / m = 0 := Nat.div_eq_of_lt hj0
  have hmi : i.1 % m = i.1 - m := mod_eq_sub_of_div_eq_one hdi
  have hmj : j.1 % m = j.1 := mod_eq_self_of_div_eq_zero hm0 hdj
  let ii : Fin m := ⟨i.1 - m, by omega⟩
  let jj : Fin m := ⟨j.1, hj0⟩
  simpa [typedGsMatrixOfTSequence, gsDataOfTSequence, gsDataOfQuad, Q,
    gsMatrix, gsMatrixEntry, gsA, gsB, gsC, gsD, hdi, hdj, hmi, hmj, ii, jj]
    using neg_circulant_mul_reversal_list_entry Q.x2 Q.x2_len ii jj

private lemma typedGsMatrix_row1_block1 {m : Nat} (T : TSequence m)
    (i j : Fin (4 * m)) (hi1 : m ≤ i.1) (hi2 : i.1 < 2 * m) (hj1 : m ≤ j.1) (hj2 : j.1 < 2 * m) :
    typedGsMatrixOfTSequence T i j =
      (circulantRow m (gsSequenceQuadOfTSequence T).x1 (i.1 - m)).getD (j.1 - m) 0 := by
  let Q := gsSequenceQuadOfTSequence T
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hi2
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hdi : i.1 / m = 1 := div_eq_one_of_block1 hmpos hi1 hi2
  have hdj : j.1 / m = 1 := div_eq_one_of_block1 hmpos hj1 hj2
  have hmi : i.1 % m = i.1 - m := mod_eq_sub_of_div_eq_one hdi
  have hmj : j.1 % m = j.1 - m := mod_eq_sub_of_div_eq_one hdj
  let ii : Fin m := ⟨i.1 - m, by omega⟩
  let jj : Fin m := ⟨j.1 - m, by omega⟩
  simpa [typedGsMatrixOfTSequence, gsDataOfTSequence, gsDataOfQuad, Q,
    gsMatrix, gsMatrixEntry, gsA, gsB, gsC, gsD, hdi, hdj, hmi, hmj, ii, jj]
    using circulant_list_entry Q.x1 Q.x1_len ii jj

private lemma typedGsMatrix_row1_block2 {m : Nat} (T : TSequence m)
    (i j : Fin (4 * m)) (hi1 : m ≤ i.1) (hi2 : i.1 < 2 * m) (hj1 : 2 * m ≤ j.1) (hj2 : j.1 < 3 * m) :
    typedGsMatrixOfTSequence T i j =
      (trRow (m := m) (gsSequenceQuadOfTSequence T).x4 (i.1 - m)).getD (j.1 - 2 * m) 0 := by
  let Q := gsSequenceQuadOfTSequence T
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hi2
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hdi : i.1 / m = 1 := div_eq_one_of_block1 hmpos hi1 hi2
  have hdj : j.1 / m = 2 := div_eq_two_of_block2 hmpos hj1 hj2
  have hmi : i.1 % m = i.1 - m := mod_eq_sub_of_div_eq_one hdi
  have hmj : j.1 % m = j.1 - 2 * m := mod_eq_sub_two_mul_of_div_eq_two hdj
  let ii : Fin m := ⟨i.1 - m, by omega⟩
  let jj : Fin m := ⟨j.1 - 2 * m, by omega⟩
  simpa [typedGsMatrixOfTSequence, gsDataOfTSequence, gsDataOfQuad, Q,
    gsMatrix, gsMatrixEntry, gsA, gsB, gsC, gsD, hdi, hdj, hmi, hmj, ii, jj]
    using trCirculant_list_entry Q.x4 Q.x4_len ii jj

private lemma typedGsMatrix_row1_block3 {m : Nat} (T : TSequence m)
    (i j : Fin (4 * m)) (hi1 : m ≤ i.1) (hi2 : i.1 < 2 * m) (hj1 : 3 * m ≤ j.1) (hj2 : j.1 < 4 * m) :
    typedGsMatrixOfTSequence T i j =
      (negRow (trRow (m := m) (gsSequenceQuadOfTSequence T).x3 (i.1 - m))).getD (j.1 - 3 * m) 0 := by
  let Q := gsSequenceQuadOfTSequence T
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hi2
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hdi : i.1 / m = 1 := div_eq_one_of_block1 hmpos hi1 hi2
  have hdj : j.1 / m = 3 := div_eq_three_of_block3 hmpos hj1 hj2
  have hmi : i.1 % m = i.1 - m := mod_eq_sub_of_div_eq_one hdi
  have hmj : j.1 % m = j.1 - 3 * m := mod_eq_sub_three_mul_of_div_eq_three hdj
  let ii : Fin m := ⟨i.1 - m, by omega⟩
  let jj : Fin m := ⟨j.1 - 3 * m, by omega⟩
  simpa [typedGsMatrixOfTSequence, gsDataOfTSequence, gsDataOfQuad, Q,
    gsMatrix, gsMatrixEntry, gsA, gsB, gsC, gsD, hdi, hdj, hmi, hmj, ii, jj]
    using neg_trCirculant_list_entry Q.x3 Q.x3_len ii jj

private lemma typedGsMatrix_row2_block0 {m : Nat} (T : TSequence m)
    (i j : Fin (4 * m)) (hi1 : 2 * m ≤ i.1) (hi2 : i.1 < 3 * m) (hj0 : j.1 < m) :
    typedGsMatrixOfTSequence T i j =
      (negRow (applyR (circulantRow m (gsSequenceQuadOfTSequence T).x3 (i.1 - 2 * m)))).getD j.1 0 := by
  let Q := gsSequenceQuadOfTSequence T
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hi2
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hdi : i.1 / m = 2 := div_eq_two_of_block2 hmpos hi1 hi2
  have hdj : j.1 / m = 0 := Nat.div_eq_of_lt hj0
  have hmi : i.1 % m = i.1 - 2 * m := mod_eq_sub_two_mul_of_div_eq_two hdi
  have hmj : j.1 % m = j.1 := mod_eq_self_of_div_eq_zero hm0 hdj
  let ii : Fin m := ⟨i.1 - 2 * m, by omega⟩
  let jj : Fin m := ⟨j.1, hj0⟩
  simpa [typedGsMatrixOfTSequence, gsDataOfTSequence, gsDataOfQuad, Q,
    gsMatrix, gsMatrixEntry, gsA, gsB, gsC, gsD, hdi, hdj, hmi, hmj, ii, jj]
    using neg_circulant_mul_reversal_list_entry Q.x3 Q.x3_len ii jj

private lemma typedGsMatrix_row2_block1 {m : Nat} (T : TSequence m)
    (i j : Fin (4 * m)) (hi1 : 2 * m ≤ i.1) (hi2 : i.1 < 3 * m) (hj1 : m ≤ j.1) (hj2 : j.1 < 2 * m) :
    typedGsMatrixOfTSequence T i j =
      (negRow (trRow (m := m) (gsSequenceQuadOfTSequence T).x4 (i.1 - 2 * m))).getD (j.1 - m) 0 := by
  let Q := gsSequenceQuadOfTSequence T
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hi2
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hdi : i.1 / m = 2 := div_eq_two_of_block2 hmpos hi1 hi2
  have hdj : j.1 / m = 1 := div_eq_one_of_block1 hmpos hj1 hj2
  have hmi : i.1 % m = i.1 - 2 * m := mod_eq_sub_two_mul_of_div_eq_two hdi
  have hmj : j.1 % m = j.1 - m := mod_eq_sub_of_div_eq_one hdj
  let ii : Fin m := ⟨i.1 - 2 * m, by omega⟩
  let jj : Fin m := ⟨j.1 - m, by omega⟩
  simpa [typedGsMatrixOfTSequence, gsDataOfTSequence, gsDataOfQuad, Q,
    gsMatrix, gsMatrixEntry, gsA, gsB, gsC, gsD, hdi, hdj, hmi, hmj, ii, jj]
    using neg_trCirculant_list_entry Q.x4 Q.x4_len ii jj

private lemma typedGsMatrix_row2_block2 {m : Nat} (T : TSequence m)
    (i j : Fin (4 * m)) (hi1 : 2 * m ≤ i.1) (hi2 : i.1 < 3 * m) (hj1 : 2 * m ≤ j.1) (hj2 : j.1 < 3 * m) :
    typedGsMatrixOfTSequence T i j =
      (circulantRow m (gsSequenceQuadOfTSequence T).x1 (i.1 - 2 * m)).getD (j.1 - 2 * m) 0 := by
  let Q := gsSequenceQuadOfTSequence T
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hi2
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hdi : i.1 / m = 2 := div_eq_two_of_block2 hmpos hi1 hi2
  have hdj : j.1 / m = 2 := div_eq_two_of_block2 hmpos hj1 hj2
  have hmi : i.1 % m = i.1 - 2 * m := mod_eq_sub_two_mul_of_div_eq_two hdi
  have hmj : j.1 % m = j.1 - 2 * m := mod_eq_sub_two_mul_of_div_eq_two hdj
  let ii : Fin m := ⟨i.1 - 2 * m, by omega⟩
  let jj : Fin m := ⟨j.1 - 2 * m, by omega⟩
  simpa [typedGsMatrixOfTSequence, gsDataOfTSequence, gsDataOfQuad, Q,
    gsMatrix, gsMatrixEntry, gsA, gsB, gsC, gsD, hdi, hdj, hmi, hmj, ii, jj]
    using circulant_list_entry Q.x1 Q.x1_len ii jj

private lemma typedGsMatrix_row2_block3 {m : Nat} (T : TSequence m)
    (i j : Fin (4 * m)) (hi1 : 2 * m ≤ i.1) (hi2 : i.1 < 3 * m) (hj1 : 3 * m ≤ j.1) (hj2 : j.1 < 4 * m) :
    typedGsMatrixOfTSequence T i j =
      (trRow (m := m) (gsSequenceQuadOfTSequence T).x2 (i.1 - 2 * m)).getD (j.1 - 3 * m) 0 := by
  let Q := gsSequenceQuadOfTSequence T
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hi2
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hdi : i.1 / m = 2 := div_eq_two_of_block2 hmpos hi1 hi2
  have hdj : j.1 / m = 3 := div_eq_three_of_block3 hmpos hj1 hj2
  have hmi : i.1 % m = i.1 - 2 * m := mod_eq_sub_two_mul_of_div_eq_two hdi
  have hmj : j.1 % m = j.1 - 3 * m := mod_eq_sub_three_mul_of_div_eq_three hdj
  let ii : Fin m := ⟨i.1 - 2 * m, by omega⟩
  let jj : Fin m := ⟨j.1 - 3 * m, by omega⟩
  simpa [typedGsMatrixOfTSequence, gsDataOfTSequence, gsDataOfQuad, Q,
    gsMatrix, gsMatrixEntry, gsA, gsB, gsC, gsD, hdi, hdj, hmi, hmj, ii, jj]
    using trCirculant_list_entry Q.x2 Q.x2_len ii jj

private lemma typedGsMatrix_row3_block0 {m : Nat} (T : TSequence m)
    (i j : Fin (4 * m)) (hi1 : 3 * m ≤ i.1) (hi2 : i.1 < 4 * m) (hj0 : j.1 < m) :
    typedGsMatrixOfTSequence T i j =
      (negRow (applyR (circulantRow m (gsSequenceQuadOfTSequence T).x4 (i.1 - 3 * m)))).getD j.1 0 := by
  let Q := gsSequenceQuadOfTSequence T
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hi2
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hdi : i.1 / m = 3 := div_eq_three_of_block3 hmpos hi1 hi2
  have hdj : j.1 / m = 0 := Nat.div_eq_of_lt hj0
  have hmi : i.1 % m = i.1 - 3 * m := mod_eq_sub_three_mul_of_div_eq_three hdi
  have hmj : j.1 % m = j.1 := mod_eq_self_of_div_eq_zero hm0 hdj
  let ii : Fin m := ⟨i.1 - 3 * m, by omega⟩
  let jj : Fin m := ⟨j.1, hj0⟩
  simpa [typedGsMatrixOfTSequence, gsDataOfTSequence, gsDataOfQuad, Q,
    gsMatrix, gsMatrixEntry, gsA, gsB, gsC, gsD, hdi, hdj, hmi, hmj, ii, jj]
    using neg_circulant_mul_reversal_list_entry Q.x4 Q.x4_len ii jj

private lemma typedGsMatrix_row3_block1 {m : Nat} (T : TSequence m)
    (i j : Fin (4 * m)) (hi1 : 3 * m ≤ i.1) (hi2 : i.1 < 4 * m) (hj1 : m ≤ j.1) (hj2 : j.1 < 2 * m) :
    typedGsMatrixOfTSequence T i j =
      (trRow (m := m) (gsSequenceQuadOfTSequence T).x3 (i.1 - 3 * m)).getD (j.1 - m) 0 := by
  let Q := gsSequenceQuadOfTSequence T
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hi2
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hdi : i.1 / m = 3 := div_eq_three_of_block3 hmpos hi1 hi2
  have hdj : j.1 / m = 1 := div_eq_one_of_block1 hmpos hj1 hj2
  have hmi : i.1 % m = i.1 - 3 * m := mod_eq_sub_three_mul_of_div_eq_three hdi
  have hmj : j.1 % m = j.1 - m := mod_eq_sub_of_div_eq_one hdj
  let ii : Fin m := ⟨i.1 - 3 * m, by omega⟩
  let jj : Fin m := ⟨j.1 - m, by omega⟩
  simpa [typedGsMatrixOfTSequence, gsDataOfTSequence, gsDataOfQuad, Q,
    gsMatrix, gsMatrixEntry, gsA, gsB, gsC, gsD, hdi, hdj, hmi, hmj, ii, jj]
    using trCirculant_list_entry Q.x3 Q.x3_len ii jj

private lemma typedGsMatrix_row3_block2 {m : Nat} (T : TSequence m)
    (i j : Fin (4 * m)) (hi1 : 3 * m ≤ i.1) (hi2 : i.1 < 4 * m) (hj1 : 2 * m ≤ j.1) (hj2 : j.1 < 3 * m) :
    typedGsMatrixOfTSequence T i j =
      (negRow (trRow (m := m) (gsSequenceQuadOfTSequence T).x2 (i.1 - 3 * m))).getD (j.1 - 2 * m) 0 := by
  let Q := gsSequenceQuadOfTSequence T
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hi2
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hdi : i.1 / m = 3 := div_eq_three_of_block3 hmpos hi1 hi2
  have hdj : j.1 / m = 2 := div_eq_two_of_block2 hmpos hj1 hj2
  have hmi : i.1 % m = i.1 - 3 * m := mod_eq_sub_three_mul_of_div_eq_three hdi
  have hmj : j.1 % m = j.1 - 2 * m := mod_eq_sub_two_mul_of_div_eq_two hdj
  let ii : Fin m := ⟨i.1 - 3 * m, by omega⟩
  let jj : Fin m := ⟨j.1 - 2 * m, by omega⟩
  simpa [typedGsMatrixOfTSequence, gsDataOfTSequence, gsDataOfQuad, Q,
    gsMatrix, gsMatrixEntry, gsA, gsB, gsC, gsD, hdi, hdj, hmi, hmj, ii, jj]
    using neg_trCirculant_list_entry Q.x2 Q.x2_len ii jj

private lemma typedGsMatrix_row3_block3 {m : Nat} (T : TSequence m)
    (i j : Fin (4 * m)) (hi1 : 3 * m ≤ i.1) (hi2 : i.1 < 4 * m) (hj1 : 3 * m ≤ j.1) (hj2 : j.1 < 4 * m) :
    typedGsMatrixOfTSequence T i j =
      (circulantRow m (gsSequenceQuadOfTSequence T).x1 (i.1 - 3 * m)).getD (j.1 - 3 * m) 0 := by
  let Q := gsSequenceQuadOfTSequence T
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hi2
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hdi : i.1 / m = 3 := div_eq_three_of_block3 hmpos hi1 hi2
  have hdj : j.1 / m = 3 := div_eq_three_of_block3 hmpos hj1 hj2
  have hmi : i.1 % m = i.1 - 3 * m := mod_eq_sub_three_mul_of_div_eq_three hdi
  have hmj : j.1 % m = j.1 - 3 * m := mod_eq_sub_three_mul_of_div_eq_three hdj
  let ii : Fin m := ⟨i.1 - 3 * m, by omega⟩
  let jj : Fin m := ⟨j.1 - 3 * m, by omega⟩
  simpa [typedGsMatrixOfTSequence, gsDataOfTSequence, gsDataOfQuad, Q,
    gsMatrix, gsMatrixEntry, gsA, gsB, gsC, gsD, hdi, hdj, hmi, hmj, ii, jj]
    using circulant_list_entry Q.x1 Q.x1_len ii jj

private lemma typedGsMatrix_entry_eq_step3_row0 {m : Nat} (T : TSequence m)
    (i j : Fin (4 * m)) (hi0 : i.1 < m) :
    typedGsMatrixOfTSequence T i j =
      ((gsMatrixOfTSequence T).rows.getD i.1 []).getD j.1 0 := by
  let Q := gsSequenceQuadOfTSequence T
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hi0
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hi : i.1 < 4 * m := by simpa using i.2
  have hdi : i.1 / m = 0 := Nat.div_eq_of_lt hi0
  have hmi : i.1 % m = i.1 := mod_eq_self_of_div_eq_zero hm0 hdi
  have hrow : (gsMatrixOfTSequence T).rows.getD i.1 [] =
      gsRow0 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i.1 % m) := by
    simpa [Q, hdi] using gsMatrixOfTSequence_getD_row T i.1 hi
  have hjlt4 : j.1 / m < 4 := by
    exact (Nat.div_lt_iff_lt_mul hmpos).2 (by simpa [Nat.mul_comm] using j.2)
  interval_cases hdj : j.1 / m
  · have hj0 : j.1 < m := lt_of_div_eq_zero hm0 hdj
    calc
      typedGsMatrixOfTSequence T i j
          = (circulantRow m Q.x1 i.1).getD j.1 0 := typedGsMatrix_row0_block0 T i j hi0 hj0
      _ = (gsRow0 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i.1 % m)).getD j.1 0 := by
            simpa [hmi] using
              (gsRow0_getD_block0 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i := i.1 % m) (j := j.1) hj0).symm
      _ = ((gsMatrixOfTSequence T).rows.getD i.1 []).getD j.1 0 := by rw [hrow]
  · rcases block1_bounds_of_div_eq_one hmpos hdj with ⟨hj1, hj2⟩
    calc
      typedGsMatrixOfTSequence T i j
          = (applyR (circulantRow m Q.x2 i.1)).getD (j.1 - m) 0 := typedGsMatrix_row0_block1 T i j hi0 hj1 hj2
      _ = (gsRow0 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i.1 % m)).getD j.1 0 := by
            simpa [hmi] using
              (gsRow0_getD_block1 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i := i.1 % m) (j := j.1) hj1 hj2).symm
      _ = ((gsMatrixOfTSequence T).rows.getD i.1 []).getD j.1 0 := by rw [hrow]
  · rcases block2_bounds_of_div_eq_two hmpos hdj with ⟨hj1, hj2⟩
    calc
      typedGsMatrixOfTSequence T i j
          = (applyR (circulantRow m Q.x3 i.1)).getD (j.1 - 2 * m) 0 := typedGsMatrix_row0_block2 T i j hi0 hj1 hj2
      _ = (gsRow0 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i.1 % m)).getD j.1 0 := by
            simpa [hmi] using
              (gsRow0_getD_block2 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i := i.1 % m) (j := j.1) hj1 hj2).symm
      _ = ((gsMatrixOfTSequence T).rows.getD i.1 []).getD j.1 0 := by rw [hrow]
  · rcases block3_bounds_of_div_eq_three hmpos hdj with ⟨hj1, hj2⟩
    calc
      typedGsMatrixOfTSequence T i j
          = (applyR (circulantRow m Q.x4 i.1)).getD (j.1 - 3 * m) 0 := typedGsMatrix_row0_block3 T i j hi0 hj1 hj2
      _ = (gsRow0 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i.1 % m)).getD j.1 0 := by
            simpa [hmi] using
              (gsRow0_getD_block3 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i := i.1 % m) (j := j.1) hj1 hj2).symm
      _ = ((gsMatrixOfTSequence T).rows.getD i.1 []).getD j.1 0 := by rw [hrow]

private lemma typedGsMatrix_entry_eq_step3_row1 {m : Nat} (T : TSequence m)
    (i j : Fin (4 * m)) (hi1 : m ≤ i.1) (hi2 : i.1 < 2 * m) :
    typedGsMatrixOfTSequence T i j =
      ((gsMatrixOfTSequence T).rows.getD i.1 []).getD j.1 0 := by
  let Q := gsSequenceQuadOfTSequence T
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hi2
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hi : i.1 < 4 * m := by simpa using i.2
  have hdi : i.1 / m = 1 := div_eq_one_of_block1 hmpos hi1 hi2
  have hmi : i.1 % m = i.1 - m := mod_eq_sub_of_div_eq_one hdi
  have hrow : (gsMatrixOfTSequence T).rows.getD i.1 [] =
      gsRow1 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i.1 % m) := by
    simpa [Q, hdi] using gsMatrixOfTSequence_getD_row T i.1 hi
  have hjlt4 : j.1 / m < 4 := by
    exact (Nat.div_lt_iff_lt_mul hmpos).2 (by simpa [Nat.mul_comm] using j.2)
  interval_cases hdj : j.1 / m
  · have hj0 : j.1 < m := lt_of_div_eq_zero hm0 hdj
    calc
      typedGsMatrixOfTSequence T i j
          = (negRow (applyR (circulantRow m Q.x2 (i.1 - m)))).getD j.1 0 := typedGsMatrix_row1_block0 T i j hi1 hi2 hj0
      _ = (gsRow1 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i.1 % m)).getD j.1 0 := by
            simpa [hmi] using
              (gsRow1_getD_block0 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i := i.1 % m) (j := j.1) hj0).symm
      _ = ((gsMatrixOfTSequence T).rows.getD i.1 []).getD j.1 0 := by rw [hrow]
  · rcases block1_bounds_of_div_eq_one hmpos hdj with ⟨hj1', hj2'⟩
    calc
      typedGsMatrixOfTSequence T i j
          = (circulantRow m Q.x1 (i.1 - m)).getD (j.1 - m) 0 := typedGsMatrix_row1_block1 T i j hi1 hi2 hj1' hj2'
      _ = (gsRow1 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i.1 % m)).getD j.1 0 := by
            simpa [hmi] using
              (gsRow1_getD_block1 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i := i.1 % m) (j := j.1) hj1' hj2').symm
      _ = ((gsMatrixOfTSequence T).rows.getD i.1 []).getD j.1 0 := by rw [hrow]
  · rcases block2_bounds_of_div_eq_two hmpos hdj with ⟨hj1', hj2'⟩
    calc
      typedGsMatrixOfTSequence T i j
          = (trRow (m := m) Q.x4 (i.1 - m)).getD (j.1 - 2 * m) 0 := typedGsMatrix_row1_block2 T i j hi1 hi2 hj1' hj2'
      _ = (gsRow1 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i.1 % m)).getD j.1 0 := by
            simpa [hmi] using
              (gsRow1_getD_block2 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i := i.1 % m) (j := j.1) hj1' hj2').symm
      _ = ((gsMatrixOfTSequence T).rows.getD i.1 []).getD j.1 0 := by rw [hrow]
  · rcases block3_bounds_of_div_eq_three hmpos hdj with ⟨hj1', hj2'⟩
    calc
      typedGsMatrixOfTSequence T i j
          = (negRow (trRow (m := m) Q.x3 (i.1 - m))).getD (j.1 - 3 * m) 0 := typedGsMatrix_row1_block3 T i j hi1 hi2 hj1' hj2'
      _ = (gsRow1 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i.1 % m)).getD j.1 0 := by
            simpa [hmi] using
              (gsRow1_getD_block3 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i := i.1 % m) (j := j.1) hj1' hj2').symm
      _ = ((gsMatrixOfTSequence T).rows.getD i.1 []).getD j.1 0 := by rw [hrow]

private lemma typedGsMatrix_entry_eq_step3_row2 {m : Nat} (T : TSequence m)
    (i j : Fin (4 * m)) (hi1 : 2 * m ≤ i.1) (hi2 : i.1 < 3 * m) :
    typedGsMatrixOfTSequence T i j =
      ((gsMatrixOfTSequence T).rows.getD i.1 []).getD j.1 0 := by
  let Q := gsSequenceQuadOfTSequence T
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hi2
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hi : i.1 < 4 * m := by simpa using i.2
  have hdi : i.1 / m = 2 := div_eq_two_of_block2 hmpos hi1 hi2
  have hmi : i.1 % m = i.1 - 2 * m := mod_eq_sub_two_mul_of_div_eq_two hdi
  have hrow : (gsMatrixOfTSequence T).rows.getD i.1 [] =
      gsRow2 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i.1 % m) := by
    simpa [Q, hdi] using gsMatrixOfTSequence_getD_row T i.1 hi
  have hjlt4 : j.1 / m < 4 := by
    exact (Nat.div_lt_iff_lt_mul hmpos).2 (by simpa [Nat.mul_comm] using j.2)
  interval_cases hdj : j.1 / m
  · have hj0 : j.1 < m := lt_of_div_eq_zero hm0 hdj
    calc
      typedGsMatrixOfTSequence T i j
          = (negRow (applyR (circulantRow m Q.x3 (i.1 - 2 * m)))).getD j.1 0 := typedGsMatrix_row2_block0 T i j hi1 hi2 hj0
      _ = (gsRow2 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i.1 % m)).getD j.1 0 := by
            simpa [hmi] using
              (gsRow2_getD_block0 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i := i.1 % m) (j := j.1) hj0).symm
      _ = ((gsMatrixOfTSequence T).rows.getD i.1 []).getD j.1 0 := by rw [hrow]
  · rcases block1_bounds_of_div_eq_one hmpos hdj with ⟨hj1', hj2'⟩
    calc
      typedGsMatrixOfTSequence T i j
          = (negRow (trRow (m := m) Q.x4 (i.1 - 2 * m))).getD (j.1 - m) 0 := typedGsMatrix_row2_block1 T i j hi1 hi2 hj1' hj2'
      _ = (gsRow2 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i.1 % m)).getD j.1 0 := by
            simpa [hmi] using
              (gsRow2_getD_block1 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i := i.1 % m) (j := j.1) hj1' hj2').symm
      _ = ((gsMatrixOfTSequence T).rows.getD i.1 []).getD j.1 0 := by rw [hrow]
  · rcases block2_bounds_of_div_eq_two hmpos hdj with ⟨hj1', hj2'⟩
    calc
      typedGsMatrixOfTSequence T i j
          = (circulantRow m Q.x1 (i.1 - 2 * m)).getD (j.1 - 2 * m) 0 := typedGsMatrix_row2_block2 T i j hi1 hi2 hj1' hj2'
      _ = (gsRow2 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i.1 % m)).getD j.1 0 := by
            simpa [hmi] using
              (gsRow2_getD_block2 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i := i.1 % m) (j := j.1) hj1' hj2').symm
      _ = ((gsMatrixOfTSequence T).rows.getD i.1 []).getD j.1 0 := by rw [hrow]
  · rcases block3_bounds_of_div_eq_three hmpos hdj with ⟨hj1', hj2'⟩
    calc
      typedGsMatrixOfTSequence T i j
          = (trRow (m := m) Q.x2 (i.1 - 2 * m)).getD (j.1 - 3 * m) 0 := typedGsMatrix_row2_block3 T i j hi1 hi2 hj1' hj2'
      _ = (gsRow2 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i.1 % m)).getD j.1 0 := by
            simpa [hmi] using
              (gsRow2_getD_block3 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i := i.1 % m) (j := j.1) hj1' hj2').symm
      _ = ((gsMatrixOfTSequence T).rows.getD i.1 []).getD j.1 0 := by rw [hrow]

private lemma typedGsMatrix_entry_eq_step3_row3 {m : Nat} (T : TSequence m)
    (i j : Fin (4 * m)) (hi1 : 3 * m ≤ i.1) (hi2 : i.1 < 4 * m) :
    typedGsMatrixOfTSequence T i j =
      ((gsMatrixOfTSequence T).rows.getD i.1 []).getD j.1 0 := by
  let Q := gsSequenceQuadOfTSequence T
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    simp at hi2
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hi : i.1 < 4 * m := by simpa using i.2
  have hdi : i.1 / m = 3 := div_eq_three_of_block3 hmpos hi1 hi2
  have hmi : i.1 % m = i.1 - 3 * m := mod_eq_sub_three_mul_of_div_eq_three hdi
  have hrow : (gsMatrixOfTSequence T).rows.getD i.1 [] =
      gsRow3 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i.1 % m) := by
    simpa [Q, hdi] using gsMatrixOfTSequence_getD_row T i.1 hi
  have hjlt4 : j.1 / m < 4 := by
    exact (Nat.div_lt_iff_lt_mul hmpos).2 (by simpa [Nat.mul_comm] using j.2)
  interval_cases hdj : j.1 / m
  · have hj0 : j.1 < m := lt_of_div_eq_zero hm0 hdj
    calc
      typedGsMatrixOfTSequence T i j
          = (negRow (applyR (circulantRow m Q.x4 (i.1 - 3 * m)))).getD j.1 0 := typedGsMatrix_row3_block0 T i j hi1 hi2 hj0
      _ = (gsRow3 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i.1 % m)).getD j.1 0 := by
            simpa [hmi] using
              (gsRow3_getD_block0 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i := i.1 % m) (j := j.1) hj0).symm
      _ = ((gsMatrixOfTSequence T).rows.getD i.1 []).getD j.1 0 := by rw [hrow]
  · rcases block1_bounds_of_div_eq_one hmpos hdj with ⟨hj1', hj2'⟩
    calc
      typedGsMatrixOfTSequence T i j
          = (trRow (m := m) Q.x3 (i.1 - 3 * m)).getD (j.1 - m) 0 := typedGsMatrix_row3_block1 T i j hi1 hi2 hj1' hj2'
      _ = (gsRow3 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i.1 % m)).getD j.1 0 := by
            simpa [hmi] using
              (gsRow3_getD_block1 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i := i.1 % m) (j := j.1) hj1' hj2').symm
      _ = ((gsMatrixOfTSequence T).rows.getD i.1 []).getD j.1 0 := by rw [hrow]
  · rcases block2_bounds_of_div_eq_two hmpos hdj with ⟨hj1', hj2'⟩
    calc
      typedGsMatrixOfTSequence T i j
          = (negRow (trRow (m := m) Q.x2 (i.1 - 3 * m))).getD (j.1 - 2 * m) 0 := typedGsMatrix_row3_block2 T i j hi1 hi2 hj1' hj2'
      _ = (gsRow3 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i.1 % m)).getD j.1 0 := by
            simpa [hmi] using
              (gsRow3_getD_block2 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i := i.1 % m) (j := j.1) hj1' hj2').symm
      _ = ((gsMatrixOfTSequence T).rows.getD i.1 []).getD j.1 0 := by rw [hrow]
  · rcases block3_bounds_of_div_eq_three hmpos hdj with ⟨hj1', hj2'⟩
    calc
      typedGsMatrixOfTSequence T i j
          = (circulantRow m Q.x1 (i.1 - 3 * m)).getD (j.1 - 3 * m) 0 := typedGsMatrix_row3_block3 T i j hi1 hi2 hj1' hj2'
      _ = (gsRow3 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i.1 % m)).getD j.1 0 := by
            simpa [hmi] using
              (gsRow3_getD_block3 (m := m) Q.x1 Q.x2 Q.x3 Q.x4 (i := i.1 % m) (j := j.1) hj1' hj2').symm
      _ = ((gsMatrixOfTSequence T).rows.getD i.1 []).getD j.1 0 := by rw [hrow]

lemma typedGsMatrix_entry_eq_step3 {m : Nat} (T : TSequence m) (i j : Fin (4 * m)) :
    typedGsMatrixOfTSequence T i j =
      ((gsMatrixOfTSequence T).rows.getD i.1 []).getD j.1 0 := by
  by_cases hm0 : m = 0
  · subst hm0
    exact Fin.elim0 i
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hilt4 : i.1 / m < 4 := by
      exact (Nat.div_lt_iff_lt_mul hmpos).2 (by simpa [Nat.mul_comm] using i.2)
    interval_cases hdi : i.1 / m
    · have hi0 : i.1 < m := lt_of_div_eq_zero hm0 hdi
      exact typedGsMatrix_entry_eq_step3_row0 T i j hi0
    · rcases block1_bounds_of_div_eq_one hmpos hdi with ⟨hi1, hi2⟩
      exact typedGsMatrix_entry_eq_step3_row1 T i j hi1 hi2
    · rcases block2_bounds_of_div_eq_two hmpos hdi with ⟨hi1, hi2⟩
      exact typedGsMatrix_entry_eq_step3_row2 T i j hi1 hi2
    · rcases block3_bounds_of_div_eq_three hmpos hdi with ⟨hi1, hi2⟩
      exact typedGsMatrix_entry_eq_step3_row3 T i j hi1 hi2

lemma matrixRow_typedGs_eq_step3_row {m : Nat} (T : TSequence m) (i : Fin (4 * m)) :
    matrixRow (typedGsMatrixOfTSequence T) i = (gsMatrixOfTSequence T).rows.getD i.1 [] := by
  apply List.ext_getElem
  · simpa [matrixRow] using (step3GsRow_length T i).symm
  · intro k hk1 hk2
    rw [← List.getD_eq_getElem _ _ hk1, ← List.getD_eq_getElem _ _ hk2]
    rw [matrixRow_getD (M := typedGsMatrixOfTSequence T) (i := i) (hj := by simpa [matrixRow] using hk1)]
    exact typedGsMatrix_entry_eq_step3 T i ⟨k, by simpa [matrixRow] using hk1⟩

theorem typedGsMatrix_target {m : Nat} (T : TSequence m) :
    (typedGsMatrixOfTSequence T) * Matrix.transpose (typedGsMatrixOfTSequence T) =
      (4 * m : Int) • (1 : IntMat (4 * m)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [← matrixRow_dot_eq_mul_transpose (M := typedGsMatrixOfTSequence T) i i]
    rw [matrixRow_typedGs_eq_step3_row T i]
    simpa using gsMatrixOfTSequence_self_dot T i.1 i.2
  · rw [← matrixRow_dot_eq_mul_transpose (M := typedGsMatrixOfTSequence T) i j]
    rw [matrixRow_typedGs_eq_step3_row T i, matrixRow_typedGs_eq_step3_row T j]
    have hij' : i.1 ≠ j.1 := by
      intro h
      apply hij
      exact Fin.ext h
    rw [gsMatrixOfTSequence_orthogonal T i.1 j.1 i.2 j.2 hij']
    simp [hij]

theorem typedGsMatrix_isHadamard {m : Nat} (T : TSequence m) :
    IsHadamardMat (typedGsMatrixOfTSequence T) := by
  refine ⟨gsMatrix_pmOne (gsDataOfTSequence T).toGSData, typedGsMatrix_target T⟩

end Turyn
