import Turyn.TSequence
import Turyn.GoethalsSeidel

/-!
# GS Array Bridge

Bridge lemmas that convert list-based T-sequence output into typed
Goethals-Seidel input and expose the resulting constructive Hadamard matrix.
-/

namespace Turyn

/-- Convert a length-`n` list into a typed vector on `Fin n`. -/
def listToIntVec {n : Nat} (xs : List Int) (hxs : xs.length = n) : IntVec n :=
  fun i => xs.getD i.1 0

@[simp] theorem listToIntVec_apply {n : Nat} (xs : List Int) (hxs : xs.length = n) (i : Fin n) :
    listToIntVec xs hxs i = xs.getD i.1 0 := rfl

/-! ### `±1` sequences extracted from a T-sequence -/

/-- First GS combination extracted from a T-sequence. -/
def tseqCombine1 {m : Nat} (T : TSequence m) : List Int :=
  (List.range m).map fun j =>
    T.a.getD j 0 + T.b.getD j 0 + T.c.getD j 0 + T.d.getD j 0

/-- Second GS combination extracted from a T-sequence. -/
def tseqCombine2 {m : Nat} (T : TSequence m) : List Int :=
  (List.range m).map fun j =>
    T.a.getD j 0 + T.b.getD j 0 - T.c.getD j 0 - T.d.getD j 0

/-- Third GS combination extracted from a T-sequence. -/
def tseqCombine3 {m : Nat} (T : TSequence m) : List Int :=
  (List.range m).map fun j =>
    T.a.getD j 0 - T.b.getD j 0 + T.c.getD j 0 - T.d.getD j 0

/-- Fourth GS combination extracted from a T-sequence. -/
def tseqCombine4 {m : Nat} (T : TSequence m) : List Int :=
  (List.range m).map fun j =>
    T.a.getD j 0 - T.b.getD j 0 - T.c.getD j 0 + T.d.getD j 0

@[simp] lemma tseqCombine1_length {m : Nat} (T : TSequence m) :
    (tseqCombine1 T).length = m := by simp [tseqCombine1]

@[simp] lemma tseqCombine2_length {m : Nat} (T : TSequence m) :
    (tseqCombine2 T).length = m := by simp [tseqCombine2]

@[simp] lemma tseqCombine3_length {m : Nat} (T : TSequence m) :
    (tseqCombine3 T).length = m := by simp [tseqCombine3]

@[simp] lemma tseqCombine4_length {m : Nat} (T : TSequence m) :
    (tseqCombine4 T).length = m := by simp [tseqCombine4]

@[simp] lemma tseqCombine1_getD {m : Nat} (T : TSequence m) {j : Nat} (hj : j < m) :
    (tseqCombine1 T).getD j 0 =
      T.a.getD j 0 + T.b.getD j 0 + T.c.getD j 0 + T.d.getD j 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa [tseqCombine1] using hj)]
  simp [tseqCombine1, hj]

@[simp] lemma tseqCombine2_getD {m : Nat} (T : TSequence m) {j : Nat} (hj : j < m) :
    (tseqCombine2 T).getD j 0 =
      T.a.getD j 0 + T.b.getD j 0 - T.c.getD j 0 - T.d.getD j 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa [tseqCombine2] using hj)]
  simp [tseqCombine2, hj]

@[simp] lemma tseqCombine3_getD {m : Nat} (T : TSequence m) {j : Nat} (hj : j < m) :
    (tseqCombine3 T).getD j 0 =
      T.a.getD j 0 - T.b.getD j 0 + T.c.getD j 0 - T.d.getD j 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa [tseqCombine3] using hj)]
  simp [tseqCombine3, hj]

@[simp] lemma tseqCombine4_getD {m : Nat} (T : TSequence m) {j : Nat} (hj : j < m) :
    (tseqCombine4 T).getD j 0 =
      T.a.getD j 0 - T.b.getD j 0 - T.c.getD j 0 + T.d.getD j 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa [tseqCombine4] using hj)]
  simp [tseqCombine4, hj]

lemma tseqCombine1_pmOne {m : Nat} (T : TSequence m) :
    ∀ j, j < m → (tseqCombine1 T).getD j 0 = 1 ∨ (tseqCombine1 T).getD j 0 = -1 := by
  intro j hj
  have h_support :
      Int.natAbs (T.a.getD j 0) + Int.natAbs (T.b.getD j 0) +
        Int.natAbs (T.c.getD j 0) + Int.natAbs (T.d.getD j 0) = 1 := by
    exact T.support j hj
  grind +locals

lemma tseqCombine2_pmOne {m : Nat} (T : TSequence m) :
    ∀ j, j < m → (tseqCombine2 T).getD j 0 = 1 ∨ (tseqCombine2 T).getD j 0 = -1 := by
  intro j hj
  have h_support :
      Int.natAbs (T.a.getD j 0) + Int.natAbs (T.b.getD j 0) +
        Int.natAbs (T.c.getD j 0) + Int.natAbs (T.d.getD j 0) = 1 := by
    exact T.support j hj
  grind +locals

lemma tseqCombine3_pmOne {m : Nat} (T : TSequence m) :
    ∀ j, j < m → (tseqCombine3 T).getD j 0 = 1 ∨ (tseqCombine3 T).getD j 0 = -1 := by
  intro j hj
  have h_support :
      Int.natAbs (T.a.getD j 0) + Int.natAbs (T.b.getD j 0) +
        Int.natAbs (T.c.getD j 0) + Int.natAbs (T.d.getD j 0) = 1 := by
    exact T.support j hj
  grind +locals

lemma tseqCombine4_pmOne {m : Nat} (T : TSequence m) :
    ∀ j, j < m → (tseqCombine4 T).getD j 0 = 1 ∨ (tseqCombine4 T).getD j 0 = -1 := by
  intro j hj
  have h_support :
      Int.natAbs (T.a.getD j 0) + Int.natAbs (T.b.getD j 0) +
        Int.natAbs (T.c.getD j 0) + Int.natAbs (T.d.getD j 0) = 1 := by
    exact T.support j hj
  grind +locals

/-- Summand-level GS identity for a single coordinate pair. -/
lemma tseqCombine_summand_identity {m : Nat} (T : TSequence m) (i j : Nat) :
    (T.a.getD i 0 + T.b.getD i 0 + T.c.getD i 0 + T.d.getD i 0) *
        (T.a.getD j 0 + T.b.getD j 0 + T.c.getD j 0 + T.d.getD j 0) +
      (T.a.getD i 0 + T.b.getD i 0 - T.c.getD i 0 - T.d.getD i 0) *
        (T.a.getD j 0 + T.b.getD j 0 - T.c.getD j 0 - T.d.getD j 0) +
      (T.a.getD i 0 - T.b.getD i 0 + T.c.getD i 0 - T.d.getD i 0) *
        (T.a.getD j 0 - T.b.getD j 0 + T.c.getD j 0 - T.d.getD j 0) +
      (T.a.getD i 0 - T.b.getD i 0 - T.c.getD i 0 + T.d.getD i 0) *
        (T.a.getD j 0 - T.b.getD j 0 - T.c.getD j 0 + T.d.getD j 0) =
      4 * (T.a.getD i 0 * T.a.getD j 0 + T.b.getD i 0 * T.b.getD j 0 +
        T.c.getD i 0 * T.c.getD j 0 + T.d.getD i 0 * T.d.getD j 0) := by
  ring

lemma tseqCombine_periodic_summand_identity {m : Nat} (T : TSequence m) (s i : Nat) :
    (tseqCombine1 T).getD i 0 * (tseqCombine1 T).getD ((i + s) % m) 0 +
      (tseqCombine2 T).getD i 0 * (tseqCombine2 T).getD ((i + s) % m) 0 +
      (tseqCombine3 T).getD i 0 * (tseqCombine3 T).getD ((i + s) % m) 0 +
      (tseqCombine4 T).getD i 0 * (tseqCombine4 T).getD ((i + s) % m) 0 =
      4 * (T.a.getD i 0 * T.a.getD ((i + s) % m) 0 +
        T.b.getD i 0 * T.b.getD ((i + s) % m) 0 +
        T.c.getD i 0 * T.c.getD ((i + s) % m) 0 +
        T.d.getD i 0 * T.d.getD ((i + s) % m) 0) := by
  by_cases hi : i < m
  · have hmod : (i + s) % m < m := by
      by_cases hm : m = 0
      · exfalso
        omega
      · exact Nat.mod_lt _ (Nat.pos_of_ne_zero hm)
    rw [tseqCombine1_getD T hi, tseqCombine2_getD T hi, tseqCombine3_getD T hi, tseqCombine4_getD T hi]
    rw [tseqCombine1_getD T hmod, tseqCombine2_getD T hmod, tseqCombine3_getD T hmod, tseqCombine4_getD T hmod]
    exact tseqCombine_summand_identity T i ((i + s) % m)
  · have hm : m ≤ i := by omega
    have ha : T.a.getD i 0 = 0 := by
      exact List.getD_eq_default _ _ (by simpa [T.a_len] using hm)
    have hb : T.b.getD i 0 = 0 := by
      exact List.getD_eq_default _ _ (by simpa [T.b_len] using hm)
    have hc : T.c.getD i 0 = 0 := by
      exact List.getD_eq_default _ _ (by simpa [T.c_len] using hm)
    have hd : T.d.getD i 0 = 0 := by
      exact List.getD_eq_default _ _ (by simpa [T.d_len] using hm)
    have h1 : (tseqCombine1 T).getD i 0 = 0 := by
      exact List.getD_eq_default _ _ (by simpa [tseqCombine1_length T] using hm)
    have h2 : (tseqCombine2 T).getD i 0 = 0 := by
      exact List.getD_eq_default _ _ (by simpa [tseqCombine2_length T] using hm)
    have h3 : (tseqCombine3 T).getD i 0 = 0 := by
      exact List.getD_eq_default _ _ (by simpa [tseqCombine3_length T] using hm)
    have h4 : (tseqCombine4 T).getD i 0 = 0 := by
      exact List.getD_eq_default _ _ (by simpa [tseqCombine4_length T] using hm)
    rw [h1, h2, h3, h4, ha, hb, hc, hd]
    ring

lemma tseqCombine_periodic_sum_identity {m : Nat} (T : TSequence m) (s : Nat) :
    ∑ i ∈ Finset.range m,
      ((tseqCombine1 T).getD i 0 * (tseqCombine1 T).getD ((i + s) % m) 0 +
        (tseqCombine2 T).getD i 0 * (tseqCombine2 T).getD ((i + s) % m) 0 +
        (tseqCombine3 T).getD i 0 * (tseqCombine3 T).getD ((i + s) % m) 0 +
        (tseqCombine4 T).getD i 0 * (tseqCombine4 T).getD ((i + s) % m) 0) =
      ∑ i ∈ Finset.range m,
        4 * (T.a.getD i 0 * T.a.getD ((i + s) % m) 0 +
          T.b.getD i 0 * T.b.getD ((i + s) % m) 0 +
          T.c.getD i 0 * T.c.getD ((i + s) % m) 0 +
          T.d.getD i 0 * T.d.getD ((i + s) % m) 0) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact tseqCombine_periodic_summand_identity T s i

theorem tseqCombine_periodic_identity {m : Nat} (T : TSequence m) :
    ∀ s, combinedPeriodicAutocorr (tseqCombine1 T) (tseqCombine2 T)
      (tseqCombine3 T) (tseqCombine4 T) s =
      4 * combinedPeriodicAutocorr T.a T.b T.c T.d s := by
  intro s
  by_cases hm : m = 0
  · subst hm
    have ha : T.a = [] := List.eq_nil_of_length_eq_zero T.a_len
    have hb : T.b = [] := List.eq_nil_of_length_eq_zero T.b_len
    have hc : T.c = [] := List.eq_nil_of_length_eq_zero T.c_len
    have hd : T.d = [] := List.eq_nil_of_length_eq_zero T.d_len
    simp [_root_.periodicAutocorr, ha, hb, hc, hd, combinedPeriodicAutocorr, tseqCombine1,
      tseqCombine2, tseqCombine3, tseqCombine4]
  · unfold combinedPeriodicAutocorr _root_.periodicAutocorr
    simp [tseqCombine1_length T, tseqCombine2_length T, tseqCombine3_length T, tseqCombine4_length T,
      T.a_len, T.b_len, T.c_len, T.d_len, hm]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    calc
      ∑ x ∈ Finset.range m,
          ((tseqCombine1 T)[x]?.getD 0 * (tseqCombine1 T)[(x + s) % m]?.getD 0 +
                (tseqCombine2 T)[x]?.getD 0 * (tseqCombine2 T)[(x + s) % m]?.getD 0 +
              (tseqCombine3 T)[x]?.getD 0 * (tseqCombine3 T)[(x + s) % m]?.getD 0 +
            (tseqCombine4 T)[x]?.getD 0 * (tseqCombine4 T)[(x + s) % m]?.getD 0)
        = ∑ x ∈ Finset.range m,
            4 * (T.a[x]?.getD 0 * T.a[(x + s) % m]?.getD 0 +
              T.b[x]?.getD 0 * T.b[(x + s) % m]?.getD 0 +
              T.c[x]?.getD 0 * T.c[(x + s) % m]?.getD 0 +
              T.d[x]?.getD 0 * T.d[(x + s) % m]?.getD 0) := by
              simpa [List.getD_eq_getElem?_getD] using tseqCombine_periodic_sum_identity T s
      _ = 4 * ∑ x ∈ Finset.range m,
            (T.a[x]?.getD 0 * T.a[(x + s) % m]?.getD 0 +
              T.b[x]?.getD 0 * T.b[(x + s) % m]?.getD 0 +
              T.c[x]?.getD 0 * T.c[(x + s) % m]?.getD 0 +
              T.d[x]?.getD 0 * T.d[(x + s) % m]?.getD 0) := by
              rw [← Finset.mul_sum]
      _ = 4 *
            (∑ x ∈ Finset.range m, T.a[x]?.getD 0 * T.a[(x + s) % m]?.getD 0 +
                  ∑ x ∈ Finset.range m, T.b[x]?.getD 0 * T.b[(x + s) % m]?.getD 0 +
                ∑ x ∈ Finset.range m, T.c[x]?.getD 0 * T.c[(x + s) % m]?.getD 0 +
              ∑ x ∈ Finset.range m, T.d[x]?.getD 0 * T.d[(x + s) % m]?.getD 0) := by
              congr 1
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]

theorem tseqCombine_periodic_vanishing {m : Nat} (T : TSequence m) :
    ∀ s, 1 ≤ s → s < m →
      combinedPeriodicAutocorr (tseqCombine1 T) (tseqCombine2 T)
        (tseqCombine3 T) (tseqCombine4 T) s = 0 := by
  intro s hs1 hs2
  rw [tseqCombine_periodic_identity T s]
  rw [T.periodic_vanishing s hs1 hs2]
  ring

/-- Certified `±1` quadruple extracted from a T-sequence for the GS construction. -/
structure GSSequenceQuad (m : Nat) where
  x1 : List Int
  x2 : List Int
  x3 : List Int
  x4 : List Int
  x1_len : x1.length = m
  x2_len : x2.length = m
  x3_len : x3.length = m
  x4_len : x4.length = m
  x1_pm : ∀ j, j < m → x1.getD j 0 = 1 ∨ x1.getD j 0 = -1
  x2_pm : ∀ j, j < m → x2.getD j 0 = 1 ∨ x2.getD j 0 = -1
  x3_pm : ∀ j, j < m → x3.getD j 0 = 1 ∨ x3.getD j 0 = -1
  x4_pm : ∀ j, j < m → x4.getD j 0 = 1 ∨ x4.getD j 0 = -1
  periodic_vanishing :
    ∀ s, 1 ≤ s → s < m → combinedPeriodicAutocorr x1 x2 x3 x4 s = 0

/-- The four `±1` GS sequences attached to a T-sequence. -/
def gsSequenceQuadOfTSequence {m : Nat} (T : TSequence m) : GSSequenceQuad m :=
  { x1 := tseqCombine1 T
    x2 := tseqCombine2 T
    x3 := tseqCombine3 T
    x4 := tseqCombine4 T
    x1_len := tseqCombine1_length T
    x2_len := tseqCombine2_length T
    x3_len := tseqCombine3_length T
    x4_len := tseqCombine4_length T
    x1_pm := tseqCombine1_pmOne T
    x2_pm := tseqCombine2_pmOne T
    x3_pm := tseqCombine3_pmOne T
    x4_pm := tseqCombine4_pmOne T
    periodic_vanishing := tseqCombine_periodic_vanishing T }

lemma typed_periodicAutocorr_eq_list {n : Nat} (xs : List Int) (hxs : xs.length = n) (s : Fin n) :
    Turyn.periodicAutocorr (listToIntVec xs hxs) s = _root_.periodicAutocorr xs s.1 := by
  by_cases hn : n = 0
  · subst hn
    exact (Nat.not_lt_zero _ s.2).elim
  · rw [show _root_.periodicAutocorr xs s.1 =
      ∑ i ∈ Finset.range n, xs.getD i 0 * xs.getD ((i + s.1) % n) 0 by
        unfold _root_.periodicAutocorr
        simp [hxs, hn]]
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
      have hs1 : 1 ≤ s.1 := by omega
      have hslt : s.1 < m := s.2
      change
        Turyn.periodicAutocorr (listToIntVec Q.x1 Q.x1_len) s +
          Turyn.periodicAutocorr (listToIntVec Q.x2 Q.x2_len) s +
          Turyn.periodicAutocorr (listToIntVec Q.x3 Q.x3_len) s +
          Turyn.periodicAutocorr (listToIntVec Q.x4 Q.x4_len) s = 0
      rw [typed_combinedPeriodic_eq_list Q s]
      simpa using Q.periodic_vanishing s.1 hs1 hslt }

/-- Typed GS input extracted from a T-sequence. -/
def gsDataOfTSequence {m : Nat} (T : TSequence m) : CertifiedGSData m :=
  gsDataOfQuad (gsSequenceQuadOfTSequence T)

/-- The typed GS matrix attached to a T-sequence. -/
def typedGsMatrixOfTSequence {m : Nat} (T : TSequence m) : IntMat (4 * m) :=
  gsMatrix (gsDataOfTSequence T).toGSData

theorem typedGsMatrix_target {m : Nat} (T : TSequence m) :
    typedGsMatrixOfTSequence T * Matrix.transpose (typedGsMatrixOfTSequence T) =
      (4 * m : Int) • (1 : IntMat (4 * m)) := by
  simpa [typedGsMatrixOfTSequence, GSTarget] using gsMatrix_target (gsDataOfTSequence T)

theorem typedGsMatrix_isHadamard {m : Nat} (T : TSequence m) :
    IsHadamardMat (typedGsMatrixOfTSequence T) := by
  simpa [typedGsMatrixOfTSequence] using gsMatrix_isHadamard (gsDataOfTSequence T)

end Turyn
