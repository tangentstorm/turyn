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
  simpa [typedGsMatrixOfTSequence] using gsMatrix_target (gsDataOfTSequence T)

theorem typedGsMatrix_isHadamard {m : Nat} (T : TSequence m) :
    IsHadamardMat (typedGsMatrixOfTSequence T) := by
  simpa [typedGsMatrixOfTSequence] using gsMatrix_isHadamard (gsDataOfTSequence T)

end Turyn
