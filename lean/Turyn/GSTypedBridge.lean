import Turyn.Step3
import Turyn.GSTyped

namespace Turyn

/-- Convert a length-`n` list into a typed vector on `Fin n`. -/
def listToIntVec {n : Nat} (xs : List Int) (hxs : xs.length = n) : IntVec n :=
  fun i => xs.getD i.1 0

@[simp] theorem listToIntVec_apply {n : Nat} (xs : List Int) (hxs : xs.length = n) (i : Fin n) :
    listToIntVec xs hxs i = xs.getD i.1 0 := rfl

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
      simpa [combinedPeriodic, periodicAutocorr, listToIntVec,
        Q.x1_len, Q.x2_len, Q.x3_len, Q.x4_len]
        using Q.periodic_vanishing s.1 hs1 hslt }

/-- Typed GS input extracted from a T-sequence. -/
def gsDataOfTSequence {m : Nat} (T : TSequence m) : CertifiedGSData m :=
  gsDataOfQuad (gsSequenceQuadOfTSequence T)

/-- The typed GS matrix attached to a T-sequence. -/
def typedGsMatrixOfTSequence {m : Nat} (T : TSequence m) : IntMat (4 * m) :=
  gsMatrix (gsDataOfTSequence T)

/-- Typed Hadamard theorem for a T-sequence, reducing everything to the typed GS target. -/
theorem typedGsMatrix_isHadamard {m : Nat} (T : TSequence m) :
    IsHadamardMat (typedGsMatrixOfTSequence T) := by
  exact gsMatrix_isHadamard (gsDataOfTSequence T)

end Turyn
