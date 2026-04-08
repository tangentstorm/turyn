import Turyn.Step3

/-!
# Typed Pipeline Examples

This file exercises the standalone typed Step1/Step2/Step3 pipeline without
depending on `Turyn.Hadamard`.
-/

def tt6X_typed : PmSeq := [-1, -1, -1, -1, 1, -1]
def tt6Y_typed : PmSeq := [-1, -1, -1, 1, -1, -1]
def tt6Z_typed : PmSeq := [-1, -1, 1, -1, 1, 1]
def tt6W_typed : PmSeq := [-1, 1, 1, 1, -1]

theorem tt6_valid_typed : IsTurynType 6 tt6X_typed tt6Y_typed tt6Z_typed tt6W_typed := by
  native_decide

/-- The standalone typed pipeline produces a Hadamard output of order 68 from TT(6). -/
noncomputable def tt6_hadamard : HadamardMatrix 68 := by
  simpa using (ofIsTurynType tt6_valid_typed)

theorem tt6_hadamard_isHadamard :
    tt6_hadamard.matrix.IsHadamard := by
  exact tt6_hadamard.isHadamard
