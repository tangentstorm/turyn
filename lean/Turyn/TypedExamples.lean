import Turyn.Hadamard

/-!
# Typed Pipeline Examples

This file exercises the constructive typed Turyn-to-Hadamard pipeline.
-/

def tt6X_typed : PmSeq := [-1, -1, -1, -1, 1, -1]
def tt6Y_typed : PmSeq := [-1, -1, -1, 1, -1, -1]
def tt6Z_typed : PmSeq := [-1, -1, 1, -1, 1, 1]
def tt6W_typed : PmSeq := [-1, 1, 1, 1, -1]

theorem tt6_valid_typed : IsTurynType 6 tt6X_typed tt6Y_typed tt6Z_typed tt6W_typed := by
  native_decide

/-- The constructive typed pipeline produces a Hadamard matrix of order 68 from TT(6). -/
def tt6_hadamard : IntMat 68 :=
  ofIsTurynTypeMatrix tt6_valid_typed

theorem tt6_hadamard_isHadamard :
    IsHadamardMat tt6_hadamard := by
  exact ofIsTurynTypeMatrix_isHadamard tt6_valid_typed
