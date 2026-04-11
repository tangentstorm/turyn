import Turyn.GSArrayBridge

/-!
# Constructive Hadamard Output

Top-level constructive interface from Turyn-type sequences, or an
`IsTurynType` certificate, to an explicit Hadamard matrix.
-/

namespace Turyn

/-- Construct the Hadamard matrix attached to a typed Turyn-type sequence. -/
def turynToHadamardMatrix {n : Nat} (T : TurynType n) :
    IntMat (4 * (3 * n - 1)) :=
  typedGsMatrixOfTSequence (step2 T)

/-- The constructive Hadamard matrix attached to a typed Turyn-type sequence
has the Hadamard property. -/
theorem turynToHadamardMatrix_isHadamard {n : Nat} (T : TurynType n) :
    IsHadamardMat (turynToHadamardMatrix T) := by
  simpa [turynToHadamardMatrix] using typedGsMatrix_isHadamard (step2 T)

/-- Convenience entry point from an existing `IsTurynType` certificate. -/
def ofIsTurynTypeMatrix {n : Nat} {x y z w : PmSeq}
    (h : IsTurynType n x y z w) :
    IntMat (4 * (3 * n - 1)) :=
  turynToHadamardMatrix h.toTyped

/-- Correctness theorem for the convenience entry point. -/
theorem ofIsTurynTypeMatrix_isHadamard {n : Nat} {x y z w : PmSeq}
    (h : IsTurynType n x y z w) :
    IsHadamardMat (ofIsTurynTypeMatrix h) := by
  simpa [ofIsTurynTypeMatrix] using turynToHadamardMatrix_isHadamard h.toTyped

end Turyn
