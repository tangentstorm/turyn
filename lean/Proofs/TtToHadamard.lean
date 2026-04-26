import Turyn.Hadamard

/-!
# Proof: TT → Hadamard pipeline

`Turyn.Result.tt_to_hadamard` is `Turyn.turynToHadamardMatrix_isHadamard`,
the existing Lean proof from `Turyn/Hadamard.lean`. This file re-exposes it
under the `Turyn.Result` namespace so that comparator can compare it against
`Results.lean`.
-/

namespace Turyn.Result

theorem tt_to_hadamard {n : Nat} (T : TurynType n) :
    IsHadamardMat (turynToHadamardMatrix T) :=
  Turyn.turynToHadamardMatrix_isHadamard T

end Turyn.Result
