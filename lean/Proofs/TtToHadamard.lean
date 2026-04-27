import Turyn.Hadamard

/-!
# Proof: TT(n) ⇒ Hadamard

`Turyn.Result.tt_implies_hadamard` packages the constructive
`ofIsTurynTypeMatrix` / `ofIsTurynTypeMatrix_isHadamard` pair from
`Turyn/Hadamard.lean` into the existence form expected by
`Results.lean`.
-/

namespace Turyn.Result

theorem tt_implies_hadamard {n : Nat} {X Y Z : PmSeq n} {W : PmSeq (n - 1)}
    (h : IsTurynType X Y Z W) :
    ∃ H : IntMat (4 * (3 * n - 1)), IsHadamardMat H :=
  ⟨Turyn.ofIsTurynTypeMatrix h, Turyn.ofIsTurynTypeMatrix_isHadamard h⟩

end Turyn.Result
