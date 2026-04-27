import Turyn.Hadamard
import Turyn.Equivalence
import Turyn.XY

/-!
# Proofs: Comparator Solution Module

This is the **solution module** for `leanprover/comparator`, paired with
`Results.lean`.  Each headline theorem under the `Turyn.Result` namespace
is re-exposed below as a thin wrapper around the corresponding result in
`Turyn.*`.

Run comparator with:

```
lake env <path-to-comparator> comparator-config.json
```
-/

namespace Turyn.Result

/-- **TT(n) ⇒ Hadamard.**  Packages the constructive
`ofIsTurynTypeMatrix` / `ofIsTurynTypeMatrix_isHadamard` pair from
`Turyn/Hadamard.lean` into the existence form expected by `Results.lean`. -/
theorem tt_implies_hadamard {n : Nat} {X Y Z : PmSeq n} {W : PmSeq (n - 1)}
    (h : IsTurynType X Y Z W) :
    ∃ H : IntMat (4 * (3 * n - 1)), IsHadamardMat H :=
  ⟨Turyn.ofIsTurynTypeMatrix h, Turyn.ofIsTurynTypeMatrix_isHadamard h⟩

/-- **Canonical representative exists.**  Re-exposes
`Turyn.canonical_representative_exists` (`Turyn/Equivalence.lean`) under
the `Turyn.Result` namespace. -/
theorem canonical_form_exists
    (n : Nat) (hn_even : n % 2 = 0) (hn : 2 ≤ n) (S : TurynType n) :
    ∃ T : TurynType n, Equivalent n S T ∧ Canonical n T :=
  Turyn.canonical_representative_exists n hn_even hn S

/-- **XY interior anti-palindrome.**  Re-exposes `Turyn.xy_product_law`
(`Turyn/XY.lean`) under the `Turyn.Result` namespace.  The "XY product
law" and the "interior anti-palindrome" statement are the same theorem;
the latter is the readable interpretation: for `2 ≤ k ≤ n − 1`,
`uAt S (n + 1 − k) = − uAt S k`. -/
theorem xy_interior_antipalindrome {n : Nat} (S : TurynType n) (hn : 4 ≤ n)
    (hc : Canonical1 n S) :
    ∀ k, 2 ≤ k → k ≤ n - 1 → uAt S (n + 1 - k) = -(uAt S k) :=
  Turyn.xy_product_law S hn hc

end Turyn.Result
