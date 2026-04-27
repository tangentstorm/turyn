import Turyn.Defs

/-!
# Results: Headline Theorems for Comparator

This is the trusted **challenge module** for `leanprover/comparator`.
It states the headline results of the Turyn library with `sorry` placeholders.
The matching proofs live in `Proofs.lean` (and the modules under `Proofs/`),
which comparator builds independently and verifies against this file.

The headline names live in the `Turyn.Result` namespace to avoid colliding
with the underlying lemmas of the same name in `Turyn.Equivalence` and
`Turyn.XY` — this file imports those modules to reuse their definitions
(`TurynType`, `TurynTypeSeq`, `Canonical1`, `uAt`, …) for the statements.

## Definitions referenced

The headline statements use the following definitions, which are imported
from the trusted `Turyn.*` modules and therefore part of the comparator
trusted base:

- `IsTurynType n x y z w` (`Turyn/TurynType.lean`):
    Boolean predicate, `(x, y, z, w)` is a TT(n).
- `TurynType n` (`Turyn/BaseSequence.lean`):
    bundled length-indexed TT(n) with the vanishing-autocorrelation witness.
- `IsHadamardMat H` (`Turyn/MatrixTyped.lean`):
    Hadamard predicate on a square `IntMat`.
- `TurynTypeSeq n` (`Turyn/Equivalence.lean`):
    bundled TT(n) plus an `IsTurynType` witness, the carrier of the
    `Equivalent`/`Canonical` relations.
- `Equivalent n S T` (`Turyn/Equivalence.lean`):
    reflexive-transitive closure of the T1..T4 elementary moves.
- `Canonical n S` (`Turyn/Equivalence.lean`):
    conjunction of the six BDKR canonical conditions (i)..(vi).

## Headline theorems (this file)

1. `tt_implies_hadamard` — *if a TT(n) exists, a Hadamard matrix of order
   `4 (3 n − 1)` exists*. The witness is the constructive base-sequence →
   T-sequence → Goethals–Seidel pipeline.
2. `canonical_form_exists` — every Turyn-type sequence (`TurynTypeSeq n`,
   even `n ≥ 2`) is equivalent to one in canonical form.
   *Note:* this is the existence half. The full BDKR result also says the
   canonical representative is unique within the equivalence class (orbit
   size dividing 1024); that uniqueness is not yet formalized here.
3. `xy_interior_antipalindrome` — for a canonical Turyn sequence of length
   `n ≥ 4`, the U = X·Y interior is an anti-palindrome:
   `uAt S (n + 1 − k) = − uAt S k` for every `2 ≤ k ≤ n − 1`. This is the
   "XY product law" (discovered by codex).
-/

namespace Turyn.Result

/-- **TT(n) ⇒ Hadamard.** If a Turyn-type sequence of length `n` exists,
then a Hadamard matrix of order `4 (3 n − 1)` exists. The witness is the
constructive Goethals–Seidel pipeline applied to the TT(n) certificate. -/
theorem tt_implies_hadamard {n : Nat} {X Y Z : PmSeq n} {W : PmSeq (n - 1)}
    (h : IsTurynType X Y Z W) :
    ∃ H : IntMat (4 * (3 * n - 1)), IsHadamardMat H := by
  sorry

/-- **Canonical representative exists** (existence half of BDKR §2).
For even `n ≥ 2`, every Turyn-type sequence is equivalent under T1..T4 to a
representative satisfying canonical conditions (i)..(vi).

The full BDKR theorem additionally asserts uniqueness of the canonical
representative within an equivalence class — that part is not yet
formalized; track it as future work. -/
theorem canonical_form_exists
    (n : Nat) (hn_even : n % 2 = 0) (hn : 2 ≤ n) (S : TurynTypeSeq n) :
    ∃ T : TurynTypeSeq n, Equivalent n S T ∧ Canonical n T := by
  sorry

/-- **XY interior anti-palindrome** ("XY product law", discovered by codex).
For a canonical Turyn sequence of length `n ≥ 4`, the U-sequence
(`U = X · Y` coordinatewise) is an anti-palindrome on its interior:
`uAt S (n + 1 − k) = − uAt S k` for every `2 ≤ k ≤ n − 1`. -/
theorem xy_interior_antipalindrome {n : Nat} (S : TurynTypeSeq n) (hn : 4 ≤ n)
    (hc : Canonical1 n S) :
    ∀ k, 2 ≤ k → k ≤ n - 1 → uAt S (n + 1 - k) = -(uAt S k) := by
  sorry

end Turyn.Result
