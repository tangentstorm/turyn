import Turyn.TurynType
import Turyn.Hadamard
import Turyn.Equivalence
import Turyn.XY

/-!
# Results: Headline Theorems for Comparator

This is the trusted **challenge module** for `leanprover/comparator`.
It states the headline results of the Turyn library with `sorry` placeholders.
The matching proofs live in `Proofs.lean` (and the modules under `Proofs/`),
which comparator builds independently and verifies against this file.

The three headline results:

1. `tt_to_hadamard` — every `TurynType n` yields a Hadamard matrix of order
   `4 (3 n − 1)` via the constructive base-sequence → T-sequence →
   Goethals–Seidel pipeline.
2. `canonical_form_exists` — every Turyn-type sequence is equivalent
   (under the symmetry group T1..T4) to one in canonical form
   (Best–Đoković–Kharaghani–Ramp normalization, arXiv:1206.4107).
3. `xy_product_law` — for a canonical Turyn sequence of length `n ≥ 4`,
   `uAt S (n + 1 − k) = − uAt S k` for every `2 ≤ k ≤ n − 1`.

The headline names live in the `Turyn.Result` namespace to avoid colliding
with the underlying lemmas of the same name in `Turyn.Equivalence` and
`Turyn.XY` — this file imports those modules to reuse their definitions
(`TurynType`, `TurynTypeSeq`, `Canonical1`, `uAt`, …) for the statements.
-/

namespace Turyn.Result

/-- **TT → Hadamard pipeline.** From a Turyn-type sequence of length `n`,
the constructive Goethals–Seidel pipeline produces a Hadamard matrix of
order `4 (3 n − 1)`. -/
theorem tt_to_hadamard {n : Nat} (T : TurynType n) :
    IsHadamardMat (turynToHadamardMatrix T) := by
  sorry

/-- **Canonical representative exists.** For even `n ≥ 2`, every Turyn-type
sequence is equivalent (under T1..T4) to a canonical representative
satisfying conditions (i)..(vi) of Best–Đoković–Kharaghani–Ramp. -/
theorem canonical_form_exists
    (n : Nat) (hn_even : n % 2 = 0) (hn : 2 ≤ n) (S : TurynTypeSeq n) :
    ∃ T : TurynTypeSeq n, Equivalent n S T ∧ Canonical n T := by
  sorry

/-- **XY product law** (Best–Đoković–Kharaghani–Ramp).
For a canonical Turyn sequence of length `n ≥ 4`,
`uAt S (n + 1 − k) = − uAt S k` for every `2 ≤ k ≤ n − 1`. -/
theorem xy_product_law {n : Nat} (S : TurynTypeSeq n) (hn : 4 ≤ n)
    (hc : Canonical1 n S) :
    ∀ k, 2 ≤ k → k ≤ n - 1 → uAt S (n + 1 - k) = -(uAt S k) := by
  sorry

end Turyn.Result
