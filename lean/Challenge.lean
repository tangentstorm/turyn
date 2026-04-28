import Turyn.Defs

/-!
# Challenge: Headline Theorems for Comparator

This is the trusted **challenge module** for `leanprover/comparator`.
It states the headline results of the Turyn library with `sorry`
placeholders.  The matching proofs live in `Results.lean`, which
comparator builds independently and verifies against this file.

The headline names live in the `Turyn.Result` namespace to avoid colliding
with the underlying lemmas of the same name in `Turyn.Equivalence` and
`Turyn.XY`.

## Definitions referenced

The headline statements use the following definitions, all in `Turyn/Defs.lean`:

- `PmSeq n`, `TurynType n`, `aperiodicAutocorr`, `combinedAutocorr` —
  the foundational sequence and quadruple types.
- `IsTurynType X Y Z W` — direct vanishing predicate on a `±1` quadruple.
- `Turyn.IntMat`, `Turyn.IsHadamardMat` — the matrix layer.
- `Canonical1 n S` — endpoint-sign canonical condition (BDKR §2 (i)).
- `Turyn.uAt` — the U = X · Y product accessor.

## Headline theorems (this file)

1. `tt_implies_hadamard` — *if a TT(n) exists, a Hadamard matrix of order
   `4 (3 n − 1)` exists*. The witness is the constructive base-sequence →
   T-sequence → Goethals–Seidel pipeline.
2. `xy_interior_antipalindrome` — for a canonical Turyn sequence of length
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

/-- **XY interior anti-palindrome** ("XY product law", discovered by codex).
For a canonical Turyn sequence of length `n ≥ 4`, the U-sequence
(`U = X · Y` coordinatewise) is an anti-palindrome on its interior:
`uAt S (n + 1 − k) = − uAt S k` for every `2 ≤ k ≤ n − 1`. -/
theorem xy_interior_antipalindrome {n : Nat} (S : TurynType n) (hn : 4 ≤ n)
    (hc : Canonical1 n S) :
    ∀ k, 2 ≤ k → k ≤ n - 1 → uAt S (n + 1 - k) = -(uAt S k) := by
  sorry

end Turyn.Result
