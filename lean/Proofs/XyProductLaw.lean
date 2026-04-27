import Turyn.XY

/-!
# Proof: XY interior anti-palindrome

`Turyn.Result.xy_interior_antipalindrome` is `Turyn.xy_product_law` from
`Turyn/XY.lean`, re-exposed under the `Turyn.Result` namespace for
comparator. The "XY product law" and the "interior anti-palindrome"
statement are the same theorem; the latter is the readable interpretation:
for `2 ≤ k ≤ n − 1`, `uAt S (n + 1 − k) = − uAt S k`.
-/

namespace Turyn.Result

theorem xy_interior_antipalindrome {n : Nat} (S : TurynType n) (hn : 4 ≤ n)
    (hc : Canonical1 n S) :
    ∀ k, 2 ≤ k → k ≤ n - 1 → uAt S (n + 1 - k) = -(uAt S k) :=
  Turyn.xy_product_law S hn hc

end Turyn.Result
