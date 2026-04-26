import Turyn.XY

/-!
# Proof: XY product law

`Turyn.Result.xy_product_law` is `Turyn.xy_product_law` from `Turyn/XY.lean`,
re-exposed under the `Turyn.Result` namespace for comparator.
-/

namespace Turyn.Result

theorem xy_product_law {n : Nat} (S : TurynTypeSeq n) (hn : 4 ≤ n)
    (hc : Canonical1 n S) :
    ∀ k, 2 ≤ k → k ≤ n - 1 → uAt S (n + 1 - k) = -(uAt S k) :=
  Turyn.xy_product_law S hn hc

end Turyn.Result
