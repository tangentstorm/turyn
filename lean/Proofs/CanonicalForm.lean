import Turyn.Equivalence

/-!
# Proof: canonical representative exists

`Turyn.Result.canonical_form_exists` is `Turyn.canonical_representative_exists`
from `Turyn/Equivalence.lean`, re-exposed under the `Turyn.Result` namespace
for comparator.
-/

namespace Turyn.Result

theorem canonical_form_exists
    (n : Nat) (hn_even : n % 2 = 0) (hn : 2 ≤ n) (S : TurynType n) :
    ∃ T : TurynType n, Equivalent n S T ∧ Canonical n T :=
  Turyn.canonical_representative_exists n hn_even hn S

end Turyn.Result
