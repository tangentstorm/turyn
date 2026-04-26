import Proofs.TtToHadamard
import Proofs.CanonicalForm
import Proofs.XyProductLaw

/-!
# Proofs: Comparator Solution Module

This is the **solution module** for `leanprover/comparator`, paired with
`Results.lean`. Each proof file under `Proofs/` exposes one of the headline
theorems under the `Turyn.Result` namespace; this top-level file just imports
them so comparator has a single solution module to point at.

Run comparator with:

```
lake env <path-to-comparator> comparator-config.json
```
-/
