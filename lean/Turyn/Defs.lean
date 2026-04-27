import Turyn.TurynType
import Turyn.MatrixTyped
import Turyn.Equivalence
import Turyn.XY

/-!
# Turyn.Defs: Definition Surface for `Results.lean`

This file is the single import target for the `leanprover/comparator`
challenge module `Results.lean`. It re-exports the definitions referenced
by the headline statements:

- `PmSeq`, `IsTurynType` (from `Turyn.TurynType`)
- `Turyn.IntMat`, `Turyn.IsHadamardMat` (from `Turyn.MatrixTyped`)
- `Turyn.TurynTypeSeq`, `Turyn.Equivalent`, `Turyn.Canonical`,
  `Turyn.Canonical1` (from `Turyn.Equivalence`)
- `Turyn.uAt` (from `Turyn.XY`)

Keeping the surface in one place makes the comparator trusted base
explicit — anything the headline theorems depend on is reachable
through this module.
-/
