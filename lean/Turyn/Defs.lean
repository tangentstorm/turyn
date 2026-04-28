import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.GetD
import Mathlib.Data.Matrix.Basic

open Finset
open BigOperators
open Matrix

/-!
# Turyn.Defs

The trusted definitions named in `Challenge.lean`'s headline statements:

- `AllPmOne`, `AllSignOne` — entry-set predicates on `Fin n → Int`.
- `aperiodicAutocorr`, `combinedAutocorr` — autocorrelation primitives.
- `PmSeq n`, `SignSeq n` — length-indexed ±1 / {0, ±1} sequences
  carried as `Fin n → Int`.
- `TurynType n` — bundled TT(n) quadruple plus the vanishing identity.
- `IsTurynType X Y Z W` — direct vanishing predicate on a `±1` quadruple.
- `xAt/yAt/zAt/wAt`, `uAt` — 1-indexed entry accessors.
- `Canonical1` — BDKR endpoint-sign canonical condition (the only
  canonical predicate referenced by `Challenge.lean`; the remaining
  rules `Canonical2..6` and the bundled `Canonical` predicate live in
  `Turyn.Equivalence`).
- `Turyn.IntVec`, `Turyn.IntMat`, `Turyn.IsHadamardMat` — typed integer
  vector/matrix abbreviations and the matrix-level Hadamard predicate.

Boolean checks, decidability, parsers, and matrix-algebra lemmas
sit on top of these definitions in `Turyn.TurynType` and
`Turyn.MatUtils`.
-/

/-! ### Function-typed entry predicates -/

/-- Propositional version: every entry of `a : Fin n → Int` is `1` or `−1`. -/
def AllPmOne {n : Nat} (a : Fin n → Int) : Prop := ∀ i : Fin n, a i = 1 ∨ a i = -1

/-- Propositional version: every entry is `0`, `1`, or `−1`. -/
def AllSignOne {n : Nat} (a : Fin n → Int) : Prop :=
  ∀ i : Fin n, a i = 0 ∨ a i = 1 ∨ a i = -1

/-! ### Aperiodic autocorrelation on function-typed sequences

For `a : Fin n → Int` and shift `s : Nat`,
`aperiodicAutocorr a s = Σ_{i = 0}^{n − 1 − s} a_i · a_{i+s}`.
Returns `0` when `s ≥ n`.  We keep `s` a `Nat` so that the
combined-autocorrelation predicate quantifies over `Nat`. -/

/-- Look up `a : Fin n → Int` at 0-indexed `Nat` position `i`, returning `0`
if out of range.  Defined here (instead of inside `namespace Turyn`)
because `aperiodicAutocorr` uses it in the sum body. -/
def lookupNat {n : Nat} (a : Fin n → Int) (i : Nat) : Int :=
  if h : i < n then a ⟨i, h⟩ else 0

@[simp] lemma lookupNat_of_lt {n : Nat} (a : Fin n → Int) {i : Nat} (h : i < n) :
    lookupNat a i = a ⟨i, h⟩ := by
  unfold lookupNat; simp [h]

@[simp] lemma lookupNat_of_ge {n : Nat} (a : Fin n → Int) {i : Nat} (h : n ≤ i) :
    lookupNat a i = 0 := by
  unfold lookupNat; simp [Nat.not_lt.mpr h]

@[simp] lemma lookupNat_eq_apply {n : Nat} (a : Fin n → Int) (i : Fin n) :
    lookupNat a i.1 = a i := lookupNat_of_lt a i.2

def aperiodicAutocorr {n : Nat} (a : Fin n → Int) (s : Nat) : Int :=
  if s ≥ n then 0
  else ∑ i ∈ range (n - s), lookupNat a i * lookupNat a (i + s)

/-- Combined weighted autocorrelation for the Turyn quadruple at lag `s`:
    C(s) = N_X(s) + N_Y(s) + 2·N_Z(s) + 2·N_W(s) -/
def combinedAutocorr {n m : Nat} (x y z : Fin n → Int) (w : Fin m → Int) (s : Nat) : Int :=
  aperiodicAutocorr x s + aperiodicAutocorr y s +
  2 * aperiodicAutocorr z s + 2 * aperiodicAutocorr w s

/-! ### Length-indexed sequence carriers -/

/-- A length-`n` sequence with entries in `{+1, −1}`. -/
structure PmSeq (n : Nat) where
  data : Fin n → Int
  pm : AllPmOne data

/-- A length-`n` sequence with entries in `{0, +1, −1}`. -/
structure SignSeq (n : Nat) where
  data : Fin n → Int
  sign : AllSignOne data

/-- A typed Turyn quadruple TT(n).  Field names follow BDKR (X, Y, Z, W). -/
structure TurynType (n : Nat) where
  X : PmSeq n
  Y : PmSeq n
  Z : PmSeq n
  W : PmSeq (n - 1)
  vanishing : ∀ s : Nat, 1 ≤ s → s < n →
    combinedAutocorr X.data Y.data Z.data W.data s = 0

/-- Direct vanishing predicate: the four `±1` carriers form a Turyn-type
sequence iff every nonzero shift's combined autocorrelation vanishes.
This is the propositional content of `TurynType n`; see
`IsTurynType.toTyped` in `Turyn.TurynType` for the bundled form. -/
def IsTurynType {n : Nat} (X Y Z : PmSeq n) (W : PmSeq (n - 1)) : Prop :=
  ∀ s : Nat, 1 ≤ s → s < n →
    combinedAutocorr X.data Y.data Z.data W.data s = 0

namespace Turyn

/-! ### 1-indexed entry accessors

These use `Nat` indexing for source-fidelity with the BDKR paper
and return `0` when `i` is out of range. -/

/-- Entry accessor for `X` (1-indexed). -/
def xAt {n : Nat} (S : TurynType n) (i : Nat) : Int := lookupNat S.X.data (i - 1)
/-- Entry accessor for `Y` (1-indexed). -/
def yAt {n : Nat} (S : TurynType n) (i : Nat) : Int := lookupNat S.Y.data (i - 1)
/-- Entry accessor for `Z` (1-indexed). -/
def zAt {n : Nat} (S : TurynType n) (i : Nat) : Int := lookupNat S.Z.data (i - 1)
/-- Entry accessor for `W` (1-indexed). -/
def wAt {n : Nat} (S : TurynType n) (i : Nat) : Int := lookupNat S.W.data (i - 1)

/-- Pointwise X·Y product at 1-indexed position `i`. -/
def uAt {n : Nat} (S : TurynType n) (i : Nat) : Int := xAt S i * yAt S i

/-! ### Canonical conditions (BDKR §2) -/

/-- Canonical condition (1): endpoint signs.
The remaining canonical conditions `Canonical2..6` and the bundled
`Canonical` predicate are defined in `Turyn.Equivalence`; they are not
needed for the headline results in `Challenge.lean`. -/
def Canonical1 (n : Nat) (S : TurynType n) : Prop :=
  xAt S 1 = 1 ∧ xAt S n = 1 ∧
  yAt S 1 = 1 ∧ yAt S n = 1 ∧
  zAt S 1 = 1 ∧ wAt S 1 = 1

/-! ### Matrix carriers and Hadamard predicate -/

/-- Typed integer vectors indexed by `Fin n`. -/
abbrev IntVec (n : Nat) := Fin n → Int

/-- Typed square integer matrices indexed by `Fin n`. -/
abbrev IntMat (n : Nat) := Matrix (Fin n) (Fin n) Int

/-- Matrix-level Hadamard predicate: entrywise `±1` and `H · Hᵀ = n · I`. -/
def IsHadamardMat {n : Nat} (H : IntMat n) : Prop :=
  (∀ i j, H i j = 1 ∨ H i j = -1) ∧
  H * Hᵀ = (n : Int) • (1 : IntMat n)

end Turyn
