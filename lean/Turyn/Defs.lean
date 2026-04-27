import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.GetD

open Finset
open BigOperators

/-!
# Turyn.Defs

The trusted definitions named in `Challenge.lean`'s headline statements:

- `AllPmOne`, `AllSignOne` — entry-set predicates on `Fin n → Int`.
- `aperiodicAutocorr`, `combinedAutocorr` — autocorrelation primitives.
- `PmSeq n`, `SignSeq n` — length-indexed ±1 / {0, ±1} sequences
  carried as `Fin n → Int`.
- `TurynType n` — bundled TT(n) quadruple plus the vanishing identity.
- `xAt/yAt/zAt/wAt`, `uAt` — 1-indexed entry accessors.
- `Canonical1..6`, `Canonical` — BDKR canonical-form predicates.

Boolean checks, decidability, parsers, and the `IsTurynType` predicate
sit on top of these definitions in `Turyn.TurynType`.
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

/-- Canonical condition (1): endpoint signs. -/
def Canonical1 (n : Nat) (S : TurynType n) : Prop :=
  xAt S 1 = 1 ∧ xAt S n = 1 ∧
  yAt S 1 = 1 ∧ yAt S n = 1 ∧
  zAt S 1 = 1 ∧ wAt S 1 = 1

/-- Canonical condition (2) for `X`. -/
def Canonical2 (n : Nat) (S : TurynType n) : Prop :=
  ∀ i, 1 ≤ i → i ≤ n →
    (∀ j, 1 ≤ j → j < i → xAt S j = xAt S (n + 1 - j)) →
    xAt S i ≠ xAt S (n + 1 - i) →
    xAt S i = 1

/-- Canonical condition (3) for `Y`. -/
def Canonical3 (n : Nat) (S : TurynType n) : Prop :=
  ∀ i, 1 ≤ i → i ≤ n →
    (∀ j, 1 ≤ j → j < i → yAt S j = yAt S (n + 1 - j)) →
    yAt S i ≠ yAt S (n + 1 - i) →
    yAt S i = 1

/-- Canonical condition (4) for `Z`. -/
def Canonical4 (n : Nat) (S : TurynType n) : Prop :=
  ∀ i, 1 ≤ i → i ≤ n →
    (∀ j, 1 ≤ j → j < i → zAt S j ≠ zAt S (n + 1 - j)) →
    zAt S i = zAt S (n + 1 - i) →
    zAt S i = 1

/-- Canonical condition (5) for `W`. -/
def Canonical5 (n : Nat) (S : TurynType n) : Prop :=
  ∀ i, 1 ≤ i → i ≤ n - 1 →
    (∀ j, 1 ≤ j → j < i → wAt S j * wAt S (n - j) = wAt S (n - 1)) →
    wAt S i * wAt S (n - i) ≠ wAt S (n - 1) →
    wAt S i = 1

/-- Canonical condition (6): tie-breaker between `X` and `Y`. -/
def Canonical6 (n : Nat) (S : TurynType n) : Prop :=
  n ≤ 2 ∨
  ((xAt S 2 ≠ yAt S 2 ∧ xAt S 2 = 1) ∨
   (xAt S 2 = yAt S 2 ∧ xAt S (n - 1) = 1 ∧ yAt S (n - 1) = -1))

/-- Full canonical predicate. -/
def Canonical (n : Nat) (S : TurynType n) : Prop :=
  Canonical1 n S ∧ Canonical2 n S ∧ Canonical3 n S ∧
  Canonical4 n S ∧ Canonical5 n S ∧ Canonical6 n S

end Turyn
