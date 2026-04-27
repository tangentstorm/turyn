import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.GetD

open Finset
open BigOperators

/-!
# Turyn.Defs: Core sequence and quadruple definitions

This file holds the foundational definitions used throughout the Turyn
library and named in `Results.lean`'s headline statements:

- `AllPmOne` / `AllSignOne` — propositional ±1 / {0, ±1} predicates on lists.
- `aperiodicAutocorr`, `combinedAutocorr` — autocorrelation primitives.
- `PmSeq n` — length-`n` sequence with ±1 entries.
- `SignSeq n` — length-`n` sequence with {0, ±1} entries.
- `TurynType n` — bundled TT(n) quadruple with the vanishing identity.

These five (plus the two carrier predicates) are defined here so the
trusted base for the comparator challenge module is concentrated in one
place.  The Boolean / decidable / parser / bridging machinery built on
top of these definitions lives in `Turyn.TurynType` (which imports this
file).
-/

/-- Propositional version: every entry is `1` or `−1`. -/
def AllPmOne (a : List Int) : Prop := ∀ v ∈ a, v = 1 ∨ v = -1

/-- Propositional version: every entry is `0`, `1`, or `−1`. -/
def AllSignOne (a : List Int) : Prop := ∀ v ∈ a, v = 0 ∨ v = 1 ∨ v = -1

/-- Aperiodic autocorrelation of sequence `a` at lag `s`:
    N_a(s) = Σ_{i=0}^{|a|−1−s} a_i · a_{i+s}
    Returns `0` when `s ≥ |a|`. -/
def aperiodicAutocorr (a : List Int) (s : Nat) : Int :=
  if s ≥ a.length then 0
  else ∑ i ∈ range (a.length - s), a.getD i 0 * a.getD (i + s) 0

/-- Combined weighted autocorrelation for the Turyn quadruple at lag `s`:
    C(s) = N_X(s) + N_Y(s) + 2·N_Z(s) + 2·N_W(s) -/
def combinedAutocorr (x y z w : List Int) (s : Nat) : Int :=
  aperiodicAutocorr x s + aperiodicAutocorr y s +
  2 * aperiodicAutocorr z s + 2 * aperiodicAutocorr w s

/-- A length-`n` sequence with entries in `{+1, −1}`. -/
structure PmSeq (n : Nat) where
  data : List Int
  len : data.length = n
  pm : AllPmOne data

/-- A length-`n` sequence with entries in `{0, +1, −1}`. -/
structure SignSeq (n : Nat) where
  data : List Int
  len : data.length = n
  sign : AllSignOne data

/-- A typed Turyn quadruple TT(n).  Field names follow BDKR (X, Y, Z, W). -/
structure TurynType (n : Nat) where
  X : PmSeq n
  Y : PmSeq n
  Z : PmSeq n
  W : PmSeq (n - 1)
  vanishing : ∀ s : Nat, 1 ≤ s → s < n →
    combinedAutocorr X.data Y.data Z.data W.data s = 0
