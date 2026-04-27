import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open Finset
open BigOperators

/-!
# Turyn-Type Sequences: Core Definitions

Formal definitions for Turyn-type sequences (TT(n)) and decidable verification.

A **Turyn-type sequence** TT(n) is a quadruple (X, Y, Z, W) of {+1, −1} sequences
with lengths (n, n, n, n−1) whose combined aperiodic autocorrelations vanish at
every nonzero shift:

  N_X(s) + N_Y(s) + 2·N_Z(s) + 2·N_W(s) = 0    for s = 1, …, n−1
-/

/-! ### Sign-character parsing -/

/-- Convert a sign character into the corresponding `±1` value. -/
def charToPm? (c : Char) : Option Int :=
  if c = '+' then some 1
  else if c = '-' then some (-1)
  else none

/-- Parse a string of `+` and `-` characters into a `List Int`. -/
def pmSeq? (s : String) : Option (List Int) :=
  s.toList.foldr
    (fun c acc =>
      match charToPm? c, acc with
      | some x, some xs => some (x :: xs)
      | _, _ => none)
    (some [])

/-- Parse a string literal of `+` and `-` characters into a `List Int`.
    Invalid characters raise an error when the definition is evaluated. -/
def pmSeq! (s : String) : List Int :=
  match pmSeq? s with
  | some xs => xs
  | none => panic! s!"invalid ±1 literal: {s}"

/-- String literal notation for ±1 sequences, e.g. `pm! "++--"`. -/
syntax "pm! " str : term

macro_rules
  | `(pm! $s:str) => `(pmSeq! $s)

/-! ### Entry-set predicates -/

/-- Boolean check that every entry of a sequence is ±1. -/
def allPmOne (a : List Int) : Bool :=
  a.all fun v => v == 1 || v == -1

/-- Propositional version: every entry is `1` or `−1`. -/
def AllPmOne (a : List Int) : Prop := ∀ v ∈ a, v = 1 ∨ v = -1

theorem allPmOne_iff (a : List Int) : allPmOne a = true ↔ AllPmOne a := by
  simp [allPmOne, AllPmOne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq]

instance (a : List Int) : Decidable (AllPmOne a) :=
  decidable_of_iff _ (allPmOne_iff a)

/-- Boolean check that every entry of a sequence is `0`, `1`, or `−1`. -/
def allSignOne (a : List Int) : Bool :=
  a.all fun v => v == 0 || v == 1 || v == -1

/-- Propositional version: every entry is `0`, `1`, or `−1`. -/
def AllSignOne (a : List Int) : Prop := ∀ v ∈ a, v = 0 ∨ v = 1 ∨ v = -1

theorem allSignOne_iff (a : List Int) : allSignOne a = true ↔ AllSignOne a := by
  simp only [allSignOne, AllSignOne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · intro h v hv
    have := h v hv
    tauto
  · intro h v hv
    have := h v hv
    tauto

instance (a : List Int) : Decidable (AllSignOne a) :=
  decidable_of_iff _ (allSignOne_iff a)

/-! ### Aperiodic Autocorrelation -/

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

/-! ### Length-indexed sequence types -/

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

/-- Every `±1` sequence is also a `{0, ±1}` sequence. -/
def PmSeq.toSign {n : Nat} (s : PmSeq n) : SignSeq n :=
  { data := s.data
    len := s.len
    sign := fun v hv => Or.inr (s.pm v hv) }

/-! ### Turyn-Type Sequences -/

/-- Boolean predicate: are `(X, Y, Z, W)` a valid TT(n)?
    Lengths and ±1-ness are guaranteed by the typed carriers, so the
    Boolean check only verifies that combined autocorrelations vanish. -/
def isTurynTypeBool {n : Nat} (X Y Z : PmSeq n) (W : PmSeq (n - 1)) : Bool :=
  (List.range (n - 1)).all fun i =>
    combinedAutocorr X.data Y.data Z.data W.data (i + 1) == 0

/-- Propositional Turyn-type predicate on length-indexed `PmSeq` carriers. -/
def IsTurynType {n : Nat} (X Y Z : PmSeq n) (W : PmSeq (n - 1)) : Prop :=
  isTurynTypeBool X Y Z W = true

instance {n : Nat} (X Y Z : PmSeq n) (W : PmSeq (n - 1)) :
    Decidable (IsTurynType X Y Z W) :=
  inferInstanceAs (Decidable (isTurynTypeBool X Y Z W = true))

/-- Direct vanishing form: unfolds the boolean check into a quantifier over
    nonzero shifts.  Useful when consuming an `IsTurynType` proof. -/
theorem IsTurynType.vanishing {n : Nat} {X Y Z : PmSeq n} {W : PmSeq (n - 1)}
    (h : IsTurynType X Y Z W) :
    ∀ s : Nat, 1 ≤ s → s < n →
      combinedAutocorr X.data Y.data Z.data W.data s = 0 := by
  unfold IsTurynType isTurynTypeBool at h
  rw [List.all_eq_true] at h
  intro s hs1 hs2
  have hmem : s - 1 ∈ List.range (n - 1) := by rw [List.mem_range]; omega
  have hk := h _ hmem
  have heq : s - 1 + 1 = s := by omega
  rw [heq] at hk
  exact eq_of_beq hk

/-! ### Bundled Turyn-type quadruple -/

/-- A typed Turyn quadruple TT(n).  Field names follow BDKR (X, Y, Z, W). -/
structure TurynType (n : Nat) where
  X : PmSeq n
  Y : PmSeq n
  Z : PmSeq n
  W : PmSeq (n - 1)
  vanishing : ∀ s : Nat, 1 ≤ s → s < n →
    combinedAutocorr X.data Y.data Z.data W.data s = 0

/-- Convert a typed `IsTurynType` certificate into the bundled `TurynType`. -/
def IsTurynType.toTyped {n : Nat} {X Y Z : PmSeq n} {W : PmSeq (n - 1)}
    (h : IsTurynType X Y Z W) : TurynType n :=
  { X := X, Y := Y, Z := Z, W := W, vanishing := h.vanishing }

/-! ### Sum of a sequence -/

/-- Sum of all entries in a sequence. -/
def seqSum (a : List Int) : Int := ∑ i ∈ range a.length, a.getD i 0

/-! ### ±1 lemmas -/

theorem pmone_sq (a : Int) (h : a = 1 ∨ a = -1) : a * a = 1 := by
  cases h with
  | inl h => subst h; decide
  | inr h => subst h; decide
