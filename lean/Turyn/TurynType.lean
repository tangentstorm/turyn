import Turyn.Defs
import Mathlib.Tactic

open Finset
open BigOperators

/-!
# Turyn-Type Sequences: Boolean / decidability / parsing layer

The core type-level definitions (`PmSeq`, `SignSeq`, `aperiodicAutocorr`,
`combinedAutocorr`, `TurynType`) live in `Turyn.Defs`.  This file
adds the Boolean and decidability machinery, the `pm! "..."` string
literal parser, and the `IsTurynType` predicate / typed bridge used
throughout the rest of the project.
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

/-! ### Boolean / decidable layer for `AllPmOne` and `AllSignOne` -/

/-- Boolean check that every entry of a sequence is ±1. -/
def allPmOne (a : List Int) : Bool :=
  a.all fun v => v == 1 || v == -1

theorem allPmOne_iff (a : List Int) : allPmOne a = true ↔ AllPmOne a := by
  simp [allPmOne, AllPmOne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq]

instance (a : List Int) : Decidable (AllPmOne a) :=
  decidable_of_iff _ (allPmOne_iff a)

/-- Boolean check that every entry of a sequence is `0`, `1`, or `−1`. -/
def allSignOne (a : List Int) : Bool :=
  a.all fun v => v == 0 || v == 1 || v == -1

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

/-! ### Cross-sequence lift -/

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
