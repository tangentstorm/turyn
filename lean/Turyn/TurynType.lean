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

/-! ### List-based predicates and Boolean / decidable layer -/

/-- Propositional check that every entry of a `List Int` is `±1`. -/
def AllPmOneList (a : List Int) : Prop := ∀ v ∈ a, v = 1 ∨ v = -1

/-- Propositional check that every entry of a `List Int` is `0`, `1`, or `−1`. -/
def AllSignOneList (a : List Int) : Prop := ∀ v ∈ a, v = 0 ∨ v = 1 ∨ v = -1

/-- Boolean check that every entry of a list is ±1. -/
def allPmOne (a : List Int) : Bool :=
  a.all fun v => v == 1 || v == -1

theorem allPmOne_iff (a : List Int) : allPmOne a = true ↔ AllPmOneList a := by
  simp [allPmOne, AllPmOneList, List.all_eq_true, Bool.or_eq_true, beq_iff_eq]

instance (a : List Int) : Decidable (AllPmOneList a) :=
  decidable_of_iff _ (allPmOne_iff a)

/-- Boolean check that every entry of a list is `0`, `1`, or `−1`. -/
def allSignOne (a : List Int) : Bool :=
  a.all fun v => v == 0 || v == 1 || v == -1

theorem allSignOne_iff (a : List Int) : allSignOne a = true ↔ AllSignOneList a := by
  simp only [allSignOne, AllSignOneList, List.all_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · intro h v hv
    have := h v hv
    tauto
  · intro h v hv
    have := h v hv
    tauto

instance (a : List Int) : Decidable (AllSignOneList a) :=
  decidable_of_iff _ (allSignOne_iff a)

/-! ### Constructing a `PmSeq` / `SignSeq` from a list -/

/-- Function view of a `List Int` as a `Fin n → Int` (default `0` out of range). -/
def listToFin (l : List Int) (n : Nat) : Fin n → Int :=
  fun i => l.getD i.1 0

/-- Construct a `PmSeq n` from a list of length `n` of ±1 values. -/
def PmSeq.ofList (l : List Int) {n : Nat} (hlen : l.length = n) (hpm : AllPmOneList l) :
    PmSeq n :=
  { data := listToFin l n
    pm := by
      intro i
      have hi : i.1 < l.length := by rw [hlen]; exact i.2
      have hmem : l.getD i.1 0 ∈ l := by
        rw [List.getD_eq_getElem _ _ hi]
        exact List.getElem_mem hi
      exact hpm _ hmem }

/-- Construct a `SignSeq n` from a list of length `n` of `{0,±1}` values. -/
def SignSeq.ofList (l : List Int) {n : Nat} (hlen : l.length = n) (hsign : AllSignOneList l) :
    SignSeq n :=
  { data := listToFin l n
    sign := by
      intro i
      have hi : i.1 < l.length := by rw [hlen]; exact i.2
      have hmem : l.getD i.1 0 ∈ l := by
        rw [List.getD_eq_getElem _ _ hi]
        exact List.getElem_mem hi
      exact hsign _ hmem }

/-- Decidability instance: a `List Int` is all `±1`, decided by length-based check. -/
instance {n : Nat} (l : List Int) (h : l.length = n) :
    Decidable (AllPmOneList l) := by infer_instance

/-! ### Cross-sequence lift -/

/-- Every `±1` sequence is also a `{0, ±1}` sequence. -/
def PmSeq.toSign {n : Nat} (s : PmSeq n) : SignSeq n :=
  { data := s.data
    sign := fun i => Or.inr (s.pm i) }

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

/-- Sum of all entries of a function-typed sequence. -/
def seqSum {n : Nat} (a : Fin n → Int) : Int := ∑ i : Fin n, a i

/-- Sum of all entries in a `List Int` sequence. -/
def seqSumList (a : List Int) : Int := ∑ i ∈ range a.length, a.getD i 0

/-! ### ±1 lemmas -/

theorem pmone_sq (a : Int) (h : a = 1 ∨ a = -1) : a * a = 1 := by
  cases h with
  | inl h => subst h; decide
  | inr h => subst h; decide
