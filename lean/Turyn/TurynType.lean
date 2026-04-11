import Mathlib
import Mathlib.Algebra.BigOperators.Intervals

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

/-! ### Sequences -/

/-- A ±1 sequence, represented as a `List Int` with entries restricted to {1, −1}. -/
abbrev PmSeq := List Int

/-- Convert a sign character into the corresponding `±1` value. -/
def charToPm? (c : Char) : Option Int :=
  if c = '+' then some 1
  else if c = '-' then some (-1)
  else none

/-- Parse a string of `+` and `-` characters into a `PmSeq`. -/
def pmSeq? (s : String) : Option PmSeq :=
  s.data.foldr
    (fun c acc =>
      match charToPm? c, acc with
      | some x, some xs => some (x :: xs)
      | _, _ => none)
    (some [])

/-- Parse a string literal of `+` and `-` characters into a `PmSeq`.
    Invalid characters raise an error when the definition is evaluated. -/
def pmSeq! (s : String) : PmSeq :=
  match pmSeq? s with
  | some xs => xs
  | none => panic! s!"invalid PmSeq literal: {s}"

/-- String literal notation for `PmSeq` values, e.g. `pm! "++--"`. -/
syntax "pm! " str : term

macro_rules
  | `(pm! $s:str) => `(pmSeq! $s)

/-- Check that every entry of a sequence is ±1. -/
def allPmOne (a : PmSeq) : Bool :=
  a.all fun v => v == 1 || v == -1

/-- Propositional version: every entry is 1 or −1. -/
def AllPmOne (a : PmSeq) : Prop := ∀ v ∈ a, v = 1 ∨ v = -1

/-! ### Aperiodic Autocorrelation -/

/-- Aperiodic autocorrelation of sequence `a` at lag `s`:
    N_a(s) = Σ_{i=0}^{|a|−1−s} a_i · a_{i+s}
    Returns 0 when `s ≥ |a|`. -/
def aperiodicAutocorr (a : PmSeq) (s : Nat) : Int :=
  if s ≥ a.length then 0
  else ∑ i ∈ range (a.length - s), a.getD i 0 * a.getD (i + s) 0

/-- Combined weighted autocorrelation for the Turyn quadruple at lag `s`:
    C(s) = N_X(s) + N_Y(s) + 2·N_Z(s) + 2·N_W(s) -/
def combinedAutocorr (x y z w : PmSeq) (s : Nat) : Int :=
  aperiodicAutocorr x s + aperiodicAutocorr y s +
  2 * aperiodicAutocorr z s + 2 * aperiodicAutocorr w s

/-! ### Turyn-Type Sequences (Boolean, for native_decide) -/

/-- Boolean predicate: is (x, y, z, w) a valid TT(n)? -/
def isTurynTypeBool (n : Nat) (x y z w : PmSeq) : Bool :=
  x.length == n &&
  y.length == n &&
  z.length == n &&
  w.length == (n - 1) &&
  allPmOne x &&
  allPmOne y &&
  allPmOne z &&
  allPmOne w &&
  (List.range (n - 1)).all fun i =>
    combinedAutocorr x y z w (i + 1) == 0

/-- Propositional predicate (definitionally Bool = true). -/
def IsTurynType (n : Nat) (x y z w : PmSeq) : Prop :=
  isTurynTypeBool n x y z w = true

instance (n : Nat) (x y z w : PmSeq) : Decidable (IsTurynType n x y z w) :=
  inferInstanceAs (Decidable (isTurynTypeBool n x y z w = true))

/-! ### Turyn-Type Sequences (Propositional, for general proofs) -/

/-- Propositional Turyn-type predicate with explicit hypotheses. -/
structure IsTurynTypeProp (n : Nat) (x y z w : PmSeq) : Prop where
  x_len : x.length = n
  y_len : y.length = n
  z_len : z.length = n
  w_len : w.length = n - 1
  x_pm : AllPmOne x
  y_pm : AllPmOne y
  z_pm : AllPmOne z
  w_pm : AllPmOne w
  vanishing : ∀ s : Nat, 1 ≤ s → s < n → combinedAutocorr x y z w s = 0

/-- Extract propositional form from Boolean form. -/
theorem IsTurynType.toProp {n : Nat} {x y z w : PmSeq}
    (h : IsTurynType n x y z w) : IsTurynTypeProp n x y z w := by
  unfold IsTurynType isTurynTypeBool at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hxl, hyl⟩, hzl⟩, hwl⟩, hxpm⟩, hypm⟩, hzpm⟩, hwpm⟩, hall⟩ := h
  have hxlen := eq_of_beq hxl
  have hylen := eq_of_beq hyl
  have hzlen := eq_of_beq hzl
  have hwlen := eq_of_beq hwl
  rw [List.all_eq_true] at hall
  -- Extract AllPmOne from Bool
  have hxp : AllPmOne x := by
    intro v hv
    rw [allPmOne, List.all_eq_true] at hxpm
    have := hxpm v hv
    simp [Bool.or_eq_true, beq_iff_eq] at this
    exact this
  have hyp : AllPmOne y := by
    intro v hv
    rw [allPmOne, List.all_eq_true] at hypm
    have := hypm v hv
    simp [Bool.or_eq_true, beq_iff_eq] at this
    exact this
  have hzp : AllPmOne z := by
    intro v hv
    rw [allPmOne, List.all_eq_true] at hzpm
    have := hzpm v hv
    simp [Bool.or_eq_true, beq_iff_eq] at this
    exact this
  have hwp : AllPmOne w := by
    intro v hv
    rw [allPmOne, List.all_eq_true] at hwpm
    have := hwpm v hv
    simp [Bool.or_eq_true, beq_iff_eq] at this
    exact this
  exact {
    x_len := hxlen
    y_len := hylen
    z_len := hzlen
    w_len := hwlen
    x_pm := hxp
    y_pm := hyp
    z_pm := hzp
    w_pm := hwp
    vanishing := by
      intro s hs1 hs2
      have hmem : s - 1 ∈ List.range (n - 1) := by
        rw [List.mem_range]; omega
      have := hall _ hmem
      have heq : s - 1 + 1 = s := by omega
      rw [heq] at this
      exact eq_of_beq this
  }

/-! ### Sum of a sequence -/

/-- Sum of all entries in a sequence. -/
def seqSum (a : PmSeq) : Int := ∑ i ∈ range a.length, a.getD i 0

/-! ### Convenience: structured Turyn quadruple with proofs -/

/-- A certified Turyn-type quadruple TT(n), bundling the sequences with
    a proof of validity. -/
structure TurynQuad (n : Nat) where
  x : PmSeq
  y : PmSeq
  z : PmSeq
  w : PmSeq
  valid : IsTurynType n x y z w

/-! ### ±1 lemmas -/

theorem pmone_sq (a : Int) (h : a = 1 ∨ a = -1) : a * a = 1 := by
  cases h with
  | inl h => subst h; decide
  | inr h => subst h; decide
