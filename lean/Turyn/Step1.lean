import Turyn.Basic

/-!
# Step 1: Typed Turyn Data and Base Sequences

This file is standalone and does not depend on `Turyn.Hadamard`.
It introduces typed wrappers for signed sequences and Turyn quadruples.
-/

/-- A length-indexed `±1` sequence. -/
structure SignedSeq (n : Nat) where
  data : List Int
  len : data.length = n
  pm : AllPmOne data

/-- A typed Turyn quadruple TT(n). -/
structure TurynType (n : Nat) where
  x : SignedSeq n
  y : SignedSeq n
  z : SignedSeq n
  w : SignedSeq (n - 1)
  vanishing : ∀ s : Nat, 1 ≤ s → s < n →
    combinedAutocorr x.data y.data z.data w.data s = 0

/-- Convert an existing propositional TT witness into the typed wrapper. -/
def IsTurynTypeProp.toTyped {n : Nat} {x y z w : PmSeq}
    (h : IsTurynTypeProp n x y z w) : TurynType n :=
  { x := ⟨x, h.x_len, h.x_pm⟩
    y := ⟨y, h.y_len, h.y_pm⟩
    z := ⟨z, h.z_len, h.z_pm⟩
    w := ⟨w, h.w_len, h.w_pm⟩
    vanishing := h.vanishing }

/-- Convert a Boolean-style TT certificate into the typed wrapper. -/
def IsTurynType.toTyped {n : Nat} {x y z w : PmSeq}
    (h : IsTurynType n x y z w) : TurynType n :=
  (IsTurynType.toProp h).toTyped

/-- Negate every entry in a sequence. -/
def negSeq (a : List Int) : List Int := a.map (· * (-1))

/-- Typed base-sequence data for Step 1. -/
structure BaseSeqData (n : Nat) where
  a : SignedSeq (2 * n - 1)
  b : SignedSeq (2 * n - 1)
  c : SignedSeq n
  d : SignedSeq n
  vanishing : ∀ s : Nat, 1 ≤ s →
    aperiodicAutocorr a.data s + aperiodicAutocorr b.data s +
    aperiodicAutocorr c.data s + aperiodicAutocorr d.data s = 0

/-- Step 1 interface: every typed Turyn quadruple yields typed base sequences. -/
axiom step1 {n : Nat} (T : TurynType n) : BaseSeqData n
