/-!
# Turyn-Type Sequences: Core Definitions

Formal definitions for Turyn-type sequences (TT(n)) and decidable verification.

A **Turyn-type sequence** TT(n) is a quadruple (X, Y, Z, W) of {+1, −1} sequences
with lengths (n, n, n, n−1) whose combined aperiodic autocorrelations vanish at
every nonzero shift:

  N_X(s) + N_Y(s) + 2·N_Z(s) + 2·N_W(s) = 0    for s = 1, …, n−1

## References

- Best, Djokovic, Kharaghani, Ramp (2013). *Turyn-Type Sequences: Classification,
  Enumeration and Construction.* arXiv:1206.4107
- Kharaghani & Tayfeh-Rezaie (2005). *A Hadamard matrix of order 428.*
  J. Combin. Des. 13(6), 435–440.
-/

/-! ### Sequences -/

/-- A ±1 sequence, represented as a `List Int` with entries restricted to {1, −1}. -/
abbrev Seq := List Int

/-- Check that every entry of a sequence is ±1. -/
def allPmOne (a : Seq) : Bool :=
  a.all fun v => v == 1 || v == -1

/-- Propositional version: every entry is 1 or −1. -/
def AllPmOne (a : Seq) : Prop := ∀ v ∈ a, v = 1 ∨ v = -1

/-! ### Aperiodic Autocorrelation -/

/-- Aperiodic autocorrelation of sequence `a` at lag `s`:

    N_a(s) = Σ_{i=0}^{|a|−1−s} a_i · a_{i+s}

Returns 0 when `s ≥ |a|`. -/
def aperiodicAutocorr (a : Seq) (s : Nat) : Int :=
  if s ≥ a.length then 0
  else
    let stop := a.length - s
    (List.range stop).foldl (fun acc i =>
      acc + a.getD i 0 * a.getD (i + s) 0) 0

/-- Combined weighted autocorrelation for the Turyn quadruple at lag `s`:

    C(s) = N_X(s) + N_Y(s) + 2·N_Z(s) + 2·N_W(s) -/
def combinedAutocorr (x y z w : Seq) (s : Nat) : Int :=
  aperiodicAutocorr x s + aperiodicAutocorr y s +
  2 * aperiodicAutocorr z s + 2 * aperiodicAutocorr w s

/-! ### Turyn-Type Sequences -/

/-- Boolean predicate: is (x, y, z, w) a valid TT(n)?

Checks:
1. Lengths are (n, n, n, n−1)
2. All entries are ±1
3. Combined autocorrelation vanishes for every shift s ∈ {1, …, n−1} -/
def isTurynTypeBool (n : Nat) (x y z w : Seq) : Bool :=
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

/-- Propositional predicate: (x, y, z, w) is a valid Turyn-type sequence TT(n).

This is definitionally equal to `isTurynTypeBool n x y z w = true`,
making it decidable by `native_decide`. -/
def IsTurynType (n : Nat) (x y z w : Seq) : Prop :=
  isTurynTypeBool n x y z w = true

instance (n : Nat) (x y z w : Seq) : Decidable (IsTurynType n x y z w) :=
  inferInstanceAs (Decidable (isTurynTypeBool n x y z w = true))

/-! ### Sum of a sequence -/

/-- Sum of all entries in a sequence. -/
def seqSum (a : Seq) : Int := a.foldl (· + ·) 0

/-! ### Convenience: structured Turyn quadruple with proofs -/

/-- A certified Turyn-type quadruple TT(n), bundling the sequences with
    a proof of validity. -/
structure TurynQuad (n : Nat) where
  x : Seq
  y : Seq
  z : Seq
  w : Seq
  valid : IsTurynType n x y z w
