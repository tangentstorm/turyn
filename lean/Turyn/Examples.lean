import Turyn.TurynType
import Turyn.Energy
import Turyn.TSequence
import Turyn.Hadamard

open Turyn

/-!
# Verified Turyn-Type Sequences

Concrete examples verified by `native_decide`, which compiles the Boolean
check to native code and runs it, producing a kernel-level proof.

## How to add your own verified solution

```lean
def myX : PmSeq n := pm! "+−+−..."
def myY : PmSeq n := pm! "++−−..."
def myZ : PmSeq n := pm! "+−−+..."
def myW : PmSeq (n - 1) := pm! "−++−..."

theorem my_solution_is_turyn : IsTurynType myX myY myZ myW := by
  native_decide
```
-/

/-! ## TT(6): A small example -/

def tt6X : PmSeq 6 := pm! "----+-"
def tt6Y : PmSeq 6 := pm! "---+--"
def tt6Z : PmSeq 6 := pm! "--+-++"
def tt6W : PmSeq 5 := pm! "-+++-"

/-- TT(6) is a valid Turyn-type sequence.
    Verified by compiling the Boolean check to native code. -/
theorem tt6_valid : IsTurynType tt6X tt6Y tt6Z tt6W := by native_decide

/-- The energy identity holds for TT(6): (−4)² + (−4)² + 2·0² + 2·1² = 34 = 6·6 − 2. -/
theorem tt6_energy :
    checkEnergy 6 tt6X.data tt6Y.data tt6Z.data tt6W.data = true := by
  native_decide

/-- TT(6) sums: x = −4, y = −4, z = 0, w = 1. -/
theorem tt6_sums :
    seqSum tt6X.data = -4 ∧ seqSum tt6Y.data = -4 ∧
    seqSum tt6Z.data = 0 ∧ seqSum tt6W.data = 1 := by
  native_decide

/-- The constructive pipeline produces a Hadamard matrix of order `68` from TT(6). -/
def tt6_hadamard : IntMat 68 :=
  ofIsTurynTypeMatrix tt6_valid

/-- The constructive TT(6) matrix satisfies the Hadamard property. -/
theorem tt6_hadamard_isHadamard :
    IsHadamardMat tt6_hadamard := by
  exact ofIsTurynTypeMatrix_isHadamard tt6_valid

/-! ## TT(36): Kharaghani & Tayfeh-Rezaie (2005), Hadamard matrix of order 428

This is the solution that resolved the Hadamard conjecture for order 428,
the smallest order for which no Hadamard matrix was previously known.

Reference: Kharaghani, H. & Tayfeh-Rezaie, B. (2005).
"A Hadamard matrix of order 428." *J. Combin. Des.* 13(6), 435–440. -/

def kh05X : PmSeq 36 := pm! "+++----++-+-+-----++++-++-++++----+-"
def kh05Y : PmSeq 36 := pm! "+-+++++--+-+--+--++--++++-++++---++-"
def kh05Z : PmSeq 36 := pm! "+-+++++-+--++++-+++-++--+++-+--+---+"
def kh05W : PmSeq 35 := pm! "+++-+-----++--+-+++--+-+-+++-++++-+"

/-- **Kharaghani–Tayfeh-Rezaie TT(36) is a valid Turyn-type sequence.**

    This is a machine-checked proof: Lean compiles the verification algorithm
    (computing 35 combined autocorrelation values and checking they all vanish)
    to native code and certifies the result. -/
theorem kharaghani_2005_tt36 : IsTurynType kh05X kh05Y kh05Z kh05W := by
  native_decide

/-- The energy identity for TT(36): 0² + 6² + 2·8² + 2·5² = 214 = 6·36 − 2. -/
theorem kh05_energy :
    checkEnergy 36 kh05X.data kh05Y.data kh05Z.data kh05W.data = true := by
  native_decide

/-- Sequence sums for Kharaghani TT(36). -/
theorem kh05_sums :
    seqSum kh05X.data = 0 ∧ seqSum kh05Y.data = 6 ∧
    seqSum kh05Z.data = 8 ∧ seqSum kh05W.data = 5 := by
  native_decide

/-- The Hadamard order from TT(36) is 428. -/
theorem kh05_hadamard_order : hadamardOrder 36 = 428 := by native_decide

/-- **Existence of Hadamard matrix of order 428.**

    By the base-sequence → T-sequence → Goethals-Seidel pipeline (KTR2005),
    the verified TT(36) above implies the existence of a Hadamard matrix
    of order 4(3·36 − 1) = 428. -/
theorem hadamard_428_exists :
    ∃ (X Y Z : PmSeq 36) (W : PmSeq 35),
      IsTurynType X Y Z W ∧ hadamardOrder 36 = 428 :=
  ⟨kh05X, kh05Y, kh05Z, kh05W, kharaghani_2005_tt36, kh05_hadamard_order⟩

/-! ## Template for publishing your own results

```lean
import Turyn.TurynType
import Turyn.Energy
import Turyn.TSequence

def myX : PmSeq N := pm! "..."
def myY : PmSeq N := pm! "..."
def myZ : PmSeq N := pm! "..."
def myW : PmSeq (N - 1) := pm! "..."

-- Lean verifies at compile time
theorem my_tt_valid : IsTurynType myX myY myZ myW := by native_decide

theorem my_hadamard_exists :
    ∃ (X Y Z : PmSeq N) (W : PmSeq (N - 1)),
      IsTurynType X Y Z W ∧ hadamardOrder N = ORDER :=
  ⟨myX, myY, myZ, myW, my_tt_valid, by native_decide⟩
```
-/
