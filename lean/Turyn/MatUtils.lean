import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Matrix
open BigOperators

/-!
# Matrix Utilities

`Fin n`-indexed integer vectors and matrices, circulants, the back-diagonal
reversal matrix, the Hadamard predicate, and small matrix lemmas used by
the Goethals-Seidel construction.
-/

namespace Turyn

/-- Typed integer vectors indexed by `Fin n`. -/
abbrev IntVec (n : Nat) := Fin n → Int

/-- Typed square integer matrices indexed by `Fin n`. -/
abbrev IntMat (n : Nat) := Matrix (Fin n) (Fin n) Int

/-- Entrywise `±1` condition for typed vectors. -/
def IsPmOneVec {n : Nat} (x : IntVec n) : Prop :=
  ∀ i, x i = 1 ∨ x i = -1

/-- Periodic autocorrelation on a typed vector. -/
def periodicAutocorr {n : Nat} (x : IntVec n) (s : Fin n) : Int :=
  ∑ i : Fin n, x i * x (i + s)

/-- The standard circulant matrix attached to a typed vector. -/
def circulant {n : Nat} (x : IntVec n) : IntMat n :=
  fun i j => x (j - i)

/-- Reversal on `Fin n`, sending `i` to `n - 1 - i`. -/
def revFin {n : Nat} (i : Fin n) : Fin n :=
  ⟨n - 1 - i.1, by
    have hi : i.1 < n := i.2
    omega⟩

@[simp] theorem revFin_val {n : Nat} (i : Fin n) :
    (revFin i).1 = n - 1 - i.1 := rfl

@[simp] theorem revFin_involutive {n : Nat} (i : Fin n) :
    revFin (revFin i) = i := by
  apply Fin.ext
  simp [revFin]
  omega

@[simp] theorem revFin_eq_iff {n : Nat} {i j : Fin n} :
    revFin i = j ↔ i = revFin j := by
  constructor
  · intro h
    calc
      i = revFin (revFin i) := by symm; exact revFin_involutive i
      _ = revFin j := by rw [h]
  · intro h
    calc
      revFin i = revFin (revFin j) := by rw [h]
      _ = j := by exact revFin_involutive j

/-- The reversal matrix `R`. -/
def reversalMatrix (n : Nat) : IntMat n :=
  fun i j => if j = revFin i then 1 else 0

@[simp] theorem reversalMatrix_apply {n : Nat} (i j : Fin n) :
    reversalMatrix n i j = if j = revFin i then 1 else 0 := rfl

theorem reversalMatrix_transpose {n : Nat} :
    (reversalMatrix n)ᵀ = reversalMatrix n := by
  ext i j
  simp only [reversalMatrix, Matrix.transpose_apply]
  by_cases hij : i = revFin j
  · have hji : j = revFin i := by
      exact ((revFin_eq_iff).mpr hij).symm
    rw [if_pos hij, if_pos hji]
  · have hji : j ≠ revFin i := by
      intro hji
      apply hij
      exact (revFin_eq_iff).mp hji.symm
    rw [if_neg hij, if_neg hji]

@[simp] theorem circulant_apply {n : Nat} (x : IntVec n) (i j : Fin n) :
    circulant x i j = x (j - i) := rfl

@[simp] theorem circulant_diag {n : Nat} [NeZero n] (x : IntVec n) (i : Fin n) :
    circulant x i i = x 0 := by
  simp [circulant]

@[simp] theorem circulant_row_zero {n : Nat} [NeZero n] (x : IntVec n) (j : Fin n) :
    circulant x 0 j = x j := by
  simp [circulant]

@[simp] theorem circulant_transpose_apply {n : Nat} (x : IntVec n) (i j : Fin n) :
    (circulant x)ᵀ i j = x (i - j) := by
  simp [circulant]

@[simp] theorem reversalMatrix_mul_apply {n : Nat} (M : IntMat n) (i j : Fin n) :
    (reversalMatrix n * M) i j = M (revFin i) j := by
  simp [Matrix.mul_apply, reversalMatrix]

@[simp] theorem mul_reversalMatrix_apply {n : Nat} (M : IntMat n) (i j : Fin n) :
    (M * reversalMatrix n) i j = M i (revFin j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (revFin j)]
  · simp [reversalMatrix]
  · intro b _ hb
    have hne : j ≠ revFin b := by
      intro h
      apply hb
      exact (revFin_eq_iff.mp h.symm)
    simp [reversalMatrix, hne]
  · simp [reversalMatrix]

theorem reversalMatrix_mul_reversalMatrix {n : Nat} :
    reversalMatrix n * reversalMatrix n = (1 : IntMat n) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single (revFin i)]
    · simp [reversalMatrix]
    · intro b _ hb
      simp [reversalMatrix, hb]
    · simp [reversalMatrix]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (revFin j)]
    · have hne : revFin j ≠ revFin i := by
        intro h
        have : j = i := by simpa using congrArg revFin h
        exact hij this.symm
      simp [reversalMatrix, hij, hne]
    · intro b _ hb
      by_cases h1 : j = revFin b
      · have hb' : b ≠ revFin j := hb
        have : b = revFin j := revFin_eq_iff.mp h1.symm
        contradiction
      · simp [reversalMatrix, h1]
    · simp [reversalMatrix]

theorem circulant_mul_transpose_apply {n : Nat} (x y : IntVec n) (i j : Fin n) :
    (circulant x * (circulant y)ᵀ) i j = ∑ k : Fin n, x (k - i) * y (k - j) := by
  simp [Matrix.mul_apply, circulant]

theorem reversal_conjugates_circulant_apply {n : Nat} (x : IntVec n) (i j : Fin n) :
    (reversalMatrix n * circulant x * reversalMatrix n) i j = x (revFin j - revFin i) := by
  rw [mul_reversalMatrix_apply]
  rw [reversalMatrix_mul_apply]
  simp [circulant]

/-- Matrix-level Hadamard predicate. -/
def IsHadamardMat {n : Nat} (H : IntMat n) : Prop :=
  (∀ i j, H i j = 1 ∨ H i j = -1) ∧
  H * Hᵀ = (n : Int) • (1 : IntMat n)

end Turyn
