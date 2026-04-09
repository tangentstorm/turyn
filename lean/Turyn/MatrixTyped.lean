import Mathlib

open Matrix
open BigOperators

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

/-- Matrix-level Hadamard predicate. -/
def IsHadamardMat {n : Nat} (H : IntMat n) : Prop :=
  (∀ i j, H i j = 1 ∨ H i j = -1) ∧
  H * Hᵀ = (n : Int) • (1 : IntMat n)

end Turyn
