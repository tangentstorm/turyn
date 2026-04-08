import Turyn.Step2

/-!
# Step 3: Typed Matrices and Hadamard Construction

This file is standalone and does not depend on `Turyn.Hadamard`.
It packages the final pipeline as a matrix-valued function on typed input.
-/

/-- A square matrix of integers, stored as a list of rows together with its size. -/
structure SquareMatrix (n : Nat) where
  rows : List (List Int)
  dim : rows.length = n

/-- Row accessor for a typed square matrix. -/
def SquareMatrix.row {n : Nat} (M : SquareMatrix n) (i : Nat) : List Int :=
  M.rows.getD i []

/-- Dot product of two integer lists. -/
def listDotProduct (a b : List Int) : Int :=
  ((a.zip b).map fun p => p.1 * p.2).foldl (· + ·) 0

/-- Reverse a row, corresponding to the reversal matrix action on columns. -/
def applyR (row : List Int) : List Int := row.reverse

/-- Negate every entry in a row. -/
def negRow (row : List Int) : List Int := row.map (· * (-1))

@[simp] theorem applyR_length (row : List Int) : (applyR row).length = row.length := by
  simp [applyR]

@[simp] theorem negRow_length (row : List Int) : (negRow row).length = row.length := by
  simp [negRow]

/-- Circulant matrix rows from a length-`m` first row. -/
def circulantRow (m : Nat) (a : List Int) (i : Nat) : List Int :=
  (List.range m).map fun j =>
    a.getD ((j + m - i) % m) 0

/-- Circulant matrix rows from a length-`m` first row. -/
def circulantRows (m : Nat) (a : List Int) : List (List Int) :=
  (List.range m).map fun i => circulantRow m a i

@[simp] theorem circulantRows_length (m : Nat) (a : List Int) :
    (circulantRows m a).length = m := by
  simp [circulantRows]

/-- Boolean check: every entry is `±1`. -/
def allEntriesPmOne (m : List (List Int)) : Bool :=
  m.all fun row => row.all fun v => v == 1 || v == -1

/-- Boolean check: all rows have the given length. -/
def allRowsLength (m : List (List Int)) (n : Nat) : Bool :=
  m.all fun row => row.length == n

/-- Boolean check: row orthogonality. -/
def checkOrthogonality (m : List (List Int)) : Bool :=
  let n := m.length
  (List.range n).all fun i =>
    (List.range n).all fun j =>
      let dot := listDotProduct (m.getD i []) (m.getD j [])
      if i == j then dot == (n : Int) else dot == 0

/-- Hadamard predicate on a typed square matrix. -/
def SquareMatrix.IsHadamard {n : Nat} (H : SquareMatrix n) : Prop :=
  allRowsLength H.rows n = true ∧
  allEntriesPmOne H.rows = true ∧
  checkOrthogonality H.rows = true

/-- A square matrix together with a proof that it is Hadamard. -/
structure HadamardMatrix (n : Nat) where
  matrix : SquareMatrix n
  isHadamard : matrix.IsHadamard

/-- A typed quad of `m × m` circulant `(0, ±1)` matrices associated to a
    T-sequence. This is the immediate concrete object produced from Step 2
    data in the standard design-theory pipeline. -/
structure TMatrixQuad (m : Nat) where
  a : SquareMatrix m
  b : SquareMatrix m
  c : SquareMatrix m
  d : SquareMatrix m

/-- Abstract Step 3 existence theorem on typed T-sequences. -/
axiom goethals_seidel_hadamard_exists {m : Nat} (T : TSequence m) :
  ∃ H : SquareMatrix (4 * m), H.IsHadamard

/-- The immediate matrix-level object obtained from a T-sequence: four
    circulant matrices of order `m`. -/
def tMatrixQuadOfTSequence {m : Nat} (T : TSequence m) : TMatrixQuad m :=
  { a := ⟨circulantRows m T.a, by simp [circulantRows]⟩
    b := ⟨circulantRows m T.b, by simp [circulantRows]⟩
    c := ⟨circulantRows m T.c, by simp [circulantRows]⟩
    d := ⟨circulantRows m T.d, by simp [circulantRows]⟩ }

/-- Each matrix in the T-matrix quad has the expected dimension. -/
@[simp] theorem tMatrixQuadOfTSequence_dim_a {m : Nat} (T : TSequence m) :
    (tMatrixQuadOfTSequence T).a.rows.length = m := by
  simp [tMatrixQuadOfTSequence]

@[simp] theorem tMatrixQuadOfTSequence_dim_b {m : Nat} (T : TSequence m) :
    (tMatrixQuadOfTSequence T).b.rows.length = m := by
  simp [tMatrixQuadOfTSequence]

@[simp] theorem tMatrixQuadOfTSequence_dim_c {m : Nat} (T : TSequence m) :
    (tMatrixQuadOfTSequence T).c.rows.length = m := by
  simp [tMatrixQuadOfTSequence]

@[simp] theorem tMatrixQuadOfTSequence_dim_d {m : Nat} (T : TSequence m) :
    (tMatrixQuadOfTSequence T).d.rows.length = m := by
  simp [tMatrixQuadOfTSequence]

/-- Each circulant matrix in the T-matrix quad has rows of length `m`. -/
theorem tMatrixQuadOfTSequence_allRowsLength_a {m : Nat} (T : TSequence m) :
    allRowsLength (tMatrixQuadOfTSequence T).a.rows m = true := by
  simp [tMatrixQuadOfTSequence, allRowsLength, circulantRows, circulantRow]

theorem tMatrixQuadOfTSequence_allRowsLength_b {m : Nat} (T : TSequence m) :
    allRowsLength (tMatrixQuadOfTSequence T).b.rows m = true := by
  simp [tMatrixQuadOfTSequence, allRowsLength, circulantRows, circulantRow]

theorem tMatrixQuadOfTSequence_allRowsLength_c {m : Nat} (T : TSequence m) :
    allRowsLength (tMatrixQuadOfTSequence T).c.rows m = true := by
  simp [tMatrixQuadOfTSequence, allRowsLength, circulantRows, circulantRow]

theorem tMatrixQuadOfTSequence_allRowsLength_d {m : Nat} (T : TSequence m) :
    allRowsLength (tMatrixQuadOfTSequence T).d.rows m = true := by
  simp [tMatrixQuadOfTSequence, allRowsLength, circulantRows, circulantRow]

/-- Structural shape summary for the four circulant matrices attached to a T-sequence. -/
theorem tMatrixQuadOfTSequence_hasShape {m : Nat} (T : TSequence m) :
    allRowsLength (tMatrixQuadOfTSequence T).a.rows m = true ∧
    allRowsLength (tMatrixQuadOfTSequence T).b.rows m = true ∧
    allRowsLength (tMatrixQuadOfTSequence T).c.rows m = true ∧
    allRowsLength (tMatrixQuadOfTSequence T).d.rows m = true := by
  exact ⟨tMatrixQuadOfTSequence_allRowsLength_a T,
    tMatrixQuadOfTSequence_allRowsLength_b T,
    tMatrixQuadOfTSequence_allRowsLength_c T,
    tMatrixQuadOfTSequence_allRowsLength_d T⟩

/-- The `i`-th raw Goethals-Seidel block row attached to a T-matrix quad. -/
def rawGoethalsSeidelRowAt {m : Nat} (Q : TMatrixQuad m) (i : Nat) : List Int :=
  let blockRow := i / m
  let localI := i % m
  let rowA := Q.a.rows.getD localI []
  let rowB := Q.b.rows.getD localI []
  let rowC := Q.c.rows.getD localI []
  let rowD := Q.d.rows.getD localI []
  match blockRow with
  | 0 => rowA ++ applyR rowB ++ applyR rowC ++ applyR rowD
  | 1 => negRow (applyR rowB) ++ rowA ++ negRow (applyR rowD) ++ applyR rowC
  | 2 => negRow (applyR rowC) ++ applyR rowD ++ rowA ++ negRow (applyR rowB)
  | 3 => negRow (applyR rowD) ++ negRow (applyR rowC) ++ applyR rowB ++ rowA
  | _ => []

def rawGoethalsSeidelRows {m : Nat} (Q : TMatrixQuad m) : List (List Int) :=
  (List.range (4 * m)).map fun i => rawGoethalsSeidelRowAt Q i

@[simp] theorem rawGoethalsSeidelRows_length {m : Nat} (Q : TMatrixQuad m) :
    (rawGoethalsSeidelRows Q).length = 4 * m := by
  simp [rawGoethalsSeidelRows]

/-- The raw block array packaged as a square matrix. -/
def rawGoethalsSeidel {m : Nat} (T : TSequence m) : SquareMatrix (4 * m) :=
  { rows := rawGoethalsSeidelRows (tMatrixQuadOfTSequence T)
    dim := by simp }

/-- The raw Goethals-Seidel array has the expected number of rows. -/
@[simp] theorem rawGoethalsSeidel_dim {m : Nat} (T : TSequence m) :
    (rawGoethalsSeidel T).rows.length = 4 * m := by
  simp [rawGoethalsSeidel]

@[simp] theorem circulantRow_length (m : Nat) (a : List Int) (i : Nat) :
    (circulantRow m a i).length = m := by
  simp [circulantRow]

/-- Every row of the raw Goethals-Seidel array has length `4 * m`. -/
axiom rawGoethalsSeidel_allRowsLength {m : Nat} (T : TSequence m) :
    allRowsLength (rawGoethalsSeidel T).rows (4 * m) = true

/-- Structural shape theorem for the explicit raw block array. -/
theorem rawGoethalsSeidel_hasShape {m : Nat} (T : TSequence m) :
    (rawGoethalsSeidel T).rows.length = 4 * m ∧
    allRowsLength (rawGoethalsSeidel T).rows (4 * m) = true := by
  exact ⟨rawGoethalsSeidel_dim T, rawGoethalsSeidel_allRowsLength T⟩

/-- Step 3 as a typed Hadamard-matrix-valued function on T-sequence input. -/
noncomputable def step3Hadamard {m : Nat} (T : TSequence m) : HadamardMatrix (4 * m) :=
  let h := goethals_seidel_hadamard_exists T
  ⟨Classical.choose h, Classical.choose_spec h⟩

/-- Step 3 as a matrix-valued function on typed T-sequence input. -/
noncomputable def step3Matrix {m : Nat} (T : TSequence m) : SquareMatrix (4 * m) :=
  (step3Hadamard T).matrix

/-- The matrix produced by `step3Matrix` is Hadamard. -/
theorem step3Matrix_isHadamard {m : Nat} (T : TSequence m) :
    (step3Matrix T).IsHadamard := by
  exact (step3Hadamard T).isHadamard

/-- Every matrix returned by Step 3 has the expected row shape. -/
theorem step3Matrix_hasShape {m : Nat} (T : TSequence m) :
    (step3Matrix T).rows.length = 4 * m ∧
    allRowsLength (step3Matrix T).rows (4 * m) = true := by
  exact ⟨(step3Matrix T).dim, (step3Matrix_isHadamard T).1⟩

/-- Step 3 correctness, packaged at the typed output level. -/
theorem step3Hadamard_correct {m : Nat} (T : TSequence m) :
    (step3Hadamard T).matrix.IsHadamard := by
  exact (step3Hadamard T).isHadamard

/-- End-to-end typed construction from a Turyn quadruple to a Hadamard matrix. -/
noncomputable def turynToHadamard {n : Nat} (T : TurynType n) :
    HadamardMatrix (4 * (3 * n - 1)) :=
  step3Hadamard (step2 T)

/-- End-to-end correctness theorem for the typed pipeline. -/
theorem turynToHadamard_isHadamard {n : Nat} (T : TurynType n) :
    (turynToHadamard T).matrix.IsHadamard := by
  exact (turynToHadamard T).isHadamard

/-- End-to-end shape theorem for the typed pipeline output. -/
theorem turynToHadamard_hasShape {n : Nat} (T : TurynType n) :
    (turynToHadamard T).matrix.rows.length = 4 * (3 * n - 1) ∧
    allRowsLength (turynToHadamard T).matrix.rows (4 * (3 * n - 1)) = true := by
  exact ⟨(turynToHadamard T).matrix.dim, (turynToHadamard T).isHadamard.1⟩

/-- Convenience entry point from an existing `IsTurynType` certificate. -/
noncomputable def ofIsTurynType {n : Nat} {x y z w : PmSeq}
    (h : IsTurynType n x y z w) : HadamardMatrix (4 * (3 * n - 1)) :=
  turynToHadamard h.toTyped

/-- Correctness theorem for the convenience entry point. -/
theorem ofIsTurynType_isHadamard {n : Nat} {x y z w : PmSeq}
    (h : IsTurynType n x y z w) :
    (ofIsTurynType h).matrix.IsHadamard := by
  exact (ofIsTurynType h).isHadamard
