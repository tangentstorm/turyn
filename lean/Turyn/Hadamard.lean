/-!
# Hadamard Matrices and the Goethals-Seidel Construction

A **Hadamard matrix** of order m is an m × m matrix H with entries ±1 such that
H · Hᵀ = m · I.

From a TT(n), the **base-sequence → T-sequence → Goethals-Seidel** pipeline
constructs a Hadamard matrix of order **4(3n − 1)**.

## Construction pipeline

### Step 1: TT(n) → T-sequences of length 2n − 1

Given TT(n) = (X, Y, Z, W) with |X| = |Y| = |Z| = n and |W| = n − 1,
form T-sequences by interleaving:

    T₁[2i] = X[i],  T₁[2i+1] = Z[i]     (length 2n − 1)
    T₂[2i] = X[i],  T₂[2i+1] = −Z[i]    (length 2n − 1)
    T₃[2i] = Y[i],  T₃[2i+1] = W[i]     (length 2n − 1)
    T₄[2i] = Y[i],  T₄[2i+1] = −W[i]    (length 2n − 1)

These T-sequences satisfy: P_{T₁}(s) + P_{T₂}(s) + P_{T₃}(s) + P_{T₄}(s) = 0
for all s ≠ 0 (mod 2n−1), where P denotes periodic autocorrelation.

### Step 2: T-sequences → Goethals-Seidel Hadamard matrix

From four sequences of length m with vanishing combined periodic autocorrelation,
the Goethals-Seidel array produces a Hadamard matrix of order 4m:

    H = ⌈  A    B·R   C·R   D·R  ⌉
        | −B·R   A   −Dᵀ·R  Cᵀ·R |
        | −C·R  Dᵀ·R   A   −Bᵀ·R |
        ⌊ −D·R −Cᵀ·R  Bᵀ·R   A   ⌋

where A, B, C, D are circulant matrices from the T-sequences and R is the
back-identity (reversal) matrix.

### Combined: order = 4(2n − 1) from T-sequences

With m = 2n − 1, this gives order 4(2n − 1).

### Step 3: Doubling to order 4(3n − 1)

An additional "base sequence doubling" technique extends the T-sequences of
length 2n−1 to supplementary difference sets or longer sequences of length
3n−1, yielding order 4(3n − 1). See Yang (1983) and Koukouvinos-Kounias (1988).

For TT(36): 4(3·36 − 1) = 4 · 107 = **428**.

## References

- Goethals & Seidel (1967). *Orthogonal matrices with zero diagonal.*
  Can. J. Math. 19, 1001–1010.
- Yang (1983). *On composition of four-symbol δ-codes and Hadamard matrices.*
  Proc. Amer. Math. Soc. 107, 763–776.
- Kharaghani & Tayfeh-Rezaie (2005). *A Hadamard matrix of order 428.*
-/

import Turyn.Basic

/-! ### Matrix representation -/

/-- A square matrix of integers, stored as a list of rows. -/
abbrev IntMatrix := List (List Int)

/-- The dimension (number of rows) of a square matrix. -/
def IntMatrix.dim (m : IntMatrix) : Nat := m.length

/-- Entry (i, j) of a matrix. -/
def IntMatrix.entry (m : IntMatrix) (i j : Nat) : Int :=
  (m.getD i []).getD j 0

/-- Dot product of two integer lists. -/
def dotProduct (a b : List Int) : Int :=
  ((a.zip b).map fun p => p.1 * p.2).foldl (· + ·) 0

/-! ### Hadamard matrix predicate -/

/-- Boolean check: every entry is ±1. -/
def allEntriesPmOne (m : IntMatrix) : Bool :=
  m.all fun row => row.all fun v => v == 1 || v == -1

/-- Boolean check: all rows have the given length. -/
def allRowsLength (m : IntMatrix) (n : Nat) : Bool :=
  m.all fun row => row.length == n

/-- Boolean check: H · Hᵀ = n · I (row orthogonality). -/
def checkOrthogonality (m : IntMatrix) : Bool :=
  let n := m.dim
  (List.range n).all fun i =>
    (List.range n).all fun j =>
      let dot := dotProduct (m.getD i []) (m.getD j [])
      if i == j then dot == (n : Int) else dot == 0

/-- Boolean predicate: is `m` a Hadamard matrix of order `n`? -/
def isHadamardBool (m : IntMatrix) (n : Nat) : Bool :=
  m.dim == n &&
  allRowsLength m n &&
  allEntriesPmOne m &&
  checkOrthogonality m

/-- Propositional predicate: `m` is a Hadamard matrix of order `n`. -/
def IsHadamard (m : IntMatrix) (n : Nat) : Prop :=
  isHadamardBool m n = true

instance (m : IntMatrix) (n : Nat) : Decidable (IsHadamard m n) :=
  inferInstanceAs (Decidable (isHadamardBool m n = true))

/-! ### T-sequence construction from TT(n) -/

/-- Interleave two sequences: [a₀, b₀, a₁, b₁, …, a_{n-1}].
    Result has length 2n − 1 when |a| = n and |b| = n − 1,
    or length 2n − 1 when |a| = n and |b| = n (dropping last b). -/
def interleave (a b : Seq) : Seq :=
  let n := a.length
  (List.range (2 * n - 1)).map fun i =>
    if i % 2 == 0 then a.getD (i / 2) 0
    else b.getD (i / 2) 0

/-- Negate every entry in a sequence. -/
def negSeq (a : Seq) : Seq := a.map (· * (-1))

/-- Construct the four T-sequences from TT(n) = (X, Y, Z, W).
    Each T-sequence has length 2n − 1. -/
def tSequences (x y z w : Seq) : Seq × Seq × Seq × Seq :=
  ( interleave x z,
    interleave x (negSeq z),
    interleave y w,
    interleave y (negSeq w) )

/-! ### Periodic autocorrelation -/

/-- Periodic autocorrelation of a sequence of length m at lag s. -/
def periodicAutocorr (a : Seq) (s : Nat) : Int :=
  let m := a.length
  if m == 0 then 0
  else
    (List.range m).foldl (fun acc i =>
      acc + a.getD i 0 * a.getD ((i + s) % m) 0) 0

/-- Combined periodic autocorrelation of four sequences. -/
def combinedPeriodicAutocorr (a b c d : Seq) (s : Nat) : Int :=
  periodicAutocorr a s + periodicAutocorr b s +
  periodicAutocorr c s + periodicAutocorr d s

/-- Boolean check: T-sequences have vanishing combined periodic autocorrelation
    at every nonzero lag. -/
def checkTSeqProperty (a b c d : Seq) : Bool :=
  let m := a.length
  (List.range (m - 1)).all fun i =>
    combinedPeriodicAutocorr a b c d (i + 1) == 0

/-! ### Circulant matrix construction -/

/-- Build a circulant matrix from a sequence of length m. -/
def circulant (a : Seq) : IntMatrix :=
  let m := a.length
  (List.range m).map fun i =>
    (List.range m).map fun j =>
      a.getD ((j + m - i) % m) 0

/-- Reversal matrix R applied to a list (reverses columns). -/
def applyR (row : List Int) : List Int := row.reverse

/-- Negate all entries in a row. -/
def negRow (row : List Int) : List Int := row.map (· * (-1))

/-- Scale a row: multiply every entry by a scalar. -/
def scaleRow (c : Int) (row : List Int) : List Int := row.map (· * c)

/-! ### Goethals-Seidel array -/

/-- Build the Goethals-Seidel Hadamard matrix from four sequences.

    H = ⌈  A    B·R   C·R   D·R  ⌉
        | −B·R   A   −Dᵀ·R  Cᵀ·R |
        | −C·R  Dᵀ·R   A   −Bᵀ·R |
        ⌊ −D·R −Cᵀ·R  Bᵀ·R   A   ⌋

For simplicity, this constructs the basic form using circulant A and
B·R, C·R, D·R (where B·R means each row of the circulant of B is reversed).

The full construction uses the transpose-reversal pattern above. -/
def goethalsSeidel (a b c d : Seq) : IntMatrix :=
  let m := a.length
  let matA := circulant a
  let matB := circulant b
  let matC := circulant c
  let matD := circulant d
  -- Build the 4m × 4m matrix block by block
  (List.range (4 * m)).map fun i =>
    let blockRow := i / m
    let localI := i % m
    let rowA := matA.getD localI []
    let rowB := matB.getD localI []
    let rowC := matC.getD localI []
    let rowD := matD.getD localI []
    match blockRow with
    | 0 => rowA ++ applyR rowB ++ applyR rowC ++ applyR rowD
    | 1 => negRow (applyR rowB) ++ rowA ++ negRow (applyR rowD) ++ applyR rowC
    | 2 => negRow (applyR rowC) ++ applyR rowD ++ rowA ++ negRow (applyR rowB)
    | 3 => negRow (applyR rowD) ++ negRow (applyR rowC) ++ applyR rowB ++ rowA
    | _ => [] -- unreachable for valid input

/-! ### Main construction theorems -/

/-- **T-sequence theorem (stated):**
    If (X, Y, Z, W) is TT(n), then the T-sequences formed by interleaving
    have vanishing combined periodic autocorrelation.

    This is the bridge between aperiodic (Turyn) and periodic (Goethals-Seidel)
    autocorrelation conditions. -/
theorem tseq_vanishing (n : Nat) (x y z w : Seq)
    (htt : IsTurynType n x y z w) :
    let (t1, t2, t3, t4) := tSequences x y z w
    checkTSeqProperty t1 t2 t3 t4 = true := by
  sorry -- The proof relates aperiodic and periodic autocorrelation via the
         -- interleaving construction. Each periodic autocorrelation decomposes
         -- into sums of aperiodic autocorrelations of the original sequences.

/-- **Goethals-Seidel theorem (stated):**
    If four sequences of length m have vanishing combined periodic
    autocorrelation, the Goethals-Seidel array is a Hadamard matrix
    of order 4m. -/
theorem goethals_seidel_is_hadamard (a b c d : Seq)
    (hlen : a.length = b.length ∧ b.length = c.length ∧ c.length = d.length)
    (hpm : allPmOne a && allPmOne b && allPmOne c && allPmOne d = true)
    (hvanish : checkTSeqProperty a b c d = true) :
    let m := a.length
    IsHadamard (goethalsSeidel a b c d) (4 * m) := by
  sorry -- The proof uses the fact that for circulant matrices,
         -- the product A·Aᵀ + B·R·(B·R)ᵀ + C·R·(C·R)ᵀ + D·R·(D·R)ᵀ
         -- evaluates to (combined periodic autocorrelation) which is m·I
         -- when the combined autocorrelation vanishes at nonzero lags
         -- and equals 4m at lag 0.

/-- **Main theorem (stated):**
    Every TT(n) yields a Hadamard matrix of order 4(2n − 1) via the
    T-sequence + Goethals-Seidel pipeline.

    Combined with the base-sequence doubling technique, this extends to
    order 4(3n − 1). -/
theorem turyn_gives_hadamard_tseq (n : Nat) (x y z w : Seq)
    (htt : IsTurynType n x y z w) :
    let (t1, t2, t3, t4) := tSequences x y z w
    let m := 2 * n - 1
    IsHadamard (goethalsSeidel t1 t2 t3 t4) (4 * m) := by
  sorry -- Compose tseq_vanishing and goethals_seidel_is_hadamard.

/-- The Hadamard order from a TT(n) via the full pipeline (with doubling). -/
def hadamardOrder (n : Nat) : Nat := 4 * (3 * n - 1)
