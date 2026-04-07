import Turyn.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open Finset
open BigOperators

/-!
# Hadamard Matrices and the Goethals-Seidel Construction

A **Hadamard matrix** of order m is an m × m matrix H with entries ±1 such that
H · Hᵀ = m · I.

From a TT(n), the **base-sequence → T-sequence → Goethals-Seidel** pipeline
constructs a Hadamard matrix of order **4(3n − 1)**.

## Construction pipeline (KTR2005)

### Step 1: TT(n) → Base sequences BS(2n−1, 2n−1, n, n)

Given TT(n) = (X, Y, Z, W) with |X| = |Y| = |Z| = n and |W| = n − 1,
form base sequences A = Z++W, B = Z++(−W), C = X, D = Y.
These satisfy N_A(s) + N_B(s) + N_C(s) + N_D(s) = 0 for all s ≥ 1.

**Status:** Fully proved (`base_seq_vanishing_prop`).

### Step 2: Base sequences → T-sequences of length 3n − 1

Pad with zeros to get four equal-length sequences with disjoint supports:

    T₁ = Z ++ 0_n,  T₂ = 0_n ++ W ++ 0_n,
    T₃ = 0_{2n−1} ++ (X+Y)/2,  T₄ = 0_{2n−1} ++ (X−Y)/2

Disjoint supports ensure periodic autocorrelation = aperiodic, which
decomposes into the base-sequence autocorrelation (vanishes by Step 1).

**Status:** Statement only (`tseq_vanishing_prop`).

### Step 3: T-sequences → Goethals-Seidel Hadamard matrix of order 4(3n − 1)

Plug T-sequences into circulant matrices in the 4×4 block array.
For circulant C_a, (C_a · C_aᵀ)_{i,j} = periodic autocorrelation at lag i−j.
The block structure ensures H · Hᵀ = m · I.

**Status:** Statement only (`goethals_seidel_is_hadamard`).
-/

/-! ### Matrix representation -/

/-- A square matrix of integers, stored as a list of rows. -/
abbrev IntMatrix := List (List Int)

/-- The dimension (number of rows) of a square matrix. -/
def IntMatrix.dim (m : IntMatrix) : Nat := m.length

/-- Entry (i, j) of a matrix. -/
def IntMatrix.entry (m : IntMatrix) (i j : Nat) : Int :=
  (m.getD i []).getD j 0

/-- Dot product of two integer lists. -/
def listDotProduct (a b : List Int) : Int :=
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
      let dot := listDotProduct (m.getD i []) (m.getD j [])
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

/-! ### Base sequence construction from TT(n) (KTR2005, Theorem 1) -/

/-- Negate every entry in a sequence. -/
def negSeq (a : PmSeq) : PmSeq := a.map (· * (-1))

/-- Base sequences from TT(n) = (X, Y, Z, W):
    A = Z ++ W, B = Z ++ (−W), C = X, D = Y.
    Lengths: (2n−1, 2n−1, n, n). -/
def baseSequences (x y z w : PmSeq) :
    PmSeq × PmSeq × PmSeq × PmSeq :=
  ( z ++ w,           -- A
    z ++ negSeq w,    -- B
    x,                -- C
    y )               -- D

/-! ### T-sequence construction from base sequences -/

/-- Element-wise sum divided by 2. -/
def seqSumHalf (a b : PmSeq) : List Int :=
  (a.zip b).map fun p => (p.1 + p.2) / 2

/-- Element-wise difference divided by 2. -/
def seqDiffHalf (a b : PmSeq) : List Int :=
  (a.zip b).map fun p => (p.1 - p.2) / 2

/-- Zero sequence of length k. -/
def zeroSeq (k : Nat) : List Int := List.replicate k 0

/-- Construct the four T-sequences from TT(n) = (X, Y, Z, W).
    Using KTR2005: first build base sequences (A, B, C, D) of lengths
    (2n−1, 2n−1, n, n), then:
      T₁ = (A+B)/2 ++ 0_n     = Z ++ 0_n
      T₂ = (A−B)/2 ++ 0_n     = 0_n ++ W ++ 0_n
      T₃ = 0_{2n−1} ++ (C+D)/2
      T₄ = 0_{2n−1} ++ (C−D)/2
    Each has length (2n−1) + n = 3n − 1, entries in {0, ±1}. -/
def tSequences (x y z w : PmSeq) :
    List Int × List Int × List Int × List Int :=
  let (bsA, bsB, bsC, bsD) := baseSequences x y z w
  let n := x.length
  ( seqSumHalf bsA bsB ++ zeroSeq n,        -- T₁
    seqDiffHalf bsA bsB ++ zeroSeq n,       -- T₂
    zeroSeq (2 * n - 1) ++ seqSumHalf bsC bsD,  -- T₃
    zeroSeq (2 * n - 1) ++ seqDiffHalf bsC bsD ) -- T₄

/-! ### Periodic autocorrelation -/

/-- Periodic autocorrelation of a sequence of length m at lag s. -/
def periodicAutocorr (a : List Int) (s : Nat) : Int :=
  let m := a.length
  if m == 0 then 0
  else ∑ i ∈ range m, a.getD i 0 * a.getD ((i + s) % m) 0

/-- Combined periodic autocorrelation of four sequences. -/
def combinedPeriodicAutocorr (a b c d : List Int) (s : Nat) : Int :=
  periodicAutocorr a s + periodicAutocorr b s +
  periodicAutocorr c s + periodicAutocorr d s

/-- Boolean check: T-sequences have vanishing combined periodic autocorrelation. -/
def checkTSeqProperty (a b c d : List Int) : Bool :=
  let m := a.length
  (List.range (m - 1)).all fun i =>
    combinedPeriodicAutocorr a b c d (i + 1) == 0

/-- Boolean check: base sequences have vanishing combined aperiodic autocorrelation. -/
def checkBaseSeqProperty (a b c d : List Int) : Bool :=
  let m := a.length
  (List.range (m - 1)).all fun i =>
    let s := i + 1
    aperiodicAutocorr a s + aperiodicAutocorr b s +
    aperiodicAutocorr c s + aperiodicAutocorr d s == 0

/-! ### Circulant matrix construction -/

/-- Build a circulant matrix from a sequence of length m. -/
def circulant (a : List Int) : IntMatrix :=
  let m := a.length
  (List.range m).map fun i =>
    (List.range m).map fun j =>
      a.getD ((j + m - i) % m) 0

/-- Reversal matrix R applied to a list (reverses columns). -/
def applyR (row : List Int) : List Int := row.reverse

/-- Negate all entries in a row. -/
def negRow (row : List Int) : List Int := row.map (· * (-1))

/-! ### Goethals-Seidel array -/

/-- Build the Goethals-Seidel Hadamard matrix from four sequences.

    H = ⌈  A    B·R   C·R   D·R  ⌉
        | −B·R   A   −Dᵀ·R  Cᵀ·R |
        | −C·R  Dᵀ·R   A   −Bᵀ·R |
        ⌊ −D·R −Cᵀ·R  Bᵀ·R   A   ⌋ -/
def goethalsSeidel (a b c d : List Int) : IntMatrix :=
  let m := a.length
  let matA := circulant a
  let matB := circulant b
  let matC := circulant c
  let matD := circulant d
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
    | _ => []

/-- The Hadamard order from a TT(n) via the KTR2005 pipeline. -/
def hadamardOrder (n : Nat) : Nat := 4 * (3 * n - 1)

/-! ## Step 1: TT(n) → Base sequences (fully proved)

The proof builds up from three lemmas:

1. `negSeq_getD` — indexing into a negated sequence negates the value
2. `pointwise_cancel` — at each index, the Z++W and Z++(-W) products
   combine to either 2× the within-part product or 0 (cross terms cancel)
3. `concat_neg_autocorr_sum` — summing over all indices:
   N_{Z++W}(s) + N_{Z++(-W)}(s) = 2·N_Z(s) + 2·N_W(s)

These combine in `base_seq_vanishing_prop` to show that the base sequence
autocorrelation vanishes, using the Turyn vanishing condition for small lags
and the trivial bound for large lags.
-/

/-- negSeq preserves length. -/
@[simp]
theorem negSeq_length (a : PmSeq) : (negSeq a).length = a.length :=
  List.length_map _

/-- Aperiodic autocorrelation vanishes when the lag meets or exceeds
    the sequence length. -/
lemma aperiodicAutocorr_zero_of_ge (a : PmSeq) (s : Nat) (h : s ≥ a.length) :
    aperiodicAutocorr a s = 0 := by
  unfold aperiodicAutocorr; exact if_pos h

/-- Indexing into a negated sequence negates the value. -/
lemma negSeq_getD (w : PmSeq) (i : Nat) :
    (negSeq w).getD i 0 = w.getD i 0 * (-1) := by
  simp only [negSeq, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp

/-- **Pointwise cross-term cancellation:** at each index i, the sum of the
    products from Z++W and Z++(-W) gives 2× the within-part product
    (when both indices fall in the same part) or 0 (cross term). -/
private lemma pointwise_cancel (z w : PmSeq) (s i : Nat) :
    (z ++ w).getD i 0 * (z ++ w).getD (i + s) 0 +
    (z ++ negSeq w).getD i 0 * (z ++ negSeq w).getD (i + s) 0 =
    if i + s < z.length then
      2 * (z.getD i 0 * z.getD (i + s) 0)
    else if i < z.length then
      0
    else
      2 * (w.getD (i - z.length) 0 * w.getD (i + s - z.length) 0) := by
  by_cases his : i + s < z.length
  · have hi : i < z.length := by omega
    simp only [his, ↓reduceIte]
    rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ his,
        List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ his]
    ring
  · simp only [his, ↓reduceIte]
    by_cases hi : i < z.length
    · simp only [hi, ↓reduceIte]
      rw [List.getD_append _ _ _ _ hi,
          List.getD_append_right _ _ _ _ (by omega),
          List.getD_append _ _ _ _ hi,
          List.getD_append_right _ _ _ _ (by omega)]
      rw [negSeq_getD]
      ring
    · simp only [hi, ↓reduceIte]
      rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega)]
      rw [negSeq_getD, negSeq_getD]
      ring

/-- Out-of-range `getD` returns the default. -/
private lemma getD_zero_of_ge (a : List Int) (i : Nat) (h : a.length ≤ i) :
    a.getD i 0 = 0 := List.getD_eq_default _ _ h

/-- **Cross-term cancellation:**
    N_{Z++W}(s) + N_{Z++(-W)}(s) = 2·N_Z(s) + 2·N_W(s).

    The sum over index pairs splits into within-Z terms, within-W terms,
    and cross terms.  Adding the Z++W and Z++(-W) versions doubles the
    within-part contributions and kills the cross terms. -/
lemma concat_neg_autocorr_sum (z w : PmSeq) (s : Nat) :
    aperiodicAutocorr (z ++ w) s + aperiodicAutocorr (z ++ negSeq w) s =
    2 * aperiodicAutocorr z s + 2 * aperiodicAutocorr w s := by
  have hnw : (negSeq w).length = w.length := negSeq_length w
  unfold aperiodicAutocorr
  simp only [List.length_append, hnw]
  set nz := z.length; set nw := w.length
  by_cases hszw : nz + nw ≤ s
  · -- s ≥ |z| + |w|: all autocorrelations are 0
    simp only [show s ≥ nz + nw from hszw, ↓reduceIte,
               show s ≥ nz from by omega, show s ≥ nw from by omega]; ring
  · simp only [show ¬(nz + nw ≤ s) from by omega, ↓reduceIte]
    -- Combine the two sums pointwise using pointwise_cancel
    rw [← Finset.sum_add_distrib]
    conv_lhs => arg 2; ext i; rw [pointwise_cancel z w s i]
    -- Split the 3-way if-then-else sum using Finset.sum_ite
    rw [Finset.sum_ite]
    simp only [Finset.sum_ite, Finset.sum_const_zero, zero_add]
    by_cases hsz : nz ≤ s
    · -- s ≥ nz: z-autocorrelation is 0, z-filter is empty
      simp only [hsz, ↓reduceIte]
      have hfilt_empty : (range (nz + nw - s)).filter (fun i => i + s < nz) = ∅ := by
        ext x; simp [Finset.mem_filter, Finset.mem_range]; omega
      rw [hfilt_empty, Finset.sum_empty, zero_add]
      by_cases hsw : nw ≤ s
      · -- Both z and w autocorrelations are 0
        simp only [hsw, ↓reduceIte]
        have hfilt_empty2 : ((range (nz + nw - s)).filter (fun i => ¬(i + s < nz))).filter
            (fun i => ¬(↑i < nz)) = ∅ := by
          ext x; simp [Finset.mem_filter, Finset.mem_range]; omega
        rw [hfilt_empty2, Finset.sum_empty]; ring
      · -- Only w-autocorrelation survives
        simp only [hsw, ↓reduceIte]
        have hfilt_eq : ((range (nz + nw - s)).filter (fun i => ¬(i + s < nz))).filter
            (fun i => ¬(↑i < nz)) = Finset.Ico nz (nz + nw - s) := by
          ext x; simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, not_lt]; omega
        rw [hfilt_eq, Finset.sum_Ico_eq_sum_range]
        simp only [mul_zero, zero_add]
        rw [Finset.mul_sum]
        have hrange : nz + nw - s - nz = nw - s := by omega
        apply Finset.sum_congr (by rw [hrange])
        intro i _
        have h1 : nz + i - z.length = i := by omega
        have h2 : nz + i + s - z.length = i + s := by omega
        simp only [h1, h2]
    · -- s < nz: both z and w parts contribute
      simp only [hsz, ↓reduceIte]
      congr 1
      · -- z-part: filter {i+s < nz} of range(nz+nw-s) = range(nz-s)
        rw [Finset.mul_sum]
        apply Finset.sum_congr
        · ext x; simp [Finset.mem_filter, Finset.mem_range]; omega
        · intro i _; ring
      · -- w-part
        by_cases hsw : nw ≤ s
        · simp only [hsw, ↓reduceIte]
          have hfilt_empty2 : ((range (nz + nw - s)).filter (fun i => ¬(i + s < nz))).filter
              (fun i => ¬(↑i < nz)) = ∅ := by
            ext x; simp [Finset.mem_filter, Finset.mem_range]; omega
          rw [hfilt_empty2, Finset.sum_empty]; ring
        · -- Reindex the w-part from Ico nz (nz+nw-s) to range(nw-s)
          simp only [hsw, ↓reduceIte]
          rw [Finset.mul_sum]
          have hfilt_eq : ((range (nz + nw - s)).filter (fun i => ¬(i + s < nz))).filter
              (fun i => ¬(↑i < nz)) = Finset.Ico nz (nz + nw - s) := by
            ext x; simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, not_lt]; omega
          rw [hfilt_eq, Finset.sum_Ico_eq_sum_range]
          have hrange : nz + nw - s - nz = nw - s := by omega
          apply Finset.sum_congr (by rw [hrange])
          intro i _
          show 2 * (w.getD (nz + i - z.length) 0 * w.getD (nz + i + s - z.length) 0) =
               2 * (w.getD i 0 * w.getD (i + s) 0)
          congr 1; congr 1 <;> (congr 1; omega)

/-- **Base sequence theorem (KTR2005, Theorem 1):**
    If (X, Y, Z, W) is TT(n) with n ≥ 1, the base sequences
    A = Z++W, B = Z++(-W), C = X, D = Y satisfy
        N_A(s) + N_B(s) + N_C(s) + N_D(s) = 0   for all s ≥ 1. -/
theorem base_seq_vanishing_prop {n : Nat} {x y z w : PmSeq}
    (htt : IsTurynTypeProp n x y z w) (hn : n ≥ 1)
    {s : Nat} (hs1 : 1 ≤ s) :
    aperiodicAutocorr (z ++ w) s + aperiodicAutocorr (z ++ negSeq w) s +
    aperiodicAutocorr x s + aperiodicAutocorr y s = 0 := by
  rw [concat_neg_autocorr_sum]
  by_cases hsn : s < n
  · -- s < n: the Turyn vanishing condition applies directly
    have hvan := htt.vanishing s hs1 hsn
    unfold combinedAutocorr at hvan
    linarith
  · -- s ≥ n: each autocorrelation vanishes individually (lag ≥ length)
    simp only [not_lt] at hsn
    have hxl := htt.x_len; have hyl := htt.y_len
    have hzl := htt.z_len; have hwl := htt.w_len
    rw [aperiodicAutocorr_zero_of_ge z s (by omega),
        aperiodicAutocorr_zero_of_ge w s (by omega),
        aperiodicAutocorr_zero_of_ge x s (by omega),
        aperiodicAutocorr_zero_of_ge y s (by omega)]
    ring

/-! ## Step 2: Base sequences → T-sequences

The T-sequences are constructed from the base sequences (A, B, C, D)
via half-sum/half-difference and zero-padding.  We show their combined
autocorrelation vanishes by reducing to the base-sequence result.

The key idea: for ±1 sequences a, b of equal length,
  N_{(a+b)/2}(s) + N_{(a−b)/2}(s) = (N_a(s) + N_b(s)) / 2

This is because the cross terms a[i]·b[i+s] appear with opposite signs
in the two expansions and cancel.  Combined with the fact that appending
zeros doesn't affect the autocorrelation (the zero terms contribute nothing),
the T-sequence autocorrelation reduces to the base-sequence autocorrelation.
-/

/-- Appending zeros does not change the autocorrelation at any lag. -/
lemma aperiodicAutocorr_append_zeros (a : List Int) (k s : Nat) :
    aperiodicAutocorr (a ++ zeroSeq k) s = aperiodicAutocorr a s := by
  sorry

/-- Prepending zeros shifts the autocorrelation indices but does not
    change the value (the zero prefix contributes nothing). -/
lemma aperiodicAutocorr_prepend_zeros (a : List Int) (k s : Nat) :
    aperiodicAutocorr (zeroSeq k ++ a) s = aperiodicAutocorr a s := by
  sorry

/-- **Half-sum/half-difference autocorrelation identity:**
    For ±1 sequences a, b of equal length,
    2 * (N_{(a+b)/2}(s) + N_{(a−b)/2}(s)) = N_a(s) + N_b(s).

    The cross terms a[i]·b[i+s] cancel when the two are added. -/
lemma sumHalf_diffHalf_autocorr (a b : PmSeq) (s : Nat)
    (hab : a.length = b.length) :
    2 * (aperiodicAutocorr (seqSumHalf a b) s +
         aperiodicAutocorr (seqDiffHalf a b) s) =
    aperiodicAutocorr a s + aperiodicAutocorr b s := by
  sorry

/-- **T-sequence theorem:** If (X, Y, Z, W) is TT(n), the T-sequences
    of length 3n−1 have vanishing combined aperiodic autocorrelation.

    The proof reduces to `base_seq_vanishing_prop` via:
    1. `aperiodicAutocorr_append_zeros` / `aperiodicAutocorr_prepend_zeros`
       to strip the zero padding
    2. `sumHalf_diffHalf_autocorr` to recombine the half-sum/half-difference
       into the original base-sequence autocorrelation -/
theorem tseq_vanishing_prop {n : Nat} {x y z w : PmSeq}
    (htt : IsTurynTypeProp n x y z w) (hn : n ≥ 1) :
    let (t1, t2, t3, t4) := tSequences x y z w
    ∀ s, 1 ≤ s → s < 3 * n - 1 →
      aperiodicAutocorr t1 s + aperiodicAutocorr t2 s +
      aperiodicAutocorr t3 s + aperiodicAutocorr t4 s = 0 := by
  intro s hs1 _hs2
  -- The let bindings from tSequences/baseSequences are already reduced.
  -- Strip zero padding
  rw [aperiodicAutocorr_append_zeros, aperiodicAutocorr_append_zeros,
      aperiodicAutocorr_prepend_zeros, aperiodicAutocorr_prepend_zeros]
  -- Recombine half-sum/half-difference pairs
  have hAB : (z ++ w).length = (z ++ negSeq w).length := by
    simp [List.length_append, negSeq_length]
  have hCD : x.length = y.length := by
    rw [htt.x_len, htt.y_len]
  -- Use the half-sum/half-difference identity for each pair
  have hAB := sumHalf_diffHalf_autocorr (z ++ w) (z ++ negSeq w) s hAB
  have hCD := sumHalf_diffHalf_autocorr x y s hCD
  -- Base sequence vanishing gives the sum of the originals = 0
  have hbase := base_seq_vanishing_prop htt hn hs1
  -- hAB: 2 * (T1 + T2) = N_A + N_B
  -- hCD: 2 * (T3 + T4) = N_X + N_Y
  -- hbase: (N_A + N_B) + N_X + N_Y = 0
  -- Goal: T1 + T2 + T3 + T4 = 0
  linarith

/-! ## Step 3: T-sequences → Goethals-Seidel Hadamard matrix (statement only)

For circulant matrix C_a with first row a, the (i,j) entry of C_a · C_aᵀ is
the periodic autocorrelation of a at lag i − j.  The 4×4 Goethals-Seidel
block structure ensures H · Hᵀ = m · I when the four sequences have
vanishing combined periodic autocorrelation.
-/

/-- **Goethals-Seidel theorem:** If four equal-length sequences have vanishing
    combined periodic autocorrelation, the Goethals-Seidel array is a
    Hadamard matrix of order 4m. -/
theorem goethals_seidel_is_hadamard (a b c d : List Int)
    (hlen : a.length = b.length ∧ b.length = c.length ∧ c.length = d.length)
    (hvanish : checkTSeqProperty a b c d = true) :
    IsHadamard (goethalsSeidel a b c d) (4 * a.length) := by
  sorry
