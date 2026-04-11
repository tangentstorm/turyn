import Turyn.MatrixTyped

open Matrix

namespace Turyn

/-- Typed sign-quad input for the Goethals-Seidel construction. -/
structure GSData (n : Nat) where
  x1 : IntVec n
  x2 : IntVec n
  x3 : IntVec n
  x4 : IntVec n
  x1_pm : IsPmOneVec x1
  x2_pm : IsPmOneVec x2
  x3_pm : IsPmOneVec x3
  x4_pm : IsPmOneVec x4

/-- Combined typed periodic autocorrelation for a GS sign quadruple. -/
def combinedPeriodic {n : Nat} (G : GSData n) (s : Fin n) : Int :=
  periodicAutocorr G.x1 s + periodicAutocorr G.x2 s +
    periodicAutocorr G.x3 s + periodicAutocorr G.x4 s

/-- Certified GS input: sign quadruple with vanishing combined periodic autocorrelation
away from zero. -/
structure CertifiedGSData (n : Nat) extends GSData n where
  periodic_vanishing : ∀ s : Fin n, s.1 ≠ 0 → combinedPeriodic toGSData s = 0

/-- Typed transpose-twisted circulant block, corresponding to `Aᵀ R = R A`. -/
def trCirculant {n : Nat} (x : IntVec n) : IntMat n :=
  (circulant x)ᵀ * reversalMatrix n

/-- The four core circulant blocks used in the GS array. -/
def gsA {n : Nat} (G : GSData n) : IntMat n := circulant G.x1
def gsB {n : Nat} (G : GSData n) : IntMat n := circulant G.x2
def gsC {n : Nat} (G : GSData n) : IntMat n := circulant G.x3
def gsD {n : Nat} (G : GSData n) : IntMat n := circulant G.x4

/-- Typed Goethals-Seidel row formulas as `Fin (4n) -> Fin (4n) -> Int`. -/
def gsMatrixEntry {n : Nat} (G : GSData n) : Fin (4 * n) → Fin (4 * n) → Int :=
  fun i j =>
    let bi : Nat := i.1 / n
    let bj : Nat := j.1 / n
    let ii : Fin n := ⟨i.1 % n, by
      have : i.1 % n < n := by
        have hi : i.1 < 4 * n := i.2
        by_cases hn : n = 0
        · subst hn
          simp at hi
        · exact Nat.mod_lt _ (Nat.pos_of_ne_zero hn)
      exact this⟩
    let jj : Fin n := ⟨j.1 % n, by
      have : j.1 % n < n := by
        have hj : j.1 < 4 * n := j.2
        by_cases hn : n = 0
        · subst hn
          simp at hj
        · exact Nat.mod_lt _ (Nat.pos_of_ne_zero hn)
      exact this⟩
    match bi, bj with
    | 0, 0 => gsA G ii jj
    | 0, 1 => (gsB G * reversalMatrix n) ii jj
    | 0, 2 => (gsC G * reversalMatrix n) ii jj
    | 0, 3 => (gsD G * reversalMatrix n) ii jj
    | 1, 0 => (-(gsB G * reversalMatrix n)) ii jj
    | 1, 1 => gsA G ii jj
    | 1, 2 => trCirculant G.x4 ii jj
    | 1, 3 => (-(trCirculant G.x3)) ii jj
    | 2, 0 => (-(gsC G * reversalMatrix n)) ii jj
    | 2, 1 => (-(trCirculant G.x4)) ii jj
    | 2, 2 => gsA G ii jj
    | 2, 3 => trCirculant G.x2 ii jj
    | 3, 0 => (-(gsD G * reversalMatrix n)) ii jj
    | 3, 1 => trCirculant G.x3 ii jj
    | 3, 2 => (-(trCirculant G.x2)) ii jj
    | 3, 3 => gsA G ii jj
    | _, _ => 0

/-- The typed GS matrix. -/
def gsMatrix {n : Nat} (G : GSData n) : IntMat (4 * n) :=
  gsMatrixEntry G

/-- Negating a `±1` value still gives a `±1` value. -/
lemma pmOne_neg {a : Int} (ha : a = 1 ∨ a = -1) : -a = 1 ∨ -a = -1 := by
  rcases ha with rfl | rfl <;> norm_num

/-- Circulant entries inherit the `±1` property from the seed vector. -/
lemma circulant_pmOne {n : Nat} {x : IntVec n} (hx : IsPmOneVec x) :
    ∀ i j, circulant x i j = 1 ∨ circulant x i j = -1 := by
  intro i j
  simpa [circulant] using hx (j - i)

/-- Right multiplication by the reversal matrix preserves the entrywise `±1` property. -/
lemma mul_reversalMatrix_pmOne {n : Nat} {M : IntMat n}
    (hM : ∀ i j, M i j = 1 ∨ M i j = -1) :
    ∀ i j, (M * reversalMatrix n) i j = 1 ∨ (M * reversalMatrix n) i j = -1 := by
  intro i j
  rw [mul_reversalMatrix_apply]
  exact hM i (revFin j)

/-- The transpose-twisted circulant block is also entrywise `±1`. -/
lemma trCirculant_pmOne {n : Nat} {x : IntVec n} (hx : IsPmOneVec x) :
    ∀ i j, trCirculant x i j = 1 ∨ trCirculant x i j = -1 := by
  intro i j
  unfold trCirculant
  rw [mul_reversalMatrix_apply]
  rw [circulant_transpose_apply]
  exact hx (i - revFin j)

/-- Entrywise `±1` for the typed GS matrix. -/
theorem gsMatrix_pmOne {n : Nat} (G : GSData n) :
    ∀ i j, gsMatrix G i j = 1 ∨ gsMatrix G i j = -1 := by
  intro i j
  unfold gsMatrix gsMatrixEntry gsA gsB gsC gsD
  by_cases hn : n = 0
  · subst hn
    have : False := by simpa using i.2
    contradiction
  · have hi_block : i.1 / n < 4 := by
      exact Nat.div_lt_of_lt_mul (by omega)
    have hj_block : j.1 / n < 4 := by
      exact Nat.div_lt_of_lt_mul (by omega)
    interval_cases hbi : i.1 / n <;> interval_cases hbj : j.1 / n
    · simpa [trCirculant] using circulant_pmOne G.x1_pm
        ⟨i.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
        ⟨j.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
    · simpa using mul_reversalMatrix_pmOne (circulant_pmOne G.x2_pm)
        ⟨i.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
        ⟨j.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
    · simpa using mul_reversalMatrix_pmOne (circulant_pmOne G.x3_pm)
        ⟨i.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
        ⟨j.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
    · simpa using mul_reversalMatrix_pmOne (circulant_pmOne G.x4_pm)
        ⟨i.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
        ⟨j.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
    · exact pmOne_neg <| by
        simpa using mul_reversalMatrix_pmOne (circulant_pmOne G.x2_pm)
          ⟨i.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
          ⟨j.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
    · simpa using circulant_pmOne G.x1_pm
        ⟨i.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
        ⟨j.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
    · simpa using trCirculant_pmOne G.x4_pm
        ⟨i.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
        ⟨j.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
    · exact pmOne_neg <| by
        simpa using trCirculant_pmOne G.x3_pm
          ⟨i.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
          ⟨j.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
    · exact pmOne_neg <| by
        simpa using mul_reversalMatrix_pmOne (circulant_pmOne G.x3_pm)
          ⟨i.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
          ⟨j.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
    · exact pmOne_neg <| by
        simpa using trCirculant_pmOne G.x4_pm
          ⟨i.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
          ⟨j.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
    · simpa using circulant_pmOne G.x1_pm
        ⟨i.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
        ⟨j.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
    · simpa using trCirculant_pmOne G.x2_pm
        ⟨i.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
        ⟨j.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
    · exact pmOne_neg <| by
        simpa using mul_reversalMatrix_pmOne (circulant_pmOne G.x4_pm)
          ⟨i.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
          ⟨j.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
    · simpa using trCirculant_pmOne G.x3_pm
        ⟨i.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
        ⟨j.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
    · exact pmOne_neg <| by
        simpa using trCirculant_pmOne G.x2_pm
          ⟨i.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
          ⟨j.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
    · simpa using circulant_pmOne G.x1_pm
        ⟨i.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
        ⟨j.1 % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩

/-- Matrix-theoretic orthogonality target for the typed GS matrix. -/
def GSTarget {n : Nat} (G : GSData n) : Prop :=
  gsMatrix G * (gsMatrix G)ᵀ = (4 * n : Int) • (1 : IntMat (4 * n))

/-- Sum-typed index for a 4-block matrix with `n × n` blocks. -/
abbrev GSBlockIndex (n : Nat) := (Fin n ⊕ Fin n) ⊕ (Fin n ⊕ Fin n)

/-- Matrix type on the 4-block sum index. -/
abbrev GSBlockMat (n : Nat) := Matrix (GSBlockIndex n) (GSBlockIndex n) Int

/-- Explicit equivalence between the 4-way block index and `Fin (4 * n)`. -/
def gsBlockEquiv (n : Nat) : GSBlockIndex n ≃ Fin (4 * n) :=
  ((Equiv.sumCongr finSumFinEquiv finSumFinEquiv).trans finSumFinEquiv).trans
    (finCongr (by omega))

lemma gsBlockEquiv_block0 {n : Nat} (i : Fin n) :
    (gsBlockEquiv n (Sum.inl (Sum.inl i))).1 = i.1 := by
  simp [gsBlockEquiv]

lemma gsBlockEquiv_block1 {n : Nat} (i : Fin n) :
    (gsBlockEquiv n (Sum.inl (Sum.inr i))).1 = i.1 + n := by
  simp [gsBlockEquiv]

lemma gsBlockEquiv_block2 {n : Nat} (i : Fin n) :
    (gsBlockEquiv n (Sum.inr (Sum.inl i))).1 = i.1 + (n + n) := by
  simp [gsBlockEquiv, Nat.add_assoc]

lemma gsBlockEquiv_block3 {n : Nat} (i : Fin n) :
    (gsBlockEquiv n (Sum.inr (Sum.inr i))).1 = i.1 + n + (n + n) := by
  simp [gsBlockEquiv, Nat.add_assoc]

/-- The GS array expressed as a genuine 4×4 block matrix. -/
def gsBlockMatrix {n : Nat} (G : GSData n) : GSBlockMat n :=
  Matrix.fromBlocks
    (Matrix.fromBlocks (gsA G) (gsB G * reversalMatrix n)
      (-(gsB G * reversalMatrix n)) (gsA G))
    (Matrix.fromBlocks (gsC G * reversalMatrix n) (gsD G * reversalMatrix n)
      (trCirculant G.x4) (-(trCirculant G.x3)))
    (Matrix.fromBlocks (-(gsC G * reversalMatrix n)) (-(trCirculant G.x4))
      (-(gsD G * reversalMatrix n)) (trCirculant G.x3))
    (Matrix.fromBlocks (gsA G) (trCirculant G.x2)
      (-(trCirculant G.x2)) (gsA G))

/-- Block-matrix GS orthogonality target. -/
def GSBlockTarget {n : Nat} (G : GSData n) : Prop :=
  gsBlockMatrix G * (gsBlockMatrix G)ᵀ = (4 * n : Int) • (1 : GSBlockMat n)

/-! ### Helper lemmas for block entry extraction -/

private lemma div_block0 {n : Nat} (i : Fin n) (hn : n ≠ 0) :
    (gsBlockEquiv n (Sum.inl (Sum.inl i))).1 / n = 0 := by
  rw [gsBlockEquiv_block0]; exact Nat.div_eq_of_lt i.2

private lemma div_block1 {n : Nat} (i : Fin n) (hn : n ≠ 0) :
    (gsBlockEquiv n (Sum.inl (Sum.inr i))).1 / n = 1 := by
  rw [gsBlockEquiv_block1]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

private lemma div_block2 {n : Nat} (i : Fin n) (hn : n ≠ 0) :
    (gsBlockEquiv n (Sum.inr (Sum.inl i))).1 / n = 2 := by
  rw [gsBlockEquiv_block2]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

private lemma div_block3 {n : Nat} (i : Fin n) (hn : n ≠ 0) :
    (gsBlockEquiv n (Sum.inr (Sum.inr i))).1 / n = 3 := by
  rw [gsBlockEquiv_block3]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

private lemma mod_block0 {n : Nat} (i : Fin n) (hn : n ≠ 0) :
    (gsBlockEquiv n (Sum.inl (Sum.inl i))).1 % n = i.1 := by
  rw [gsBlockEquiv_block0]; exact Nat.mod_eq_of_lt i.2

private lemma mod_block1 {n : Nat} (i : Fin n) (hn : n ≠ 0) :
    (gsBlockEquiv n (Sum.inl (Sum.inr i))).1 % n = i.1 := by
  rw [gsBlockEquiv_block1]; rw [Nat.add_mod_right]; exact Nat.mod_eq_of_lt i.2

private lemma mod_block2 {n : Nat} (i : Fin n) (hn : n ≠ 0) :
    (gsBlockEquiv n (Sum.inr (Sum.inl i))).1 % n = i.1 := by
  rw [gsBlockEquiv_block2]
  rw [show i.1 + (n + n) = i.1 + 2 * n from by ring, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt i.2

private lemma mod_block3 {n : Nat} (i : Fin n) (hn : n ≠ 0) :
    (gsBlockEquiv n (Sum.inr (Sum.inr i))).1 % n = i.1 := by
  rw [gsBlockEquiv_block3]
  rw [show i.1 + n + (n + n) = i.1 + 3 * n from by ring, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt i.2

/-- The block GS matrix reindexes to the flat `Fin (4n)` GS matrix. -/
theorem gsMatrix_eq_reindex_gsBlockMatrix {n : Nat} (G : GSData n) :
    gsMatrix G = Matrix.reindex (gsBlockEquiv n) (gsBlockEquiv n) (gsBlockMatrix G) := by
  by_cases hn : n = 0
  · subst hn; ext i; exact absurd i.2 (by simp)
  · ext i j
    obtain ⟨p, rfl⟩ := (gsBlockEquiv n).surjective i
    obtain ⟨q, rfl⟩ := (gsBlockEquiv n).surjective j
    simp only [Matrix.reindex_apply, Equiv.symm_apply_apply]
    rcases p with ((p | p) | (p | p)) <;> rcases q with ((q | q) | (q | q)) <;>
    simp only [gsMatrix, gsMatrixEntry, gsBlockMatrix,
      Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      div_block0 _ hn, div_block1 _ hn, div_block2 _ hn, div_block3 _ hn,
      mod_block0 _ hn, mod_block1 _ hn, mod_block2 _ hn, mod_block3 _ hn]

/-! ### Core algebraic helper lemmas -/

/-
Circulant self-product entry equals periodic autocorrelation.
-/
lemma circulant_mul_transpose_eq_periodicAutocorr {n : Nat} (x : IntVec n) (i j : Fin n) :
    (circulant x * (circulant x)ᵀ) i j = periodicAutocorr x (i - j) := by
  -- Apply the circulant_mul_transpose_apply lemma to rewrite the left-hand side.
  rw [circulant_mul_transpose_apply];
  rcases n with ( _ | n ) <;> simp_all +decide [ periodicAutocorr ];
  rw [ ← Equiv.sum_comp ( Equiv.addRight i ) ] ; norm_num [ sub_eq_add_neg, add_assoc ] ;

/-
Periodic autocorrelation at zero gives n for ±1 vectors.
-/
lemma periodicAutocorr_zero_pmOne {n : Nat} [NeZero n] (x : IntVec n) (hx : IsPmOneVec x) :
    periodicAutocorr x 0 = (n : Int) := by
  convert Finset.sum_congr rfl fun i _ => show x i * x i = 1 by cases hx i <;> simp +decide [ * ];
  rotate_right;
  exacts [ Finset.univ, by unfold periodicAutocorr; simp +decide [ Finset.sum_range, Fin.cast_val_eq_self ], by simp +decide ]

/-
Periodic autocorrelation is an even function.
-/
lemma periodicAutocorr_neg {n : Nat} (x : IntVec n) (s : Fin n) :
    periodicAutocorr x (-s) = periodicAutocorr x s := by
  unfold periodicAutocorr;
  rcases n with ( _ | _ | n ) <;> norm_num at *;
  · fin_cases s ; rfl;
  · rw [ ← Equiv.sum_comp ( Equiv.addRight s ) ] ; norm_num;
    ac_rfl

/-- `Cᵀ * C = C * Cᵀ` for circulant matrices (both give periodic autocorrelation). -/
lemma circulant_transpose_mul_self_comm {n : Nat} (x : IntVec n) :
    (circulant x)ᵀ * circulant x = circulant x * (circulant x)ᵀ := by
  rcases n with _ | n
  · ext i; exact absurd i.2 (by simp)
  · haveI : NeZero (n + 1) := ⟨by omega⟩
    ext i j
    simp only [Matrix.mul_apply, circulant_transpose_apply, circulant_apply]
    conv_lhs =>
      arg 2; ext k
      rw [show i - k = (i + j) - k - j from by abel]
      rw [show j - k = (i + j) - k - i from by abel]
      rw [mul_comm]
    rw [← Equiv.sum_comp (Equiv.subLeft (i + j))]
    simp [Equiv.subLeft]

/-
`(M * R) * (M * R)ᵀ = M * Mᵀ` using `Rᵀ = R` and `R² = I`.
-/
lemma mul_reversalMatrix_mul_transpose_self {n : Nat} (M : IntMat n) :
    (M * reversalMatrix n) * (M * reversalMatrix n)ᵀ = M * Mᵀ := by
  simp +decide [ Matrix.mul_assoc, Matrix.transpose_mul, reversalMatrix_transpose ];
  simp_all +decide [ ← Matrix.mul_assoc, reversalMatrix_mul_reversalMatrix ]

/-
`trCirculant x * (trCirculant x)ᵀ = circulant x * (circulant x)ᵀ`.
-/
lemma trCirculant_mul_transpose_self {n : Nat} (x : IntVec n) :
    trCirculant x * (trCirculant x)ᵀ = circulant x * (circulant x)ᵀ := by
  -- Apply the property that $(M * R) * (M * R)ᵀ = M * Mᵀ$ for any matrix $M$.
  have h_prop : ∀ M : IntMat n, (M * reversalMatrix n) * (M * reversalMatrix n)ᵀ = M * Mᵀ := by
    exact?;
  convert h_prop _ using 1;
  rw [ Matrix.transpose_transpose, circulant_transpose_mul_self_comm ]

/-
Circulant matrices commute.
-/
lemma circulant_mul_circulant_comm {n : Nat} (x y : IntVec n) :
    circulant x * circulant y = circulant y * circulant x := by
  ext i j; simp +decide [ circulant_apply, Matrix.mul_apply ] ; ring;
  rcases n with ( _ | _ | n ) <;> norm_cast at *;
  · fin_cases i ; fin_cases j ; simp +decide [ mul_comm ];
  · rw [ ← Equiv.sum_comp ( Equiv.subLeft j ) ] ; simp +decide [ mul_comm ] ; ring;
    rw [ ← Equiv.sum_comp ( Equiv.subRight i ) ] ; simp +decide [ mul_comm, sub_sub ] ;

/-- Circulant transposes also commute. -/
lemma circulant_transpose_mul_comm {n : Nat} (x y : IntVec n) :
    (circulant x)ᵀ * (circulant y)ᵀ = (circulant y)ᵀ * (circulant x)ᵀ := by
  rw [← Matrix.transpose_mul, ← Matrix.transpose_mul]
  congr 1
  exact circulant_mul_circulant_comm y x

/-
Circulant commutes with circulant transpose.
-/
lemma circulant_mul_circulant_transpose_comm {n : Nat} (x y : IntVec n) :
    circulant x * (circulant y)ᵀ = (circulant y)ᵀ * circulant x := by
  ext i j; simp +decide [ mul_apply, circulant_apply, circulant_transpose_apply ] ;
  rcases n with ( _ | _ | n ) <;> norm_num [ Finset.sum_range, Fin.mod_def ];
  · simp +decide [ Fin.eq_zero, mul_comm ];
  · rw [ ← Equiv.sum_comp ( Equiv.subLeft ( i + j ) ) ] ; simp +decide [ mul_comm, sub_eq_add_neg ];
    grind

/-
`circulant x * R = R * (circulant x)ᵀ`.
-/
lemma circulant_reversalMatrix {n : Nat} (x : IntVec n) :
    circulant x * reversalMatrix n = reversalMatrix n * (circulant x)ᵀ := by
  -- By definition of matrix multiplication and the properties of the reversal matrix, we can show that the entries of the two matrices are equal.
  ext i j; simp [Matrix.mul_apply, reversalMatrix];
  rw [ Finset.sum_eq_single ( revFin j ) ] <;> simp +decide [ revFin ];
  · grind;
  · grind

/-
`(circulant x)ᵀ * R = R * circulant x`.
-/
lemma circulant_transpose_reversalMatrix {n : Nat} (x : IntVec n) :
    (circulant x)ᵀ * reversalMatrix n = reversalMatrix n * circulant x := by
  ext i j; simp +decide [ Matrix.mul_apply ] ;
  rw [ Finset.sum_eq_single ( revFin j ) ] <;> simp +decide [ revFin ];
  · grind;
  · grind

/-
Key symmetry: `C_x * R * C_yᵀ = C_y * R * C_xᵀ` for circulants.
-/
lemma circulant_reversalMatrix_transpose_comm {n : Nat} (x y : IntVec n) :
    circulant x * reversalMatrix n * (circulant y)ᵀ =
    circulant y * reversalMatrix n * (circulant x)ᵀ := by
  -- By circulant_transpose_mul_comm, we have circulant x * R = R * (circulant x)^T.
  have h1 : circulant x * reversalMatrix n = reversalMatrix n * (circulant x)ᵀ := by
    -- By definition of circulant matrices and the reversal matrix, we can show that they commute.
    ext i j; simp [circulant, reversalMatrix];
    unfold revFin;
    grind;
  rw [ h1, Matrix.mul_assoc, circulant_transpose_mul_comm ];
  -- By circulant_transpose_mul_comm, we have circulant y * R = R * (circulant y)^T.
  have h2 : circulant y * reversalMatrix n = reversalMatrix n * (circulant y)ᵀ := by
    ext i j; simp +decide [ *, Matrix.mul_apply ] ;
    rw [ Finset.sum_eq_single ( revFin j ) ] <;> simp +decide [ revFin ];
    · grind +splitImp;
    · grind
  rw [ h2, Matrix.mul_assoc ]

/-
The combined sum of four circulant self-products equals `(4n) • I`.
-/
lemma four_circulant_products_eq {n : Nat} (G : CertifiedGSData n) :
    gsA G.toGSData * (gsA G.toGSData)ᵀ + gsB G.toGSData * (gsB G.toGSData)ᵀ +
    gsC G.toGSData * (gsC G.toGSData)ᵀ + gsD G.toGSData * (gsD G.toGSData)ᵀ =
    (4 * ↑n : Int) • (1 : IntMat n) := by
  ext i j; by_cases hij : i = j <;> simp_all +decide [ Matrix.mul_apply, Finset.sum_apply, Finset.mul_sum ] ;
  · -- Since each entry in the circulant matrices is ±1, the square of each entry is 1. Therefore, the sum of the squares of the entries in each row is n.
    have h_sum_squares : ∀ (x : IntVec n) (hx : IsPmOneVec x), ∀ j : Fin n, ∑ x_1 : Fin n, x (x_1 - j) * x (x_1 - j) = n := by
      intro x hx j; rw [ Finset.sum_congr rfl fun i hi => by rw [ show x ( i - j ) * x ( i - j ) = 1 by rcases hx ( i - j ) with h | h <;> rw [ h ] <;> norm_num ] ] ; simp +decide ;
    linarith! [ h_sum_squares G.x1 G.x1_pm j, h_sum_squares G.x2 G.x2_pm j, h_sum_squares G.x3 G.x3_pm j, h_sum_squares G.x4 G.x4_pm j ];
  · have h_combined : combinedPeriodic G.toGSData (i - j) = 0 := by
      apply G.periodic_vanishing;
      simp_all +decide [ Fin.ext_iff, Fin.val_sub ];
      contrapose! hij; have := Nat.mod_add_div ( n - j + i ) n; simp_all +decide [ Nat.mod_eq_of_lt ] ;
      nlinarith [ show ( n - j + i : ℕ ) / n = 1 by nlinarith [ Fin.is_lt i, Fin.is_lt j, Nat.sub_add_cancel ( show ( j : ℕ ) ≤ n from j.2.le ) ], Nat.sub_add_cancel ( show ( j : ℕ ) ≤ n from j.2.le ) ];
    have h_combined : ∀ x : IntVec n, (circulant x * (circulant x)ᵀ) i j = periodicAutocorr x (i - j) := by
      exact?;
    unfold gsA gsB gsC gsD; simp_all +decide [ Matrix.mul_apply, Finset.sum_add_distrib ] ;
    exact?

/-! ### Block matrix computations -/

/-- The 4×4 block GS matrix is entrywise `±1`. -/
theorem gsBlockMatrix_pmOne {n : Nat} (G : GSData n) :
    ∀ i j, gsBlockMatrix G i j = 1 ∨ gsBlockMatrix G i j = -1 := by
  intro i j
  rcases i with (i | i)
  · rcases i with (i | i)
    · rcases j with (j | j)
      · rcases j with (j | j)
        · simpa [gsBlockMatrix, gsA] using circulant_pmOne G.x1_pm i j
        · simpa [gsBlockMatrix, gsB] using mul_reversalMatrix_pmOne (circulant_pmOne G.x2_pm) i j
      · rcases j with (j | j)
        · simpa [gsBlockMatrix, gsC] using mul_reversalMatrix_pmOne (circulant_pmOne G.x3_pm) i j
        · simpa [gsBlockMatrix, gsD] using mul_reversalMatrix_pmOne (circulant_pmOne G.x4_pm) i j
    · rcases j with (j | j)
      · rcases j with (j | j)
        · exact pmOne_neg <| by
            simpa [gsBlockMatrix, gsB] using mul_reversalMatrix_pmOne (circulant_pmOne G.x2_pm) i j
        · simpa [gsBlockMatrix, gsA] using circulant_pmOne G.x1_pm i j
      · rcases j with (j | j)
        · simpa [gsBlockMatrix] using trCirculant_pmOne G.x4_pm i j
        · exact pmOne_neg <| by
            simpa [gsBlockMatrix] using trCirculant_pmOne G.x3_pm i j
  · rcases i with (i | i)
    · rcases j with (j | j)
      · rcases j with (j | j)
        · exact pmOne_neg <| by
            simpa [gsBlockMatrix, gsC] using mul_reversalMatrix_pmOne (circulant_pmOne G.x3_pm) i j
        · exact pmOne_neg <| by
            simpa [gsBlockMatrix] using trCirculant_pmOne G.x4_pm i j
      · rcases j with (j | j)
        · simpa [gsBlockMatrix, gsA] using circulant_pmOne G.x1_pm i j
        · simpa [gsBlockMatrix] using trCirculant_pmOne G.x2_pm i j
    · rcases j with (j | j)
      · rcases j with (j | j)
        · exact pmOne_neg <| by
            simpa [gsBlockMatrix, gsD] using mul_reversalMatrix_pmOne (circulant_pmOne G.x4_pm) i j
        · simpa [gsBlockMatrix] using trCirculant_pmOne G.x3_pm i j
      · rcases j with (j | j)
        · exact pmOne_neg <| by
            simpa [gsBlockMatrix] using trCirculant_pmOne G.x2_pm i j
        · simpa [gsBlockMatrix, gsA] using circulant_pmOne G.x1_pm i j

/-! ### Diagonal block identity -/

/-
Each diagonal block of `gsBlockMatrix * gsBlockMatrixᵀ` equals `(4n) • I`.
-/
theorem gsBlockMatrix_diag_blocks {n : Nat} (G : CertifiedGSData n) :
    let M := gsBlockMatrix G.toGSData * (gsBlockMatrix G.toGSData)ᵀ
    Matrix.toBlocks₁₁ (Matrix.toBlocks₁₁ M) = (4 * n : Int) • (1 : IntMat n) ∧
    Matrix.toBlocks₂₂ (Matrix.toBlocks₁₁ M) = (4 * n : Int) • (1 : IntMat n) ∧
    Matrix.toBlocks₁₁ (Matrix.toBlocks₂₂ M) = (4 * n : Int) • (1 : IntMat n) ∧
    Matrix.toBlocks₂₂ (Matrix.toBlocks₂₂ M) = (4 * n : Int) • (1 : IntMat n) := by
  unfold gsBlockMatrix; simp +decide [ Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply ] ;
  simp +decide [ Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.fromBlocks_multiply ] at *;
  simp_all +decide [ ← Matrix.mul_assoc, mul_reversalMatrix_mul_transpose_self, trCirculant_mul_transpose_self ];
  simp_all +decide [ mul_assoc, reversalMatrix_transpose, reversalMatrix_mul_reversalMatrix ];
  have := four_circulant_products_eq G; simp_all +decide [ ← add_assoc, ← Matrix.ext_iff ] ;
  exact ⟨ fun i j => by linarith! [ this i j ], fun i j => by linarith! [ this i j ], fun i j => by linarith! [ this i j ] ⟩

/-
The upper-right block of `gsBlockMatrix * gsBlockMatrixᵀ` vanishes.
-/
theorem gsBlockMatrix_upper_right_zero {n : Nat} (G : CertifiedGSData n) :
    Matrix.toBlocks₁₂ (gsBlockMatrix G.toGSData * (gsBlockMatrix G.toGSData)ᵀ) = 0 := by
  unfold gsBlockMatrix;
  simp +decide [ Matrix.toBlocks₁₂, Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose, reversalMatrix_transpose, reversalMatrix_mul_reversalMatrix, circulant_reversalMatrix, circulant_transpose_reversalMatrix, circulant_mul_circulant_comm, circulant_mul_circulant_transpose_comm, circulant_reversalMatrix_transpose_comm, Matrix.mul_assoc, neg_mul, mul_neg ];
  ext i j;
  rcases i with ( i | i ) <;> rcases j with ( j | j ) <;> simp +decide [ Matrix.fromBlocks ];
  · unfold gsA gsB gsC gsD trCirculant;
    simp +decide [ ← Matrix.mul_assoc, ← circulant_reversalMatrix, ← circulant_transpose_reversalMatrix, ← circulant_mul_circulant_comm, ← circulant_mul_circulant_transpose_comm, ← circulant_reversalMatrix_transpose_comm, reversalMatrix_transpose, reversalMatrix_mul_reversalMatrix ];
    ring;
  · unfold gsA gsB gsC gsD trCirculant; simp +decide [ ← Matrix.mul_assoc, reversalMatrix_mul_reversalMatrix ] ; ring;
    simp +decide [ Matrix.mul_assoc, reversalMatrix_transpose ];
    simp +decide [ ← Matrix.mul_assoc, reversalMatrix_mul_reversalMatrix ];
    simp_all +decide [ circulant_reversalMatrix_transpose_comm, circulant_mul_circulant_comm ];
  · unfold trCirculant; simp +decide [ Matrix.mul_assoc, Matrix.transpose_mul ] ;
    simp +decide [ ← Matrix.mul_assoc, reversalMatrix_transpose, reversalMatrix_mul_reversalMatrix ];
    unfold gsA gsB gsC; simp +decide [ Matrix.mul_assoc, circulant_mul_circulant_comm, circulant_mul_circulant_transpose_comm, circulant_reversalMatrix, circulant_transpose_reversalMatrix ] ;
    ring;
  · simp +decide [ ← Matrix.mul_assoc, trCirculant ];
    simp +decide [ gsA, gsB, gsC, gsD, reversalMatrix_transpose, reversalMatrix_mul_reversalMatrix, Matrix.mul_assoc ];
    simp +decide [ ← Matrix.mul_assoc, circulant_mul_circulant_comm, circulant_mul_circulant_transpose_comm, circulant_reversalMatrix_transpose_comm, circulant_transpose_mul_comm ];
    simp +decide [ Matrix.mul_assoc, circulant_reversalMatrix, circulant_transpose_reversalMatrix, circulant_mul_circulant_comm, circulant_mul_circulant_transpose_comm, circulant_reversalMatrix_transpose_comm, circulant_transpose_mul_comm ];
    grind

/-
The lower-left block of `gsBlockMatrix * gsBlockMatrixᵀ` vanishes.
-/
theorem gsBlockMatrix_lower_left_zero {n : Nat} (G : CertifiedGSData n) :
    Matrix.toBlocks₂₁ (gsBlockMatrix G.toGSData * (gsBlockMatrix G.toGSData)ᵀ) = 0 := by
  ext i j; simp +decide [ Matrix.toBlocks₂₁ ] ;
  convert congr_arg ( fun m => m j i ) ( gsBlockMatrix_upper_right_zero G ) using 1;
  simp +decide [ Matrix.toBlocks₁₂, Matrix.mul_apply ];
  ac_rfl

/-
The full block product collapses to `(4n) • 1`.
-/
set_option maxHeartbeats 800000 in
theorem gsBlockMatrix_target_from_blocks {n : Nat} (G : CertifiedGSData n) :
    GSBlockTarget G.toGSData := by
  unfold GSBlockTarget;
  unfold gsBlockMatrix;
  simp +decide [ Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose ];
  unfold gsA gsB gsC gsD trCirculant at *;
  simp +decide [ Matrix.mul_assoc, Matrix.transpose_mul, reversalMatrix_transpose, reversalMatrix_mul_reversalMatrix ] at *;
  simp +decide [ ← Matrix.mul_assoc, ← circulant_mul_circulant_comm, ← circulant_mul_circulant_transpose_comm, ← circulant_reversalMatrix_transpose_comm, ← circulant_reversalMatrix, ← circulant_transpose_reversalMatrix, reversalMatrix_mul_reversalMatrix ] at *;
  simp +decide [ ← Matrix.ext_iff ] at *;
  simp +decide [ show ( 4 * n : Matrix ( GSBlockIndex n ) ( GSBlockIndex n ) ℤ ) = ( 4 * n : ℤ ) • 1 from by norm_num ] at *;
  simp +decide [ Matrix.one_apply, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm ] at *;
  have := four_circulant_products_eq G; simp_all +decide [ ← Matrix.ext_iff ] ;
  simp_all +decide [ ← add_assoc, gsA, gsB, gsC, gsD ];
  simp_all +decide [ ← Matrix.ext_iff, circulant_transpose_mul_comm ];
  simp +decide [ show ( 4 * n : Matrix ( Fin n ) ( Fin n ) ℤ ) = ( 4 * n : ℤ ) • 1 from by norm_num ];
  simp +decide [ Matrix.one_apply ]

/-- Block-matrix GS orthogonality theorem. -/
theorem gsBlockMatrix_target {n : Nat} (G : CertifiedGSData n) :
    GSBlockTarget G.toGSData := by
  exact gsBlockMatrix_target_from_blocks G

/-- The typed GS matrix is Hadamard once the matrix-algebra target identity is proved. -/
theorem gsTarget_implies_hadamard {n : Nat} (G : GSData n) (h : GSTarget G) :
    IsHadamardMat (gsMatrix G) := by
  constructor
  · exact gsMatrix_pmOne G
  · exact h

/-
Typed GS orthogonality target.
-/
theorem gsMatrix_target {n : Nat} (G : CertifiedGSData n) :
    GSTarget G.toGSData := by
  convert gsBlockMatrix_target_from_blocks G using 1;
  funext n G;
  rw [ GSTarget, GSBlockTarget ];
  rw [ gsMatrix_eq_reindex_gsBlockMatrix ];
  simp +decide [ Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_eq_diagonal_mul ];
  constructor <;> intro h <;> ext i j <;> simp_all +decide [ Matrix.submatrix, Matrix.diagonal ];
  simpa using congr_fun ( congr_fun h ( gsBlockEquiv n i ) ) ( gsBlockEquiv n j )

/-- Final typed GS Hadamard theorem. -/
theorem gsMatrix_isHadamard {n : Nat} (G : CertifiedGSData n) :
    IsHadamardMat (gsMatrix G.toGSData) := by
  exact gsTarget_implies_hadamard G.toGSData (gsMatrix_target G)

end Turyn