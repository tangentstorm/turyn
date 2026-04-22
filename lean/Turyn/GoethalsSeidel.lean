import Turyn.MatrixTyped

open Matrix

/-!
# Goethals-Seidel Construction

The typed Goethals-Seidel array, together with the matrix-algebra proof that
certified GS data produces a Hadamard matrix.
-/

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
  simp [gsBlockEquiv]

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

private lemma div_block0 {n : Nat} (i : Fin n) :
    (gsBlockEquiv n (Sum.inl (Sum.inl i))).1 / n = 0 := by
  rw [gsBlockEquiv_block0]; exact Nat.div_eq_of_lt i.2

private lemma div_block1 {n : Nat} (i : Fin n) :
    (gsBlockEquiv n (Sum.inl (Sum.inr i))).1 / n = 1 := by
  rw [gsBlockEquiv_block1]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

private lemma div_block2 {n : Nat} (i : Fin n) :
    (gsBlockEquiv n (Sum.inr (Sum.inl i))).1 / n = 2 := by
  rw [gsBlockEquiv_block2]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

private lemma div_block3 {n : Nat} (i : Fin n) :
    (gsBlockEquiv n (Sum.inr (Sum.inr i))).1 / n = 3 := by
  rw [gsBlockEquiv_block3]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

private lemma mod_block0 {n : Nat} (i : Fin n) :
    (gsBlockEquiv n (Sum.inl (Sum.inl i))).1 % n = i.1 := by
  rw [gsBlockEquiv_block0]; exact Nat.mod_eq_of_lt i.2

private lemma mod_block1 {n : Nat} (i : Fin n) :
    (gsBlockEquiv n (Sum.inl (Sum.inr i))).1 % n = i.1 := by
  rw [gsBlockEquiv_block1]; rw [Nat.add_mod_right]; exact Nat.mod_eq_of_lt i.2

private lemma mod_block2 {n : Nat} (i : Fin n) :
    (gsBlockEquiv n (Sum.inr (Sum.inl i))).1 % n = i.1 := by
  rw [gsBlockEquiv_block2]
  rw [show i.1 + (n + n) = i.1 + 2 * n from by ring, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt i.2

private lemma mod_block3 {n : Nat} (i : Fin n) :
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
    simp only [Matrix.reindex_apply, Equiv.symm_apply_apply, Matrix.submatrix_apply]
    rcases p with ((p | p) | (p | p)) <;> rcases q with ((q | q) | (q | q)) <;>
    simp only [gsMatrix, gsMatrixEntry, gsBlockMatrix,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, div_block0, div_block1,
      div_block2, div_block3, mod_block0, mod_block1, mod_block2,
      mod_block3, Matrix.neg_apply]

/-! ### Core algebraic helper lemmas -/

/-
Circulant self-product entry equals periodic autocorrelation.
-/
lemma circulant_mul_transpose_eq_periodicAutocorr {n : Nat} (x : IntVec n) (i j : Fin n) :
    (circulant x * (circulant x)ᵀ) i j = periodicAutocorr x (i - j) := by
  rcases n with _ | n
  · exact Fin.elim0 i
  · rw [circulant_mul_transpose_apply]
    unfold periodicAutocorr
    rw [← Equiv.sum_comp (Equiv.addRight i)]
    congr 1; ext k
    simp only [Equiv.coe_addRight]
    congr 1 <;> congr 1 <;> abel

/-
Periodic autocorrelation at zero gives n for ±1 vectors.
-/
lemma periodicAutocorr_zero_pmOne {n : Nat} [NeZero n] (x : IntVec n) (hx : IsPmOneVec x) :
    periodicAutocorr x 0 = (n : Int) := by
  unfold periodicAutocorr
  have h : ∀ i : Fin n, x i * x (i + 0) = 1 := by
    intro i; simp only [add_zero]; rcases hx i with h | h <;> rw [h] <;> norm_num
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, Nat.smul_one_eq_cast]

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

/-
`Cᵀ * C = C * Cᵀ` for circulant matrices (both give periodic autocorrelation).
-/
lemma circulant_transpose_mul_self_comm {n : Nat} (x : IntVec n) :
    (circulant x)ᵀ * circulant x = circulant x * (circulant x)ᵀ := by
  rcases n with _ | n
  · ext i; exact Fin.elim0 i
  · ext i j
    simp only [Matrix.mul_apply, circulant_transpose_apply, circulant_apply]
    conv_lhs =>
      arg 2; ext k
      rw [show i - k = (i + j) - k - j from by abel,
          show j - k = (i + j) - k - i from by abel, mul_comm]
    rw [← Equiv.sum_comp (Equiv.subLeft (i + j))]
    congr 1; ext k
    simp only [Equiv.subLeft_apply]
    congr 1 <;> congr 1 <;> abel

/-
`(M * R) * (M * R)ᵀ = M * Mᵀ` using `Rᵀ = R` and `R² = I`.
-/
lemma mul_reversalMatrix_mul_transpose_self {n : Nat} (M : IntMat n) :
    (M * reversalMatrix n) * (M * reversalMatrix n)ᵀ = M * Mᵀ := by
  rw [Matrix.transpose_mul, reversalMatrix_transpose,
      Matrix.mul_assoc, ← Matrix.mul_assoc (reversalMatrix n) (reversalMatrix n),
      reversalMatrix_mul_reversalMatrix, Matrix.one_mul]

/-
`trCirculant x * (trCirculant x)ᵀ = circulant x * (circulant x)ᵀ`.
-/
lemma trCirculant_mul_transpose_self {n : Nat} (x : IntVec n) :
    trCirculant x * (trCirculant x)ᵀ = circulant x * (circulant x)ᵀ := by
  -- Apply the property that $(M * R) * (M * R)ᵀ = M * Mᵀ$ for any matrix $M$.
  have h_prop : ∀ M : IntMat n, (M * reversalMatrix n) * (M * reversalMatrix n)ᵀ = M * Mᵀ := by
    exact fun M => mul_reversalMatrix_mul_transpose_self M;
  convert h_prop _ using 1;
  rw [ Matrix.transpose_transpose, circulant_transpose_mul_self_comm ]

/-- `revFin j - i = revFin i - j`: the reversal-based subtraction is symmetric. -/
private lemma revFin_sub_comm {n : Nat} (i j : Fin n) : revFin j - i = revFin i - j := by
  rcases n with _ | n
  · exact Fin.elim0 i
  · apply Fin.ext; simp only [revFin_val, Fin.val_sub]; congr 1; omega

/-- `i - revFin j = j - revFin i`: subtraction from a reversed index is symmetric. -/
private lemma sub_revFin_comm {n : Nat} (i j : Fin n) : i - revFin j = j - revFin i := by
  rcases n with _ | n
  · exact Fin.elim0 i
  · apply Fin.ext; simp only [revFin_val, Fin.val_sub]; congr 1; omega

/-
Circulant matrices commute.
-/
lemma circulant_mul_circulant_comm {n : Nat} (x y : IntVec n) :
    circulant x * circulant y = circulant y * circulant x := by
  rcases n with _ | n
  · ext i; exact Fin.elim0 i
  · ext i j
    simp only [Matrix.mul_apply, circulant_apply]
    rw [← Equiv.sum_comp (Equiv.subLeft (i + j))]
    simp only [Equiv.subLeft_apply]
    apply Finset.sum_congr rfl
    intro k _
    have h1 : i + j - k - i = j - k := by abel
    have h2 : j - (i + j - k) = k - i := by abel
    rw [h1, h2, mul_comm]

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
  rcases n with _ | n
  · ext i; exact Fin.elim0 i
  · ext i j
    simp only [Matrix.mul_apply, circulant_apply, circulant_transpose_apply]
    rw [← Equiv.sum_comp (Equiv.subLeft (i + j))]
    simp only [Equiv.subLeft_apply]
    apply Finset.sum_congr rfl
    intro k _
    have h1 : i + j - k - i = j - k := by abel
    have h2 : i + j - k - j = i - k := by abel
    rw [h1, h2, mul_comm]

/-
`circulant x * R = R * (circulant x)ᵀ`.
-/
lemma circulant_reversalMatrix {n : Nat} (x : IntVec n) :
    circulant x * reversalMatrix n = reversalMatrix n * (circulant x)ᵀ := by
  ext i j
  simp only [mul_reversalMatrix_apply, reversalMatrix_mul_apply,
    circulant_apply, circulant_transpose_apply]
  exact congr_arg x (revFin_sub_comm i j)

/-
`(circulant x)ᵀ * R = R * circulant x`.
-/
lemma circulant_transpose_reversalMatrix {n : Nat} (x : IntVec n) :
    (circulant x)ᵀ * reversalMatrix n = reversalMatrix n * circulant x := by
  ext i j
  simp only [mul_reversalMatrix_apply, reversalMatrix_mul_apply,
    circulant_transpose_apply, circulant_apply]
  exact congr_arg x (sub_revFin_comm i j)

/-
Key symmetry: `C_x * R * C_yᵀ = C_y * R * C_xᵀ` for circulants.
-/
lemma circulant_reversalMatrix_transpose_comm {n : Nat} (x y : IntVec n) :
    circulant x * reversalMatrix n * (circulant y)ᵀ =
    circulant y * reversalMatrix n * (circulant x)ᵀ := by
  rw [circulant_reversalMatrix x, Matrix.mul_assoc,
      circulant_transpose_mul_comm x y,
      ← Matrix.mul_assoc, ← circulant_reversalMatrix y]


private lemma fin_sub_val_ne_zero {n : Nat} {i j : Fin n} (hij : i ≠ j) : (i - j).val ≠ 0 := by
  intro h; apply hij; rw [Fin.ext_iff]
  simp only [Fin.val_sub] at h
  have hi := i.isLt; have hj := j.2
  by_cases hij2 : j.val ≤ i.val
  · rw [show n - j.val + i.val = i.val - j.val + n from by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega : i.val - j.val < n)] at h; omega
  · push_neg at hij2
    rw [Nat.mod_eq_of_lt (by omega : n - j.val + i.val < n)] at h; omega

/-
The combined sum of four circulant self-products equals `(4n) • I`.
-/
lemma four_circulant_products_eq {n : Nat} (G : CertifiedGSData n) :
    gsA G.toGSData * (gsA G.toGSData)ᵀ + gsB G.toGSData * (gsB G.toGSData)ᵀ +
    gsC G.toGSData * (gsC G.toGSData)ᵀ + gsD G.toGSData * (gsD G.toGSData)ᵀ =
    (4 * ↑n : Int) • (1 : IntMat n) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    haveI : NeZero n := ⟨fun h => by subst h; exact (Nat.not_lt_zero _ i.2).elim⟩
    unfold gsA gsB gsC gsD
    rw [circulant_mul_transpose_eq_periodicAutocorr, circulant_mul_transpose_eq_periodicAutocorr,
        circulant_mul_transpose_eq_periodicAutocorr, circulant_mul_transpose_eq_periodicAutocorr,
        sub_self,
        periodicAutocorr_zero_pmOne _ G.x1_pm,
        periodicAutocorr_zero_pmOne _ G.x2_pm,
        periodicAutocorr_zero_pmOne _ G.x3_pm,
        periodicAutocorr_zero_pmOne _ G.x4_pm]
    simp; ring
  · simp only [if_neg hij, mul_zero]
    have h_periodic : combinedPeriodic G.toGSData (i - j) = 0 :=
      G.periodic_vanishing _ (fin_sub_val_ne_zero hij)
    unfold combinedPeriodic at h_periodic
    rw [← circulant_mul_transpose_eq_periodicAutocorr,
        ← circulant_mul_transpose_eq_periodicAutocorr,
        ← circulant_mul_transpose_eq_periodicAutocorr,
        ← circulant_mul_transpose_eq_periodicAutocorr] at h_periodic
    unfold gsA gsB gsC gsD
    linarith
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
  refine' ⟨ _, _, _, _ ⟩;
  · convert four_circulant_products_eq G using 1;
    simp [ gsBlockMatrix, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply ];
    simp [ Matrix.toBlocks₁₁ ];
    ext i j; simp [ Matrix.mul_assoc, reversalMatrix_transpose ] ; ring_nf;
    simp [ ← Matrix.mul_assoc, reversalMatrix_mul_reversalMatrix ];
  · convert four_circulant_products_eq G using 1;
    unfold gsBlockMatrix;
    simp [ Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂ ];
    ext i j; simp [ ← Matrix.mul_assoc, trCirculant_mul_transpose_self ] ;
    simp [ reversalMatrix_transpose ] ; ring_nf!;
    simp [ Matrix.mul_assoc, reversalMatrix_mul_reversalMatrix ] ; ring;
  · rw [ gsBlockMatrix ];
    simp [ Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂ ];
    convert four_circulant_products_eq G using 1;
    · ext i j; simp [ Matrix.mul_assoc, trCirculant_mul_transpose_self ] ; ring_nf;
      simp [ ← Matrix.mul_assoc, reversalMatrix_transpose, reversalMatrix_mul_reversalMatrix ] ; ring!;
    · norm_num [ Algebra.smul_def ];
  · convert four_circulant_products_eq G using 1;
    unfold gsBlockMatrix;
    simp [ Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply ];
    simp [ ← Matrix.mul_assoc, trCirculant_mul_transpose_self, reversalMatrix_transpose ];
    ext i j; simp [ Matrix.toBlocks₂₂, Matrix.fromBlocks ] ;
    simp [ Matrix.mul_assoc, reversalMatrix_mul_reversalMatrix ] ; ring!

/-
The upper-right block of `gsBlockMatrix * gsBlockMatrixᵀ` vanishes.
-/
theorem gsBlockMatrix_upper_right_zero {n : Nat} (G : CertifiedGSData n) :
    Matrix.toBlocks₁₂ (gsBlockMatrix G.toGSData * (gsBlockMatrix G.toGSData)ᵀ) = 0 := by
  unfold gsBlockMatrix;
  simp [ Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose ];
  ext ( i j );
  rcases i with ( i | i ) <;> rcases j with ( j | j ) <;> norm_num [ Matrix.mul_assoc, Matrix.transpose_mul, Matrix.transpose_one, Matrix.transpose_neg, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_transpose ];
  · unfold trCirculant;
    simp [ ← Matrix.mul_assoc, reversalMatrix_transpose ];
    simp [ Matrix.mul_assoc, reversalMatrix_mul_reversalMatrix ];
    simp [ ← Matrix.mul_assoc ];
    simp [ gsA, gsB, gsC, gsD, circulant_reversalMatrix_transpose_comm ];
    rw [ circulant_mul_circulant_comm ] ; ring;
  · unfold trCirculant; simp [ Matrix.transpose_mul, Matrix.transpose_transpose ] ;
    simp [ ← Matrix.mul_assoc, reversalMatrix_transpose, reversalMatrix_mul_reversalMatrix ];
    simp [ gsA, gsB, gsC, gsD, circulant_reversalMatrix_transpose_comm ];
    rw [ circulant_mul_circulant_comm ] ; ring;
  · unfold gsA gsB trCirculant;
    simp [ ← Matrix.mul_assoc, reversalMatrix_transpose, reversalMatrix_mul_reversalMatrix ];
    simp [ Matrix.mul_assoc, circulant_mul_circulant_transpose_comm, circulant_reversalMatrix, circulant_transpose_reversalMatrix ];
    rw [ show gsC G.toGSData = circulant G.x3 from rfl ] ; simp [ circulant_mul_circulant_transpose_comm ] ; ring;
  · simp [ ← Matrix.mul_assoc, reversalMatrix_transpose, trCirculant ];
    simp [ Matrix.mul_assoc, reversalMatrix_mul_reversalMatrix ];
    simp [ ← Matrix.mul_assoc, ← circulant_transpose_reversalMatrix, ← circulant_mul_circulant_transpose_comm ];
    simp [ Matrix.mul_assoc, ← circulant_reversalMatrix, gsA, gsB, gsD ];
    simp [ ← Matrix.mul_assoc, ← circulant_mul_circulant_transpose_comm ];
    ring

/-
The lower-left block of `gsBlockMatrix * gsBlockMatrixᵀ` vanishes.
-/
theorem gsBlockMatrix_lower_left_zero {n : Nat} (G : CertifiedGSData n) :
    Matrix.toBlocks₂₁ (gsBlockMatrix G.toGSData * (gsBlockMatrix G.toGSData)ᵀ) = 0 := by
  -- By symmetry, the lower-left block is the transpose of the upper-right block.
  have h_symm : (gsBlockMatrix G.toGSData * (gsBlockMatrix G.toGSData)ᵀ).toBlocks₂₁ = ((gsBlockMatrix G.toGSData * (gsBlockMatrix G.toGSData)ᵀ).toBlocks₁₂)ᵀ := by
    ext i j; simp [ Matrix.toBlocks₁₂, Matrix.toBlocks₂₁ ] ;
    simp [ Matrix.mul_apply, Matrix.transpose_apply ];
    ac_rfl;
  rw [ h_symm, gsBlockMatrix_upper_right_zero G, Matrix.transpose_zero ]

/-! ### Helpers for the explicit proof of `gsBlockMatrix_target_from_blocks` -/

/-- Reconstruct a matrix over `(α ⊕ α) ⊕ (α ⊕ α)` from its four blocks
    when those blocks are `c • 1`, `0`, `0`, `c • 1`. -/
private lemma fromBlocks_eq_smul_one {n : Nat} (c : ℤ)
    {M : Matrix ((Fin n ⊕ Fin n) ⊕ (Fin n ⊕ Fin n)) ((Fin n ⊕ Fin n) ⊕ (Fin n ⊕ Fin n)) ℤ}
    (h11 : M.toBlocks₁₁ = c • 1)
    (h12 : M.toBlocks₁₂ = 0)
    (h21 : M.toBlocks₂₁ = 0)
    (h22 : M.toBlocks₂₂ = c • 1) :
    M = c • 1 := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  rw [h11, h12, h21, h22]
  ext (i | i) (j | j) <;>
  simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply,
    Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_false, smul_eq_mul, mul_zero]

/-- Reconstruct a `(Fin n ⊕ Fin n)` matrix from its four `Fin n`-indexed blocks. -/
private lemma inner_fromBlocks_eq_smul_one {n : Nat} (c : ℤ)
    {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ}
    (h11 : M.toBlocks₁₁ = c • 1)
    (h12 : M.toBlocks₁₂ = 0)
    (h21 : M.toBlocks₂₁ = 0)
    (h22 : M.toBlocks₂₂ = c • 1) :
    M = c • 1 := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  rw [h11, h12, h21, h22]
  ext (i | i) (j | j) <;>
  simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply,
    Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_false, smul_eq_mul, mul_zero]

/-- `H * Hᵀ` is symmetric. -/
private lemma gsProduct_symmetric {n : Nat} (G : CertifiedGSData n) :
    (gsBlockMatrix G.toGSData * (gsBlockMatrix G.toGSData)ᵀ)ᵀ =
    gsBlockMatrix G.toGSData * (gsBlockMatrix G.toGSData)ᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

/-
Off-diagonal (1,2) sub-block of the upper-left quadrant of M·Mᵀ vanishes.

The block expands to:
  -A·(B·R)ᵀ + B·R·Aᵀ + C·R·(D'ᵀ) + D·R·(-C')ᵀ
where A,B,C,D are circulants and D' = (circ x4)ᵀ·R, C' = (circ x3)ᵀ·R.
The first pair cancels by `circulant_reversalMatrix_transpose_comm`,
the second by `circulant_mul_circulant_comm`.
-/
private lemma gsBlock_offdiag_upper_left_12 {n : Nat} (G : CertifiedGSData n) :
    (gsBlockMatrix G.toGSData * (gsBlockMatrix G.toGSData)ᵀ).toBlocks₁₁.toBlocks₁₂ = 0 := by
  ext i j; simp [ gsBlockMatrix ] ; ring_nf;
  unfold gsBlockMatrix at *; simp [ Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply ] ;
  unfold gsC gsD gsA gsB at *; simp [ Matrix.mul_assoc, reversalMatrix_transpose ] ;
  unfold trCirculant at *; simp [ Matrix.mul_assoc, Matrix.transpose_mul, Matrix.transpose_transpose, reversalMatrix_transpose ] ;
  simp [ ← Matrix.mul_assoc, reversalMatrix_mul_reversalMatrix ];
  simp [ Matrix.toBlocks₁₂, circulant_reversalMatrix_transpose_comm, circulant_mul_circulant_comm ]

/-
Off-diagonal (2,1) sub-block of the upper-left quadrant of M·Mᵀ vanishes.
Follows from (1,2) by symmetry of M·Mᵀ: since M = Mᵀ, the (2,1) sub-block
is the transpose of the (1,2) sub-block.
-/
private lemma gsBlock_offdiag_upper_left_21 {n : Nat} (G : CertifiedGSData n) :
    (gsBlockMatrix G.toGSData * (gsBlockMatrix G.toGSData)ᵀ).toBlocks₁₁.toBlocks₂₁ = 0 := by
  -- By symmetry of the matrix, the (2,1) sub-block is the transpose of the (1,2) sub-block.
  have h_symm : (gsBlockMatrix G.toGSData * (gsBlockMatrix G.toGSData)ᵀ).toBlocks₁₁.toBlocks₂₁ = (gsBlockMatrix G.toGSData * (gsBlockMatrix G.toGSData)ᵀ).toBlocks₁₁.toBlocks₁₂.transpose := by
    have h_symm : ∀ (M : Matrix ((Fin n ⊕ Fin n) ⊕ (Fin n ⊕ Fin n)) ((Fin n ⊕ Fin n) ⊕ (Fin n ⊕ Fin n)) ℤ), M.transpose = M → M.toBlocks₁₁.toBlocks₂₁ = M.toBlocks₁₁.toBlocks₁₂.transpose := by
      intros M hM_symm
      ext i j
      simp [Matrix.transpose];
      exact congr_fun ( congr_fun hM_symm _ ) _;
    exact h_symm _ ( by rw [ Matrix.transpose_mul, Matrix.transpose_transpose ] );
  rw [ h_symm, gsBlock_offdiag_upper_left_12, Matrix.transpose_zero ]

/-
Off-diagonal (1,2) sub-block of the lower-right quadrant of M·Mᵀ vanishes.

The block expands to:
  circ x3·(circ x4)ᵀ − (circ x4)ᵀ·circ x3 − circ x1·R·circ x2 + (circ x2)ᵀ·R·(circ x1)ᵀ
The first pair cancels by `circulant_mul_circulant_transpose_comm`,
the second by `circulant_reversalMatrix`, `circulant_transpose_reversalMatrix`,
and `circulant_mul_circulant_transpose_comm`.
-/
private lemma gsBlock_offdiag_lower_right_12 {n : Nat} (G : CertifiedGSData n) :
    (gsBlockMatrix G.toGSData * (gsBlockMatrix G.toGSData)ᵀ).toBlocks₂₂.toBlocks₁₂ = 0 := by
  unfold gsBlockMatrix;
  simp [ ← Matrix.ext_iff ];
  simp [ fromBlocks_transpose, Matrix.fromBlocks_multiply ];
  simp [ Matrix.toBlocks₁₂, Matrix.fromBlocks ];
  unfold trCirculant; simp [ Matrix.mul_assoc ] ;
  simp [ ← Matrix.mul_assoc, reversalMatrix_transpose, reversalMatrix_mul_reversalMatrix ];
  simp [ gsA, gsC, gsD, circulant_mul_circulant_transpose_comm, circulant_reversalMatrix, circulant_transpose_reversalMatrix ];
  simp [ Matrix.mul_assoc, circulant_mul_circulant_transpose_comm ]

/-
Off-diagonal (2,1) sub-block of the lower-right quadrant of M·Mᵀ vanishes.
Follows from (1,2) by symmetry of M·Mᵀ.
-/
private lemma gsBlock_offdiag_lower_right_21 {n : Nat} (G : CertifiedGSData n) :
    (gsBlockMatrix G.toGSData * (gsBlockMatrix G.toGSData)ᵀ).toBlocks₂₂.toBlocks₂₁ = 0 := by
  -- Apply the auxiliary lemma that the transpose of zero is zero.
  have := gsBlock_offdiag_lower_right_12 G;
  ext i j;
  convert congr_arg ( fun m => m j i ) this using 1;
  simp [ Matrix.toBlocks₂₂, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂ ];
  rw [ ← Matrix.transpose_apply ( gsBlockMatrix G.toGSData * ( gsBlockMatrix G.toGSData ) ᵀ ), gsProduct_symmetric ]

/-- The upper-left (2n×2n) block of M·Mᵀ equals (4n)•I. -/
private lemma gsBlock_diag_upper_left {n : Nat} (G : CertifiedGSData n) :
    (gsBlockMatrix G.toGSData * (gsBlockMatrix G.toGSData)ᵀ).toBlocks₁₁ =
    (4 * ↑n : ℤ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) := by
  have ⟨h1, h2, _, _⟩ := gsBlockMatrix_diag_blocks G
  exact inner_fromBlocks_eq_smul_one _ h1 (gsBlock_offdiag_upper_left_12 G)
    (gsBlock_offdiag_upper_left_21 G) h2

/-- The lower-right (2n×2n) block of M·Mᵀ equals (4n)•I. -/
private lemma gsBlock_diag_lower_right {n : Nat} (G : CertifiedGSData n) :
    (gsBlockMatrix G.toGSData * (gsBlockMatrix G.toGSData)ᵀ).toBlocks₂₂ =
    (4 * ↑n : ℤ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) := by
  have ⟨_, _, h3, h4⟩ := gsBlockMatrix_diag_blocks G
  exact inner_fromBlocks_eq_smul_one _ h3 (gsBlock_offdiag_lower_right_12 G)
    (gsBlock_offdiag_lower_right_21 G) h4

/-
The full block product collapses to `(4n) • 1`.
-/
theorem gsBlockMatrix_target_from_blocks {n : Nat} (G : CertifiedGSData n) :
    GSBlockTarget G.toGSData := by
  unfold GSBlockTarget
  exact fromBlocks_eq_smul_one _
    (gsBlock_diag_upper_left G)
    (gsBlockMatrix_upper_right_zero G)
    (gsBlockMatrix_lower_left_zero G)
    (gsBlock_diag_lower_right G)

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
      rw [ GSTarget, gsMatrix_eq_reindex_gsBlockMatrix ];
      -- By definition of reindex, we can rewrite the left-hand side as the submatrix of the block product.
      have h_reindex : (reindex (gsBlockEquiv n) (gsBlockEquiv n)) (gsBlockMatrix G.toGSData) = (gsBlockMatrix G.toGSData).submatrix (gsBlockEquiv n).symm (gsBlockEquiv n).symm := by
        exact reindex_apply (gsBlockEquiv n) (gsBlockEquiv n) (gsBlockMatrix G.toGSData);
      rw [ h_reindex, Matrix.transpose_submatrix ];
      convert congr_arg ( fun m => m.submatrix ( gsBlockEquiv n |> Equiv.symm ) ( gsBlockEquiv n |> Equiv.symm ) ) ( gsBlockMatrix_target_from_blocks G ) using 1;
      · exact submatrix_mul_equiv (gsBlockMatrix G.toGSData) (gsBlockMatrix G.toGSData)ᵀ (⇑(gsBlockEquiv n).symm) (gsBlockEquiv n).symm ⇑(gsBlockEquiv n).symm;
      · ext i j; simp [ Matrix.smul_eq_diagonal_mul ] ;
        by_cases hij : i = j <;> simp [ hij, Matrix.one_apply ]

/-- Final typed GS Hadamard theorem. -/
theorem gsMatrix_isHadamard {n : Nat} (G : CertifiedGSData n) :
    IsHadamardMat (gsMatrix G.toGSData) := by
  exact gsTarget_implies_hadamard G.toGSData (gsMatrix_target G)

end Turyn