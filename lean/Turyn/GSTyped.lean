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

/-- The block GS matrix reindexes to the flat `Fin (4n)` GS matrix. -/
theorem gsMatrix_eq_reindex_gsBlockMatrix {n : Nat} (G : GSData n) :
    gsMatrix G = Matrix.reindex (gsBlockEquiv n) (gsBlockEquiv n) (gsBlockMatrix G) := by
  sorry

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

/-- Step 1 of the typed GS block proof: each diagonal `n × n` block of
`gsBlockMatrix * gsBlockMatrixᵀ` is `(4 * n) • 1`. -/
theorem gsBlockMatrix_diag_blocks {n : Nat} (G : CertifiedGSData n) :
    let M := gsBlockMatrix G.toGSData * (gsBlockMatrix G.toGSData)ᵀ
    Matrix.toBlocks₁₁ (Matrix.toBlocks₁₁ M) = (4 * n : Int) • (1 : IntMat n) ∧
    Matrix.toBlocks₂₂ (Matrix.toBlocks₁₁ M) = (4 * n : Int) • (1 : IntMat n) ∧
    Matrix.toBlocks₁₁ (Matrix.toBlocks₂₂ M) = (4 * n : Int) • (1 : IntMat n) ∧
    Matrix.toBlocks₂₂ (Matrix.toBlocks₂₂ M) = (4 * n : Int) • (1 : IntMat n) := by
  sorry

/-- Step 2 of the typed GS block proof: the upper-right 2×2 block of
`gsBlockMatrix * gsBlockMatrixᵀ` vanishes. -/
theorem gsBlockMatrix_upper_right_zero {n : Nat} (G : CertifiedGSData n) :
    Matrix.toBlocks₁₂ (gsBlockMatrix G.toGSData * (gsBlockMatrix G.toGSData)ᵀ) = 0 := by
  sorry

/-- Step 3 of the typed GS block proof: the lower-left 2×2 block of
`gsBlockMatrix * gsBlockMatrixᵀ` vanishes. -/
theorem gsBlockMatrix_lower_left_zero {n : Nat} (G : CertifiedGSData n) :
    Matrix.toBlocks₂₁ (gsBlockMatrix G.toGSData * (gsBlockMatrix G.toGSData)ᵀ) = 0 := by
  sorry

/-- Step 4 of the typed GS block proof: the full block product collapses to
`(4 * n) • 1`. -/
theorem gsBlockMatrix_target_from_blocks {n : Nat} (G : CertifiedGSData n) :
    GSBlockTarget G.toGSData := by
  sorry

/-- Block-matrix GS orthogonality theorem in the right algebraic form. -/
theorem gsBlockMatrix_target {n : Nat} (G : CertifiedGSData n) :
    GSBlockTarget G.toGSData := by
  exact gsBlockMatrix_target_from_blocks G

/-- The typed GS matrix is Hadamard once the matrix-algebra target identity is proved. -/
theorem gsTarget_implies_hadamard {n : Nat} (G : GSData n) (h : GSTarget G) :
    IsHadamardMat (gsMatrix G) := by
  constructor
  · exact gsMatrix_pmOne G
  · exact h

/-- Typed GS orthogonality target, isolated as the remaining matrix-algebra theorem. -/
theorem gsMatrix_target {n : Nat} (G : CertifiedGSData n) :
    GSTarget G.toGSData := by
  sorry

/-- Final typed GS Hadamard theorem. -/
theorem gsMatrix_isHadamard {n : Nat} (G : CertifiedGSData n) :
    IsHadamardMat (gsMatrix G.toGSData) := by
  exact gsTarget_implies_hadamard G.toGSData (gsMatrix_target G)

end Turyn
