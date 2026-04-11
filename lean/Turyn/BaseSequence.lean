import Turyn.TurynType

/-!
# Step 1: Typed Turyn Data and Base Sequences

This file is standalone and does not depend on `Turyn.Hadamard`.
It introduces typed wrappers for signed sequences and Turyn quadruples.
-/

/-- A length-indexed `±1` sequence. -/
structure SignedSeq (n : Nat) where
  data : List Int
  len : data.length = n
  pm : AllPmOne data

/-- A typed Turyn quadruple TT(n). -/
structure TurynType (n : Nat) where
  x : SignedSeq n
  y : SignedSeq n
  z : SignedSeq n
  w : SignedSeq (n - 1)
  vanishing : ∀ s : Nat, 1 ≤ s → s < n →
    combinedAutocorr x.data y.data z.data w.data s = 0

/-- Convert an existing propositional TT witness into the typed wrapper. -/
def IsTurynTypeProp.toTyped {n : Nat} {x y z w : PmSeq}
    (h : IsTurynTypeProp n x y z w) : TurynType n :=
  { x := ⟨x, h.x_len, h.x_pm⟩
    y := ⟨y, h.y_len, h.y_pm⟩
    z := ⟨z, h.z_len, h.z_pm⟩
    w := ⟨w, h.w_len, h.w_pm⟩
    vanishing := h.vanishing }

/-- Convert a Boolean-style TT certificate into the typed wrapper. -/
def IsTurynType.toTyped {n : Nat} {x y z w : PmSeq}
    (h : IsTurynType n x y z w) : TurynType n :=
  (IsTurynType.toProp h).toTyped

/-- Negate every entry in a sequence. -/
def negSeq (a : List Int) : List Int := a.map (· * (-1))

/-- Base sequences from TT(n) = (X, Y, Z, W):
    A = Z ++ W, B = Z ++ (-W), C = X, D = Y. -/
def baseSequences (x y z w : PmSeq) :
    PmSeq × PmSeq × PmSeq × PmSeq :=
  (z ++ w, z ++ negSeq w, x, y)

/-- Typed base-sequence data for Step 1. -/
structure BaseSeqData (n : Nat) where
  a : SignedSeq (2 * n - 1)
  b : SignedSeq (2 * n - 1)
  c : SignedSeq n
  d : SignedSeq n
  vanishing : ∀ s : Nat, 1 ≤ s →
    aperiodicAutocorr a.data s + aperiodicAutocorr b.data s +
    aperiodicAutocorr c.data s + aperiodicAutocorr d.data s = 0

/-! ### Helper lemmas for Step 1 -/

open Finset BigOperators

/-- negSeq preserves length. -/
@[simp] lemma negSeq_length_eq (a : List Int) : (negSeq a).length = a.length := by
  simp [negSeq]

/-- AllPmOne is preserved by append. -/
lemma AllPmOne_append {a b : List Int} (ha : AllPmOne a) (hb : AllPmOne b) :
    AllPmOne (a ++ b) := by
  intro v hv
  rw [List.mem_append] at hv
  exact hv.elim (ha v) (hb v)

/-- negSeq preserves AllPmOne. -/
lemma AllPmOne_negSeq {a : List Int} (ha : AllPmOne a) : AllPmOne (negSeq a) := by
  intro v hv
  simp only [negSeq, List.mem_map] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  rcases ha u hu with h | h <;> subst h <;> decide

/-- Indexing into negSeq negates the value. -/
lemma negSeq_getD (w : List Int) (i : Nat) :
    (negSeq w).getD i 0 = w.getD i 0 * (-1) := by
  simp only [negSeq, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp

/-- Aperiodic autocorrelation vanishes when the lag meets or exceeds the length. -/
lemma aperiodicAutocorr_zero_of_ge' (a : List Int) (s : Nat) (h : s ≥ a.length) :
    aperiodicAutocorr a s = 0 := by
  unfold aperiodicAutocorr; exact if_pos h

/-- Pointwise cross-term cancellation. -/
private lemma pointwise_cancel (z w : List Int) (s i : Nat) :
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

/-- Cross-term cancellation:
    N_{Z++W}(s) + N_{Z++(-W)}(s) = 2·N_Z(s) + 2·N_W(s). -/
lemma concat_neg_autocorr_sum' (z w : List Int) (s : Nat) :
    aperiodicAutocorr (z ++ w) s + aperiodicAutocorr (z ++ negSeq w) s =
    2 * aperiodicAutocorr z s + 2 * aperiodicAutocorr w s := by
  have hnw : (negSeq w).length = w.length := negSeq_length_eq w
  unfold aperiodicAutocorr
  simp only [List.length_append, hnw]
  set nz := z.length; set nw := w.length
  by_cases hszw : nz + nw ≤ s
  · simp only [show s ≥ nz + nw from hszw, ↓reduceIte,
               show s ≥ nz from by omega, show s ≥ nw from by omega]; ring
  · simp only [show ¬(nz + nw ≤ s) from by omega, ↓reduceIte]
    rw [← Finset.sum_add_distrib]
    conv_lhs => arg 2; ext i; rw [pointwise_cancel z w s i]
    rw [Finset.sum_ite]
    simp only [Finset.sum_ite, Finset.sum_const_zero, zero_add]
    by_cases hsz : nz ≤ s
    · simp only [hsz, ↓reduceIte]
      have hfilt_empty : (range (nz + nw - s)).filter (fun i => i + s < nz) = ∅ := by
        ext x; simp [Finset.mem_filter, Finset.mem_range]; omega
      rw [hfilt_empty, Finset.sum_empty, zero_add]
      by_cases hsw : nw ≤ s
      · simp only [hsw, ↓reduceIte]
        have hfilt_empty2 : ((range (nz + nw - s)).filter (fun i => ¬(i + s < nz))).filter
            (fun i => ¬(↑i < nz)) = ∅ := by
          ext x; simp [Finset.mem_filter, Finset.mem_range]; omega
        rw [hfilt_empty2, Finset.sum_empty]; ring
      · simp only [hsw, ↓reduceIte]
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
    · simp only [hsz, ↓reduceIte]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr
        · ext x; simp [Finset.mem_filter, Finset.mem_range]; omega
        · intro i _; ring
      · by_cases hsw : nw ≤ s
        · simp only [hsw, ↓reduceIte]
          have hfilt_empty2 : ((range (nz + nw - s)).filter (fun i => ¬(i + s < nz))).filter
              (fun i => ¬(↑i < nz)) = ∅ := by
            ext x; simp [Finset.mem_filter, Finset.mem_range]; omega
          rw [hfilt_empty2, Finset.sum_empty]; ring
        · simp only [hsw, ↓reduceIte]
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

/-- Cross-term cancellation:
    `N_{Z++W}(s) + N_{Z++(-W)}(s) = 2·N_Z(s) + 2·N_W(s)`. -/
lemma concat_neg_autocorr_sum (z w : PmSeq) (s : Nat) :
    aperiodicAutocorr (z ++ w) s + aperiodicAutocorr (z ++ negSeq w) s =
    2 * aperiodicAutocorr z s + 2 * aperiodicAutocorr w s :=
  concat_neg_autocorr_sum' z w s

/-- Base-sequence theorem (KTR2005, Theorem 1). -/
theorem base_seq_vanishing_prop {n : Nat} {x y z w : PmSeq}
    (htt : IsTurynTypeProp n x y z w) (_hn : n ≥ 1)
    {s : Nat} (hs1 : 1 ≤ s) :
    aperiodicAutocorr (z ++ w) s + aperiodicAutocorr (z ++ negSeq w) s +
    aperiodicAutocorr x s + aperiodicAutocorr y s = 0 := by
  rw [concat_neg_autocorr_sum]
  by_cases hsn : s < n
  · have hvan := htt.vanishing s hs1 hsn
    unfold combinedAutocorr at hvan
    linarith
  · simp only [not_lt] at hsn
    rw [aperiodicAutocorr_zero_of_ge' z s (by rw [htt.z_len]; omega),
        aperiodicAutocorr_zero_of_ge' w s (by rw [htt.w_len]; omega),
        aperiodicAutocorr_zero_of_ge' x s (by rw [htt.x_len]; omega),
        aperiodicAutocorr_zero_of_ge' y s (by rw [htt.y_len]; omega)]
    ring

/-- Step 1 interface: every typed Turyn quadruple yields typed base sequences. -/
def step1 {n : Nat} (T : TurynType n) : BaseSeqData n :=
  { a := ⟨T.z.data ++ T.w.data,
         by simp [T.z.len, T.w.len]; omega,
         AllPmOne_append T.z.pm T.w.pm⟩
    b := ⟨T.z.data ++ negSeq T.w.data,
         by simp [negSeq_length_eq, T.z.len, T.w.len]; omega,
         AllPmOne_append T.z.pm (AllPmOne_negSeq T.w.pm)⟩
    c := T.x
    d := T.y
    vanishing := by
      intro s hs
      rw [concat_neg_autocorr_sum]
      by_cases hsn : s < n
      · have := T.vanishing s hs hsn
        unfold combinedAutocorr at this
        linarith
      · simp only [not_lt] at hsn
        rw [aperiodicAutocorr_zero_of_ge' T.z.data s (by rw [T.z.len]; omega),
            aperiodicAutocorr_zero_of_ge' T.w.data s (by rw [T.w.len]; omega),
            aperiodicAutocorr_zero_of_ge' T.x.data s (by rw [T.x.len]; omega),
            aperiodicAutocorr_zero_of_ge' T.y.data s (by rw [T.y.len]; omega)]
        ring }
