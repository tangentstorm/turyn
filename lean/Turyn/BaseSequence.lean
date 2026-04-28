import Turyn.TurynType
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option linter.unusedSimpArgs false

open Finset BigOperators

/-!
# Base Sequences

Typed signed-sequence wrappers, typed Turyn-type input, and the standard
construction of base sequences `(A,B,C,D)` from a Turyn-type sequence. The
main theorem in this file proves that these base sequences satisfy the required
combined aperiodic autocorrelation identity.
-/

/-- Negate every entry in a function-typed sequence. -/
def negSeqFn {n : Nat} (a : Fin n → Int) : Fin n → Int := fun i => -(a i)

/-- Concatenate two function-typed sequences: a positive-length-respecting
analogue of `List.append` on `Fin n`-indexed functions. -/
def appendFn {n m : Nat} (a : Fin n → Int) (b : Fin m → Int) : Fin (n + m) → Int :=
  fun i =>
    if h : i.1 < n then a ⟨i.1, h⟩
    else b ⟨i.1 - n, by have := i.2; omega⟩

@[simp] lemma negSeqFn_apply {n : Nat} (a : Fin n → Int) (i : Fin n) :
    negSeqFn a i = -(a i) := rfl

lemma appendFn_left {n m : Nat} (a : Fin n → Int) (b : Fin m → Int) (i : Fin (n + m))
    (h : i.1 < n) :
    appendFn a b i = a ⟨i.1, h⟩ := by
  unfold appendFn; simp [h]

lemma appendFn_right {n m : Nat} (a : Fin n → Int) (b : Fin m → Int) (i : Fin (n + m))
    (h : ¬ i.1 < n) :
    appendFn a b i = b ⟨i.1 - n, by have := i.2; omega⟩ := by
  unfold appendFn; simp [h]

lemma negSeqFn_AllPmOne {n : Nat} {a : Fin n → Int} (h : AllPmOne a) :
    AllPmOne (negSeqFn a) := by
  intro i; simp [negSeqFn]
  rcases h i with h1 | h1 <;> rw [h1] <;> simp

/-- AllPmOne is preserved under appending. -/
lemma AllPmOne_appendFn {n m : Nat} {a : Fin n → Int} {b : Fin m → Int}
    (ha : AllPmOne a) (hb : AllPmOne b) : AllPmOne (appendFn a b) := by
  intro i
  unfold appendFn
  by_cases h : i.1 < n
  · simp [h]; exact ha _
  · simp [h]; exact hb _

/-- Alternation: entry at position `i` gets factor `(-1)^i`. -/
def Turyn.altSeqFn {n : Nat} (a : Fin n → Int) : Fin n → Int :=
  fun i => (if i.1 % 2 = 0 then (1 : Int) else -1) * a i

@[simp] lemma Turyn.altSeqFn_apply {n : Nat} (a : Fin n → Int) (i : Fin n) :
    Turyn.altSeqFn a i = (if i.1 % 2 = 0 then (1 : Int) else -1) * a i := rfl

/-- Reversal: entry at position `i` becomes the entry at position `n - 1 - i`. -/
def reverseFn {n : Nat} (a : Fin n → Int) : Fin n → Int :=
  fun i => a ⟨n - 1 - i.1, by have := i.2; omega⟩

@[simp] lemma reverseFn_apply {n : Nat} (a : Fin n → Int) (i : Fin n) :
    reverseFn a i = a ⟨n - 1 - i.1, by have := i.2; omega⟩ := rfl

/-- AllPmOne is preserved under alternation. -/
lemma AllPmOne_altSeqFn {n : Nat} {a : Fin n → Int} (h : AllPmOne a) :
    AllPmOne (Turyn.altSeqFn a) := by
  intro i; unfold Turyn.altSeqFn
  rcases h i with h1 | h1 <;> rw [h1] <;> split_ifs <;> simp

/-- AllPmOne is preserved under reversal. -/
lemma AllPmOne_reverseFn {n : Nat} {a : Fin n → Int} (h : AllPmOne a) :
    AllPmOne (reverseFn a) := by
  intro i; unfold reverseFn; exact h _

/-! ### Sign-pattern helpers for `aperiodicAutocorr_altSeqFn` -/

private lemma ite_mod2_eq_neg_one_pow (k : Nat) :
    (if k % 2 = 0 then (1 : Int) else -1) = (-1) ^ k := by
  induction k with
  | zero => norm_num
  | succ j ih =>
    rw [pow_succ]
    by_cases hj : j % 2 = 0
    · rw [if_neg (by omega), ← ih, if_pos hj]; ring
    · rw [if_pos (by omega), ← ih, if_neg hj]; ring

private lemma sign_product_eq (i s : Nat) :
    ((if i % 2 = 0 then (1 : Int) else -1) *
      (if (i + s) % 2 = 0 then (1 : Int) else -1)) = (-1 : Int) ^ s := by
  rw [ite_mod2_eq_neg_one_pow, ite_mod2_eq_neg_one_pow, ← pow_add]
  rw [show i + (i + s) = 2 * i + s from by ring,
      pow_add, pow_mul, neg_one_sq, one_pow, one_mul]

/-- Alternation scales aperiodic autocorrelation by `(-1)^s`. -/
lemma aperiodicAutocorr_altSeqFn {n : Nat} (a : Fin n → Int) (s : Nat) :
    aperiodicAutocorr (Turyn.altSeqFn a) s = (-1 : Int) ^ s * aperiodicAutocorr a s := by
  unfold aperiodicAutocorr
  by_cases h : s ≥ n
  · simp [h]
  · simp only [h, ↓reduceIte]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hir := Finset.mem_range.mp hi
    have hi_lt : i < n := by omega
    have his_lt : i + s < n := by omega
    rw [lookupNat_of_lt _ hi_lt, lookupNat_of_lt _ his_lt,
        lookupNat_of_lt _ hi_lt, lookupNat_of_lt _ his_lt]
    rw [Turyn.altSeqFn_apply, Turyn.altSeqFn_apply]
    rw [show
          (if (⟨i, hi_lt⟩ : Fin n).1 % 2 = 0 then (1 : Int) else -1) * a ⟨i, hi_lt⟩ *
            ((if (⟨i + s, his_lt⟩ : Fin n).1 % 2 = 0 then (1 : Int) else -1) *
              a ⟨i + s, his_lt⟩) =
          ((if i % 2 = 0 then (1 : Int) else -1) *
            (if (i + s) % 2 = 0 then (1 : Int) else -1)) *
          (a ⟨i, hi_lt⟩ * a ⟨i + s, his_lt⟩) from by ring]
    rw [sign_product_eq]

/-- Reversal preserves aperiodic autocorrelation. -/
lemma aperiodicAutocorr_reverseFn {n : Nat} (a : Fin n → Int) (s : Nat) :
    aperiodicAutocorr (reverseFn a) s = aperiodicAutocorr a s := by
  unfold aperiodicAutocorr
  by_cases h : s ≥ n
  · simp [h]
  · simp only [h, ↓reduceIte]
    push_neg at h
    apply Finset.sum_nbij (fun i => n - 1 - s - i)
    · intro i hi
      exact Finset.mem_range.mpr (by rw [Finset.mem_range] at hi; omega)
    · intro i₁ hi₁ i₂ hi₂ heq
      rw [Finset.mem_coe, Finset.mem_range] at hi₁ hi₂
      change n - 1 - s - i₁ = n - 1 - s - i₂ at heq
      omega
    · intro j hj
      rw [Finset.mem_coe, Finset.mem_range] at hj
      refine ⟨n - 1 - s - j, ?_, ?_⟩
      · rw [Finset.mem_coe, Finset.mem_range]; omega
      · show n - 1 - s - (n - 1 - s - j) = j; omega
    · intro i hi
      have hir := Finset.mem_range.mp hi
      have hi_lt : i < n := by omega
      have his_lt : i + s < n := by omega
      have hr1 : n - 1 - s - i < n := by omega
      have hr2 : n - 1 - s - i + s < n := by omega
      rw [lookupNat_of_lt _ hi_lt, lookupNat_of_lt _ his_lt,
          lookupNat_of_lt _ hr1, lookupNat_of_lt _ hr2]
      have e1 : reverseFn a ⟨i, hi_lt⟩ = a ⟨n - 1 - s - i + s, hr2⟩ := by
        unfold reverseFn
        congr 1
        exact Fin.ext (by simp; omega)
      have e2 : reverseFn a ⟨i + s, his_lt⟩ = a ⟨n - 1 - s - i, hr1⟩ := by
        unfold reverseFn
        congr 1
        exact Fin.ext (by simp; omega)
      rw [e1, e2, mul_comm]

/-- Typed base-sequence data for Step 1. -/
structure BaseSeqData (n : Nat) where
  a : PmSeq (2 * n - 1)
  b : PmSeq (2 * n - 1)
  c : PmSeq n
  d : PmSeq n
  vanishing : ∀ s : Nat, 1 ≤ s →
    aperiodicAutocorr a.data s + aperiodicAutocorr b.data s +
    aperiodicAutocorr c.data s + aperiodicAutocorr d.data s = 0

/-! ### Helper lemmas for Step 1 -/

/-- Aperiodic autocorrelation vanishes when the lag meets or exceeds the length. -/
lemma aperiodicAutocorr_zero_of_ge {n : Nat} (a : Fin n → Int) (s : Nat) (h : s ≥ n) :
    aperiodicAutocorr a s = 0 := by
  unfold aperiodicAutocorr; exact if_pos h

/-- Aperiodic autocorrelation of `negSeqFn a` equals that of `a`. -/
lemma aperiodicAutocorr_negSeqFn {n : Nat} (a : Fin n → Int) (s : Nat) :
    aperiodicAutocorr (negSeqFn a) s = aperiodicAutocorr a s := by
  unfold aperiodicAutocorr
  by_cases h : s ≥ n
  · simp [h]
  · simp only [h, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro i _
    unfold lookupNat
    by_cases h1 : i < n
    · by_cases h2 : i + s < n
      · simp [h1, h2, negSeqFn]
      · simp [h1, h2, negSeqFn]
    · simp [h1]

/-- Pointwise cross-term cancellation for the `(Z++W) / (Z++(-W))` pair. -/
private lemma pointwise_cancel_fn {nz nw : Nat} (z : Fin nz → Int) (w : Fin nw → Int)
    (s i : Nat) :
    lookupNat (appendFn z w) i * lookupNat (appendFn z w) (i + s) +
    lookupNat (appendFn z (negSeqFn w)) i * lookupNat (appendFn z (negSeqFn w)) (i + s) =
    if i + s < nz then
      2 * (lookupNat z i * lookupNat z (i + s))
    else if i < nz then
      0
    else
      2 * (lookupNat w (i - nz) * lookupNat w (i + s - nz)) := by
  -- Decompose by case analysis on which segment i and i+s land in.
  unfold lookupNat appendFn
  by_cases hbi : i < nz + nw
  · by_cases hbis : i + s < nz + nw
    · -- both in range
      simp only [hbi, ↓reduceDIte, hbis]
      by_cases his : i + s < nz
      · have hi : i < nz := by omega
        simp only [his, ↓reduceIte, hi]
        simp [hi, his, hbi, hbis]; ring
      · simp only [his, ↓reduceIte]
        by_cases hi : i < nz
        · simp only [hi, ↓reduceIte]
          have hwis : i + s - nz < nw := by omega
          simp only [hi, his, hwis, ↓reduceDIte, negSeqFn]
          ring
        · simp only [hi, ↓reduceIte]
          have hwi : i - nz < nw := by omega
          have hwis : i + s - nz < nw := by omega
          simp only [hi, his, hwi, hwis, ↓reduceDIte, negSeqFn]
          ring
    · -- i in range, i+s out of range
      simp only [hbi, ↓reduceDIte, hbis]
      by_cases his : i + s < nz
      · -- can't be: i + s out of total range but in nz < nz+nw
        omega
      · simp only [his, ↓reduceIte]
        by_cases hi : i < nz
        · simp only [hi, ↓reduceIte]
          -- (i+s) >= nz+nw, so out of w as well
          have hno : ¬ ((i+s) - nz < nw) := by omega
          simp [hno]
        · simp only [hi, ↓reduceIte]
          have hno : ¬ ((i+s) - nz < nw) := by omega
          simp [hno, negSeqFn]
  · -- i out of total range
    simp only [hbi, ↓reduceDIte]
    by_cases hbis : i + s < nz + nw
    · omega
    · simp only [hbis, ↓reduceDIte]
      by_cases his : i + s < nz
      · omega
      · simp only [his, ↓reduceIte]
        by_cases hi : i < nz
        · omega
        · simp only [hi, ↓reduceIte]
          have h1 : ¬ ((i) - nz < nw) := by omega
          have h2 : ¬ ((i+s) - nz < nw) := by omega
          simp [h1, h2]

/-- Cross-term cancellation:
    N_{Z++W}(s) + N_{Z++(-W)}(s) = 2·N_Z(s) + 2·N_W(s). -/
lemma concat_neg_autocorr_sum_fn {nz nw : Nat} (z : Fin nz → Int) (w : Fin nw → Int)
    (s : Nat) :
    aperiodicAutocorr (appendFn z w) s + aperiodicAutocorr (appendFn z (negSeqFn w)) s =
    2 * aperiodicAutocorr z s + 2 * aperiodicAutocorr w s := by
  unfold aperiodicAutocorr
  by_cases hszw : nz + nw ≤ s
  · simp only [show s ≥ nz + nw from hszw, ↓reduceIte,
               show s ≥ nz from by omega, show s ≥ nw from by omega]; ring
  · simp only [show ¬(nz + nw ≤ s) from by omega, ↓reduceIte]
    rw [← Finset.sum_add_distrib]
    conv_lhs => arg 2; ext i; rw [pointwise_cancel_fn z w s i]
    rw [Finset.sum_ite]
    simp only [Finset.sum_ite, Finset.sum_const_zero, zero_add]
    by_cases hsz : nz ≤ s
    · simp only [show s ≥ nz from hsz, ↓reduceIte]
      have hfilt_empty : (range (nz + nw - s)).filter (fun i => i + s < nz) = ∅ := by
        ext x; simp [Finset.mem_filter, Finset.mem_range]; omega
      rw [hfilt_empty, Finset.sum_empty, zero_add]
      by_cases hsw : nw ≤ s
      · simp only [show s ≥ nw from hsw, ↓reduceIte]
        have hfilt_empty2 : ((range (nz + nw - s)).filter (fun i => ¬(i + s < nz))).filter
            (fun i => ¬(↑i < nz)) = ∅ := by
          ext x; simp [Finset.mem_filter, Finset.mem_range]; omega
        rw [hfilt_empty2, Finset.sum_empty]; ring
      · simp only [show ¬ (s ≥ nw) from by omega, ↓reduceIte]
        have hfilt_eq : ((range (nz + nw - s)).filter (fun i => ¬(i + s < nz))).filter
            (fun i => ¬(↑i < nz)) = Finset.Ico nz (nz + nw - s) := by
          ext x; simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, not_lt]; omega
        rw [hfilt_eq, Finset.sum_Ico_eq_sum_range]
        simp only [mul_zero, zero_add]
        rw [Finset.mul_sum]
        have hrange : nz + nw - s - nz = nw - s := by omega
        apply Finset.sum_congr (by rw [hrange])
        intro i _
        have h1 : nz + i - nz = i := by omega
        have h2 : nz + i + s - nz = i + s := by omega
        rw [h1, h2]
    · simp only [show ¬ (s ≥ nz) from by omega, ↓reduceIte]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr
        · ext x; simp [Finset.mem_filter, Finset.mem_range]; omega
        · intro i _; ring
      · by_cases hsw : nw ≤ s
        · simp only [show s ≥ nw from hsw, ↓reduceIte]
          have hfilt_empty2 : ((range (nz + nw - s)).filter (fun i => ¬(i + s < nz))).filter
              (fun i => ¬(↑i < nz)) = ∅ := by
            ext x; simp [Finset.mem_filter, Finset.mem_range]; omega
          rw [hfilt_empty2, Finset.sum_empty]; ring
        · simp only [show ¬ (s ≥ nw) from by omega, ↓reduceIte]
          rw [Finset.mul_sum]
          have hfilt_eq : ((range (nz + nw - s)).filter (fun i => ¬(i + s < nz))).filter
              (fun i => ¬(↑i < nz)) = Finset.Ico nz (nz + nw - s) := by
            ext x; simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, not_lt]; omega
          rw [hfilt_eq, Finset.sum_Ico_eq_sum_range]
          have hrange : nz + nw - s - nz = nw - s := by omega
          apply Finset.sum_congr (by rw [hrange])
          intro i _
          show 2 * (lookupNat w (nz + i - nz) * lookupNat w (nz + i + s - nz)) =
               2 * (lookupNat w i * lookupNat w (i + s))
          have h1 : nz + i - nz = i := by omega
          have h2 : nz + i + s - nz = i + s := by omega
          rw [h1, h2]

/-- Length identity: `2 * n - 1 = n + (n - 1)` for all `n`.  (When `n = 0`,
both sides reduce to `0` since `2 * 0 - 1` and `0 + (0 - 1)` are both `0`
in `Nat`.) -/
private lemma two_n_sub_one_eq (n : Nat) : 2 * n - 1 = n + (n - 1) := by
  rcases n with _ | n
  · rfl
  · simp [Nat.mul_succ]; omega

/-- Build the typed `PmSeq (2*n - 1)` for component `a` of step 1 from a function
on `Fin (n + (n - 1))`.  The recast is just a relabel of the underlying `Nat`
index — `aperiodicAutocorr_step1_pmSeq` shows the autocorrelation is
unchanged. -/
private def step1_pmSeq {n : Nat} (f : Fin (n + (n - 1)) → Int)
    (h : AllPmOne f) : PmSeq (2 * n - 1) :=
  ⟨fun i => f ⟨i.1, by have := i.2; have := two_n_sub_one_eq n; omega⟩, by
    intro i
    exact h _⟩

/-- The autocorrelation of `step1_pmSeq f h` agrees with that of `f` itself. -/
private lemma aperiodicAutocorr_step1_pmSeq {n : Nat} (f : Fin (n + (n - 1)) → Int)
    (h : AllPmOne f) (s : Nat) :
    aperiodicAutocorr (step1_pmSeq f h).data s = aperiodicAutocorr f s := by
  unfold aperiodicAutocorr step1_pmSeq lookupNat
  have hlen : 2 * n - 1 = n + (n - 1) := two_n_sub_one_eq n
  by_cases hs : s ≥ 2 * n - 1
  · simp [hs, show s ≥ n + (n-1) from by omega]
  · simp only [hs, ↓reduceIte, show ¬(s ≥ n + (n-1)) from by omega]
    have hlenSub : 2 * n - 1 - s = n + (n - 1) - s := by omega
    apply Finset.sum_congr (by rw [hlenSub])
    intro i _
    by_cases h1 : i < 2 * n - 1
    · have h1' : i < n + (n - 1) := by omega
      simp only [h1, ↓reduceDIte, h1']
      by_cases h2 : i + s < 2 * n - 1
      · have h2' : i + s < n + (n - 1) := by omega
        simp only [h2, ↓reduceDIte, h2']
      · have h2' : ¬ i + s < n + (n - 1) := by omega
        simp only [h2, ↓reduceDIte, h2']
    · have h1' : ¬ i < n + (n - 1) := by omega
      simp [h1, h1']

/-- Step 1 interface: every typed Turyn quadruple yields typed base sequences. -/
def step1 {n : Nat} (T : TurynType n) : BaseSeqData n :=
  let castA : Fin (n + (n - 1)) → Int := appendFn T.Z.data T.W.data
  let castB : Fin (n + (n - 1)) → Int := appendFn T.Z.data (negSeqFn T.W.data)
  let pmA : AllPmOne castA := AllPmOne_appendFn T.Z.pm T.W.pm
  let pmB : AllPmOne castB := AllPmOne_appendFn T.Z.pm (negSeqFn_AllPmOne T.W.pm)
  { a := step1_pmSeq castA pmA
    b := step1_pmSeq castB pmB
    c := T.X
    d := T.Y
    vanishing := by
      intro s hs
      rw [aperiodicAutocorr_step1_pmSeq castA pmA s,
          aperiodicAutocorr_step1_pmSeq castB pmB s]
      rw [concat_neg_autocorr_sum_fn]
      by_cases hsn : s < n
      · have := T.vanishing s hs hsn
        unfold combinedAutocorr at this
        linarith
      · simp only [not_lt] at hsn
        have hzx : aperiodicAutocorr T.Z.data s = 0 := aperiodicAutocorr_zero_of_ge _ _ hsn
        have hwx : aperiodicAutocorr T.W.data s = 0 :=
          aperiodicAutocorr_zero_of_ge _ _ (by omega)
        have hxx : aperiodicAutocorr T.X.data s = 0 := aperiodicAutocorr_zero_of_ge _ _ hsn
        have hyx : aperiodicAutocorr T.Y.data s = 0 := aperiodicAutocorr_zero_of_ge _ _ hsn
        rw [hzx, hwx, hxx, hyx]; ring }
