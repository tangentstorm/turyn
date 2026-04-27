import Turyn.TurynType
import Turyn.BaseSequence
import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Equivalence and canonical representatives for Turyn-type sequences

Based on:
- Best, D.J., Đoković, D.Ž., Kharaghani, H., and Ramp, H.,
  "Turyn Type Sequences: Status Report," arXiv:1206.4107v1, 2013.

This file formalizes the canonical normalization proof for Turyn-type sequences.
Every Turyn-type quadruple (A,B,C,D) of lengths (n,n,n,n−1) can be brought to a
canonical form using four families of elementary transformations:
- (T1) Negate one component
- (T2) Reverse one component
- (T3) Alternate all four components (multiply entry i by (−1)^i)
- (T4) Swap A and B

The six-step normalization procedure produces a canonical representative from
each equivalence class:
1. Normalize endpoints
2. Normalize the first asymmetric index of A
3. Normalize the first asymmetric index of B
4. Normalize the first symmetric index of C
5. Normalize the first exceptional index of D
6. Normalize the A/B tie-breaking condition
-/

open Finset BigOperators

/-! ### Sequence operations -/

/-- Alternation of a sequence: entry at 0-indexed position `i` gets factor `(-1)^i`. -/
def Turyn.altSeq (X : List Int) : List Int :=
  (List.range X.length).map (fun i => ((if i % 2 = 0 then 1 else -1) : Int) * X.getD i 0)

/-! ### Length preservation -/

@[simp] lemma Turyn.altSeq_length (X : List Int) : (Turyn.altSeq X).length = X.length := by
  simp [Turyn.altSeq]

/-! ### AllPmOne preservation -/

lemma AllPmOne_neg {X : List Int} (h : AllPmOne X) : AllPmOne (negSeq X) := by
  intro v hv
  simp only [negSeq, List.mem_map] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  rcases h u hu with rfl | rfl <;> simp

lemma AllPmOne_reverse {X : List Int} (h : AllPmOne X) : AllPmOne X.reverse := by
  intro v hv; exact h v (List.mem_reverse.mp hv)

lemma AllPmOne_alt {X : List Int} (h : AllPmOne X) : AllPmOne (Turyn.altSeq X) := by
  intro x hx
  simp only [Turyn.altSeq, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hmem : X.getD i 0 ∈ X := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  have hv := h (X.getD i 0) hmem
  rcases hv with h1 | h1 <;> rw [h1] <;> split_ifs <;> norm_num

/-! ### Private helpers for autocorrelation proofs -/

private lemma list_reverse_getD (a : List Int) (i : Nat) (hi : i < a.length) :
    a.reverse.getD i 0 = a.getD (a.length - 1 - i) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  have hi' : i < a.reverse.length := by rwa [List.length_reverse]
  rw [List.getElem?_eq_getElem hi', List.getElem_reverse hi']
  rw [List.getElem?_eq_getElem (by rw [List.length_reverse] at hi'; omega)]

private lemma ite_mod2_eq_neg_one_pow (n : Nat) :
    (if n % 2 = 0 then (1:Int) else -1) = (-1) ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    by_cases hk : k % 2 = 0
    · rw [if_neg (by omega), ← ih, if_pos hk]; ring
    · rw [if_pos (by omega), ← ih, if_neg hk]; ring

private lemma sign_product_eq (i s : Nat) :
    ((if i % 2 = 0 then (1:Int) else -1) * (if (i + s) % 2 = 0 then (1:Int) else -1)) =
    (-1 : Int) ^ s := by
  rw [ite_mod2_eq_neg_one_pow, ite_mod2_eq_neg_one_pow, ← pow_add]
  rw [show i + (i + s) = 2 * i + s from by ring, pow_add, pow_mul, neg_one_sq, one_pow, one_mul]

private lemma altSeq_getD_aux (X : List Int) (i : Nat) (hi : i < X.length) :
    (Turyn.altSeq X).getD i 0 = (if i % 2 = 0 then 1 else -1) * X.getD i 0 := by
  unfold Turyn.altSeq
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  have hi2 : i < (List.range X.length).length := by rw [List.length_range]; exact hi
  rw [List.getElem?_eq_getElem hi2]
  simp only [Option.map, Option.getD, List.getElem_range]

/-! ### Autocorrelation preservation -/

/-- Negation preserves aperiodic autocorrelation: `N_{-X}(s) = N_X(s)`. -/
lemma aperiodicAutocorr_neg (a : List Int) (s : Nat) :
    aperiodicAutocorr (negSeq a) s = aperiodicAutocorr a s := by
  unfold aperiodicAutocorr
  rw [negSeq_length_eq]
  split_ifs with h
  · rfl
  · exact Finset.sum_congr rfl fun i _ => by rw [negSeq_getD, negSeq_getD, neg_mul_neg]

/-- Reversal preserves aperiodic autocorrelation: `N_{X*}(s) = N_X(s)`. -/
lemma aperiodicAutocorr_rev (a : List Int) (s : Nat) :
    aperiodicAutocorr a.reverse s = aperiodicAutocorr a s := by
  unfold aperiodicAutocorr
  rw [List.length_reverse]
  split_ifs with h
  · rfl
  · push_neg at h
    set n := a.length
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
      rw [list_reverse_getD a i (by omega), list_reverse_getD a (i + s) (by omega)]
      have h1 : n - 1 - i = (n - 1 - s - i) + s := by omega
      have h2 : n - 1 - (i + s) = n - 1 - s - i := by omega
      rw [h1, h2, mul_comm]

/-- Alternation scales autocorrelation by `(-1)^s`: `N_{X̂}(s) = (-1)^s · N_X(s)`. -/
lemma aperiodicAutocorr_alt (a : List Int) (s : Nat) :
    aperiodicAutocorr (Turyn.altSeq a) s = (-1 : Int) ^ s * aperiodicAutocorr a s := by
  unfold aperiodicAutocorr
  rw [Turyn.altSeq_length]
  split_ifs with h
  · rw [mul_zero]
  · push_neg at h
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => by
      have hir := Finset.mem_range.mp hi
      rw [altSeq_getD_aux a i (by omega), altSeq_getD_aux a (i + s) (by omega)]
      rw [show (if i % 2 = 0 then (1:Int) else -1) * a.getD i 0 *
          ((if (i + s) % 2 = 0 then (1:Int) else -1) * a.getD (i + s) 0) =
          ((if i % 2 = 0 then (1:Int) else -1) * (if (i + s) % 2 = 0 then (1:Int) else -1)) *
          (a.getD i 0 * a.getD (i + s) 0) from by ring]
      rw [sign_product_eq]

/-! ### Vanishing preservation under each elementary transformation

These lemmas operate directly on `TurynType n`: the carrier-level
length/pm proofs come for free with `PmSeq`, leaving only the
combined-autocorrelation vanishing identity to re-derive. -/

namespace Turyn

/-- Negating one sequence preserves vanishing (autocorrelation is invariant
under sign flip). -/
lemma vanishing_negX {n : Nat} (T : TurynType n) :
    ∀ s, 1 ≤ s → s < n →
      combinedAutocorr (negSeq T.X.data) T.Y.data T.Z.data T.W.data s = 0 :=
  fun s hs1 hs2 => by
    have hv := T.vanishing s hs1 hs2
    unfold combinedAutocorr at hv ⊢; rw [aperiodicAutocorr_neg]; exact hv

lemma vanishing_negY {n : Nat} (T : TurynType n) :
    ∀ s, 1 ≤ s → s < n →
      combinedAutocorr T.X.data (negSeq T.Y.data) T.Z.data T.W.data s = 0 :=
  fun s hs1 hs2 => by
    have hv := T.vanishing s hs1 hs2
    unfold combinedAutocorr at hv ⊢; rw [aperiodicAutocorr_neg]; exact hv

lemma vanishing_negZ {n : Nat} (T : TurynType n) :
    ∀ s, 1 ≤ s → s < n →
      combinedAutocorr T.X.data T.Y.data (negSeq T.Z.data) T.W.data s = 0 :=
  fun s hs1 hs2 => by
    have hv := T.vanishing s hs1 hs2
    unfold combinedAutocorr at hv ⊢; rw [aperiodicAutocorr_neg]; exact hv

lemma vanishing_negW {n : Nat} (T : TurynType n) :
    ∀ s, 1 ≤ s → s < n →
      combinedAutocorr T.X.data T.Y.data T.Z.data (negSeq T.W.data) s = 0 :=
  fun s hs1 hs2 => by
    have hv := T.vanishing s hs1 hs2
    unfold combinedAutocorr at hv ⊢; rw [aperiodicAutocorr_neg]; exact hv

/-- Reversing one sequence preserves vanishing. -/
lemma vanishing_revX {n : Nat} (T : TurynType n) :
    ∀ s, 1 ≤ s → s < n →
      combinedAutocorr T.X.data.reverse T.Y.data T.Z.data T.W.data s = 0 :=
  fun s hs1 hs2 => by
    have hv := T.vanishing s hs1 hs2
    unfold combinedAutocorr at hv ⊢; rw [aperiodicAutocorr_rev]; exact hv

lemma vanishing_revY {n : Nat} (T : TurynType n) :
    ∀ s, 1 ≤ s → s < n →
      combinedAutocorr T.X.data T.Y.data.reverse T.Z.data T.W.data s = 0 :=
  fun s hs1 hs2 => by
    have hv := T.vanishing s hs1 hs2
    unfold combinedAutocorr at hv ⊢; rw [aperiodicAutocorr_rev]; exact hv

lemma vanishing_revZ {n : Nat} (T : TurynType n) :
    ∀ s, 1 ≤ s → s < n →
      combinedAutocorr T.X.data T.Y.data T.Z.data.reverse T.W.data s = 0 :=
  fun s hs1 hs2 => by
    have hv := T.vanishing s hs1 hs2
    unfold combinedAutocorr at hv ⊢; rw [aperiodicAutocorr_rev]; exact hv

lemma vanishing_revW {n : Nat} (T : TurynType n) :
    ∀ s, 1 ≤ s → s < n →
      combinedAutocorr T.X.data T.Y.data T.Z.data T.W.data.reverse s = 0 :=
  fun s hs1 hs2 => by
    have hv := T.vanishing s hs1 hs2
    unfold combinedAutocorr at hv ⊢; rw [aperiodicAutocorr_rev]; exact hv

/-- Alternating all four sequences preserves vanishing (combined sum scales
by `(-1)^s` which is zero times zero). -/
lemma vanishing_altAll {n : Nat} (T : TurynType n) :
    ∀ s, 1 ≤ s → s < n →
      combinedAutocorr (Turyn.altSeq T.X.data) (Turyn.altSeq T.Y.data)
        (Turyn.altSeq T.Z.data) (Turyn.altSeq T.W.data) s = 0 :=
  fun s hs1 hs2 => by
    have hv := T.vanishing s hs1 hs2
    unfold combinedAutocorr at hv ⊢
    rw [aperiodicAutocorr_alt, aperiodicAutocorr_alt, aperiodicAutocorr_alt, aperiodicAutocorr_alt]
    have factored :
        (-1 : Int) ^ s * aperiodicAutocorr T.X.data s +
          (-1 : Int) ^ s * aperiodicAutocorr T.Y.data s +
          2 * ((-1 : Int) ^ s * aperiodicAutocorr T.Z.data s) +
          2 * ((-1 : Int) ^ s * aperiodicAutocorr T.W.data s) =
        (-1 : Int) ^ s * (aperiodicAutocorr T.X.data s + aperiodicAutocorr T.Y.data s +
          2 * aperiodicAutocorr T.Z.data s + 2 * aperiodicAutocorr T.W.data s) := by ring
    rw [factored, hv, mul_zero]

/-- Swapping `X` and `Y` preserves vanishing (their roles in the combined sum
are symmetric). -/
lemma vanishing_swapXY {n : Nat} (T : TurynType n) :
    ∀ s, 1 ≤ s → s < n →
      combinedAutocorr T.Y.data T.X.data T.Z.data T.W.data s = 0 :=
  fun s hs1 hs2 => by
    have hv := T.vanishing s hs1 hs2
    unfold combinedAutocorr at hv ⊢; linarith

end Turyn

namespace Turyn

/-! ### `PmSeq` operations: negation, reversal, alternation -/

/-- Negate every entry of a `PmSeq n`. -/
def _root_.PmSeq.neg {n : Nat} (s : PmSeq n) : PmSeq n :=
  ⟨negSeq s.data, by simp [negSeq_length_eq, s.len], AllPmOne_negSeq s.pm⟩

/-- Reverse a `PmSeq n`. -/
def _root_.PmSeq.reverse {n : Nat} (s : PmSeq n) : PmSeq n :=
  ⟨s.data.reverse, by simp [s.len], AllPmOne_reverse s.pm⟩

/-- Alternate a `PmSeq n` (entry `i` gets factor `(-1)^i`). -/
def _root_.PmSeq.alt {n : Nat} (s : PmSeq n) : PmSeq n :=
  ⟨altSeq s.data, by simp [altSeq_length, s.len], AllPmOne_alt s.pm⟩

/-! ### TurynType transformations -/

def _root_.TurynType.doNegX {n : Nat} (S : TurynType n) : TurynType n :=
  ⟨S.X.neg, S.Y, S.Z, S.W, vanishing_negX S⟩

def _root_.TurynType.doNegY {n : Nat} (S : TurynType n) : TurynType n :=
  ⟨S.X, S.Y.neg, S.Z, S.W, vanishing_negY S⟩

def _root_.TurynType.doNegZ {n : Nat} (S : TurynType n) : TurynType n :=
  ⟨S.X, S.Y, S.Z.neg, S.W, vanishing_negZ S⟩

def _root_.TurynType.doNegW {n : Nat} (S : TurynType n) : TurynType n :=
  ⟨S.X, S.Y, S.Z, S.W.neg, vanishing_negW S⟩

def _root_.TurynType.doRevX {n : Nat} (S : TurynType n) : TurynType n :=
  ⟨S.X.reverse, S.Y, S.Z, S.W, vanishing_revX S⟩

def _root_.TurynType.doRevY {n : Nat} (S : TurynType n) : TurynType n :=
  ⟨S.X, S.Y.reverse, S.Z, S.W, vanishing_revY S⟩

def _root_.TurynType.doRevZ {n : Nat} (S : TurynType n) : TurynType n :=
  ⟨S.X, S.Y, S.Z.reverse, S.W, vanishing_revZ S⟩

def _root_.TurynType.doRevW {n : Nat} (S : TurynType n) : TurynType n :=
  ⟨S.X, S.Y, S.Z, S.W.reverse, vanishing_revW S⟩

def _root_.TurynType.doAltAll {n : Nat} (S : TurynType n) : TurynType n :=
  ⟨S.X.alt, S.Y.alt, S.Z.alt, S.W.alt, vanishing_altAll S⟩

def _root_.TurynType.doSwap {n : Nat} (S : TurynType n) : TurynType n :=
  ⟨S.Y, S.X, S.Z, S.W, vanishing_swapXY S⟩

/-! ### Elementary transformations -/

/-- Elementary transformations between Turyn-type sequences.

These encode the four move families from Best–Đoković–Kharaghani–Ramp (2013):
- (T1) Negate one component
- (T2) Reverse one component
- (T3) Alternate all four components
- (T4) Swap A and B -/
inductive Elementary (n : Nat) : TurynType n → TurynType n → Prop where
  | negX (S : TurynType n) : Elementary n S S.doNegX
  | negY (S : TurynType n) : Elementary n S S.doNegY
  | negZ (S : TurynType n) : Elementary n S S.doNegZ
  | negW (S : TurynType n) : Elementary n S S.doNegW
  | revX (S : TurynType n) : Elementary n S S.doRevX
  | revY (S : TurynType n) : Elementary n S S.doRevY
  | revZ (S : TurynType n) : Elementary n S S.doRevZ
  | revW (S : TurynType n) : Elementary n S S.doRevW
  | altAll (S : TurynType n) : Elementary n S S.doAltAll
  | swap (S : TurynType n) : Elementary n S S.doSwap

/-- Equivalence is the reflexive-transitive closure of elementary transformations. -/
def Equivalent (n : Nat) (S T : TurynType n) : Prop :=
  Relation.ReflTransGen (Elementary n) S T

/-- A single elementary step implies equivalence. -/
lemma Elementary.toEquivalent {n : Nat} {S T : TurynType n}
    (h : Elementary n S T) : Equivalent n S T :=
  Relation.ReflTransGen.single h

/-! ### Helper: ±1 entries are 1 or -1 -/

lemma pm_entry_of_getD {X : List Int} (hpm : AllPmOne X) {i : Nat} (hi : i < X.length) :
    X.getD i 0 = 1 ∨ X.getD i 0 = -1 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact hpm X[i] (List.getElem_mem hi)

/-! ### Endpoint constraint from vanishing at s = n-1 -/

lemma aperiodicAutocorr_last {n : Nat} {a : List Int} (ha : a.length = n) (hn : 1 < n) :
    aperiodicAutocorr a (n - 1) = a.getD 0 0 * a.getD (n - 1) 0 := by
  unfold aperiodicAutocorr
  rw [if_neg (by rw [ha]; omega)]
  rw [show a.length - (n - 1) = 1 from by rw [ha]; omega]
  rw [Finset.sum_range_one]
  rw [Nat.zero_add]

lemma endpoint_relation {n : Nat} (hn : 1 < n) (S : TurynType n) :
    xAt S 1 * xAt S n + yAt S 1 * yAt S n + 2 * (zAt S 1 * zAt S n) = 0 := by
      convert S.vanishing ( n - 1 ) ( Nat.sub_pos_of_lt hn ) ( Nat.sub_lt ( by linarith ) zero_lt_one ) using 1;
      unfold combinedAutocorr;
      unfold xAt yAt zAt; simp +arith +decide [ * ] ;
      rw [ aperiodicAutocorr_last, aperiodicAutocorr_last, aperiodicAutocorr_last ] <;> norm_num [ S.X.len, S.Y.len, S.Z.len, S.W.len ];
      · unfold aperiodicAutocorr; simp +decide [ S.W.len ] ;
        ring;
      · linarith;
      · linarith;
      · linarith

theorem lemma1_endpoint_constraint
    (n : Nat) (hn : 1 < n) (S : TurynType n)
    (h1 : Canonical1 n S) :
    zAt S n = -1 := by
  have hep := endpoint_relation hn S
  unfold Canonical1 at h1
  obtain ⟨ha1, han, hb1, hbn, hc1, _⟩ := h1
  rw [ha1, han, hb1, hbn, hc1] at hep
  linarith

/-! ### Helper lemmas for step proofs -/

/-
altSeq multiplies by (-1)^i at each valid index.
-/
lemma altSeq_getD (X : List Int) (i : Nat) (hi : i < X.length) :
    (altSeq X).getD i 0 = (if i % 2 = 0 then 1 else -1) * X.getD i 0 :=
  altSeq_getD_aux X i hi

/-
altSeq preserves position 0 (factor = 1).
-/
lemma altSeq_getD_zero (X : List Int) (hX : 0 < X.length) :
    (altSeq X).getD 0 0 = X.getD 0 0 := by
  rw [altSeq_getD X 0 hX]
  norm_num

/-
For even length ≥ 2, altSeq at position length-1 has factor -1.
-/
lemma altSeq_getD_last (X : List Int) (hn : X.length % 2 = 0) (hX : 2 ≤ X.length) :
    (altSeq X).getD (X.length - 1) 0 = -(X.getD (X.length - 1) 0) := by
  rw [altSeq_getD X (X.length - 1) (by omega)]
  have hodd : (X.length - 1) % 2 = 1 := by omega
  rw [if_neg (by omega)]
  ring

/-! ### Step theorems -/

/-- Transitivity of equivalence (closure composition). -/
theorem equivalent_trans
    (n : Nat) {S T U : TurynType n} :
    Equivalent n S T → Equivalent n T U → Equivalent n S U :=
  Relation.ReflTransGen.trans

/-! ### Private helpers for step1_condition1 -/

private lemma step1_xAt_doNegX {n : Nat} (S : TurynType n) (i : Nat) :
    xAt S.doNegX i = -(xAt S i) := by
  unfold xAt TurynType.doNegX PmSeq.neg; exact negSeq_getD _ _

private lemma step1_yAt_doNegY {n : Nat} (S : TurynType n) (i : Nat) :
    yAt S.doNegY i = -(yAt S i) := by
  unfold yAt TurynType.doNegY PmSeq.neg; exact negSeq_getD _ _

private lemma step1_zAt_doNegZ {n : Nat} (S : TurynType n) (i : Nat) :
    zAt S.doNegZ i = -(zAt S i) := by
  unfold zAt TurynType.doNegZ PmSeq.neg; exact negSeq_getD _ _

private lemma step1_wAt_doNegW {n : Nat} (S : TurynType n) (i : Nat) :
    wAt S.doNegW i = -(wAt S i) := by
  unfold wAt TurynType.doNegW PmSeq.neg; exact negSeq_getD _ _

private lemma step1_xAt_doAltAll_first {n : Nat} (S : TurynType n) (hn : 1 ≤ n) :
    xAt S.doAltAll 1 = xAt S 1 := by
  unfold xAt TurynType.doAltAll PmSeq.alt
  exact altSeq_getD_zero S.X.data (by rw [S.X.len]; omega)

private lemma step1_yAt_doAltAll_first {n : Nat} (S : TurynType n) (hn : 1 ≤ n) :
    yAt S.doAltAll 1 = yAt S 1 := by
  unfold yAt TurynType.doAltAll PmSeq.alt
  exact altSeq_getD_zero S.Y.data (by rw [S.Y.len]; omega)

private lemma step1_zAt_doAltAll_first {n : Nat} (S : TurynType n) (hn : 1 ≤ n) :
    zAt S.doAltAll 1 = zAt S 1 := by
  unfold zAt TurynType.doAltAll PmSeq.alt
  exact altSeq_getD_zero S.Z.data (by rw [S.Z.len]; omega)

private lemma step1_wAt_doAltAll_first {n : Nat} (S : TurynType n) (hn : 2 ≤ n) :
    wAt S.doAltAll 1 = wAt S 1 := by
  unfold wAt TurynType.doAltAll PmSeq.alt
  exact altSeq_getD_zero S.W.data (by rw [S.W.len]; omega)

private lemma step1_xAt_doAltAll_last {n : Nat} (S : TurynType n)
    (hn_even : n % 2 = 0) (hn : 2 ≤ n) :
    xAt S.doAltAll n = -(xAt S n) := by
  unfold xAt TurynType.doAltAll PmSeq.alt
  have hlen := S.X.len
  have h := altSeq_getD_last S.X.data (by rw [hlen]; exact hn_even) (by rw [hlen]; exact hn)
  rw [hlen] at h; exact h

private lemma step1_yAt_doAltAll_last {n : Nat} (S : TurynType n)
    (hn_even : n % 2 = 0) (hn : 2 ≤ n) :
    yAt S.doAltAll n = -(yAt S n) := by
  unfold yAt TurynType.doAltAll PmSeq.alt
  have hlen := S.Y.len
  have h := altSeq_getD_last S.Y.data (by rw [hlen]; exact hn_even) (by rw [hlen]; exact hn)
  rw [hlen] at h; exact h

/-- Step 1: enforce condition (1) — normalize endpoint signs. -/
theorem step1_condition1
    (n : Nat) (hn_even : n % 2 = 0) (hn : 2 ≤ n) (S : TurynType n) :
    ∃ S1 : TurynType n, Equivalent n S S1 ∧ Canonical1 n S1 := by
  -- Phase 1: Normalize first entries of A, B, C, D to +1 by optional negations.
  -- Step 1a: Normalize xAt 1 to +1.
  have ha_pm : xAt S 1 = 1 ∨ xAt S 1 = -1 :=
    pm_entry_of_getD S.X.pm (by rw [S.X.len]; omega)
  obtain ⟨Sa, hSa_eq, hSa_a1⟩ : ∃ Sa : TurynType n,
      Equivalent n S Sa ∧ xAt Sa 1 = 1 := by
    rcases ha_pm with ha1 | ha1
    · exact ⟨S, Relation.ReflTransGen.refl, ha1⟩
    · exact ⟨S.doNegX, Relation.ReflTransGen.single (Elementary.negX S),
        by rw [step1_xAt_doNegX, ha1]; norm_num⟩
  -- Step 1b: Normalize yAt 1 to +1 (doNegY preserves A).
  have hb_pm : yAt Sa 1 = 1 ∨ yAt Sa 1 = -1 :=
    pm_entry_of_getD Sa.Y.pm (by rw [Sa.Y.len]; omega)
  obtain ⟨Sb, hSb_eq, hSb_a1, hSb_b1⟩ : ∃ Sb : TurynType n,
      Equivalent n Sa Sb ∧ xAt Sb 1 = 1 ∧ yAt Sb 1 = 1 := by
    rcases hb_pm with hb1 | hb1
    · exact ⟨Sa, Relation.ReflTransGen.refl, hSa_a1, hb1⟩
    · exact ⟨Sa.doNegY, Relation.ReflTransGen.single (Elementary.negY Sa),
        hSa_a1, -- xAt Sa.doNegY 1 = xAt Sa 1 = 1 (definitional)
        by rw [step1_yAt_doNegY, hb1]; norm_num⟩
  -- Step 1c: Normalize zAt 1 to +1 (doNegZ preserves A, B).
  have hc_pm : zAt Sb 1 = 1 ∨ zAt Sb 1 = -1 :=
    pm_entry_of_getD Sb.Z.pm (by rw [Sb.Z.len]; omega)
  obtain ⟨Sc, hSc_eq, hSc_a1, hSc_b1, hSc_c1⟩ : ∃ Sc : TurynType n,
      Equivalent n Sb Sc ∧ xAt Sc 1 = 1 ∧ yAt Sc 1 = 1 ∧ zAt Sc 1 = 1 := by
    rcases hc_pm with hc1 | hc1
    · exact ⟨Sb, Relation.ReflTransGen.refl, hSb_a1, hSb_b1, hc1⟩
    · exact ⟨Sb.doNegZ, Relation.ReflTransGen.single (Elementary.negZ Sb),
        hSb_a1, -- xAt Sb.doNegZ 1 = xAt Sb 1 (definitional)
        hSb_b1, -- yAt Sb.doNegZ 1 = yAt Sb 1 (definitional)
        by rw [step1_zAt_doNegZ, hc1]; norm_num⟩
  -- Step 1d: Normalize wAt 1 to +1 (doNegW preserves A, B, C).
  have hd_pm : wAt Sc 1 = 1 ∨ wAt Sc 1 = -1 :=
    pm_entry_of_getD Sc.W.pm (by rw [Sc.W.len]; omega)
  obtain ⟨Sd, hSd_eq, hSd_a1, hSd_b1, hSd_c1, hSd_d1⟩ : ∃ Sd : TurynType n,
      Equivalent n Sc Sd ∧ xAt Sd 1 = 1 ∧ yAt Sd 1 = 1 ∧ zAt Sd 1 = 1 ∧ wAt Sd 1 = 1 := by
    rcases hd_pm with hd1 | hd1
    · exact ⟨Sc, Relation.ReflTransGen.refl, hSc_a1, hSc_b1, hSc_c1, hd1⟩
    · exact ⟨Sc.doNegW, Relation.ReflTransGen.single (Elementary.negW Sc),
        hSc_a1, hSc_b1, hSc_c1,
        by rw [step1_wAt_doNegW, hd1]; norm_num⟩
  -- Chain equivalences: S ~ Sa ~ Sb ~ Sc ~ Sd.
  have hS_Sd : Equivalent n S Sd :=
    (hSa_eq.trans hSb_eq).trans (hSc_eq.trans hSd_eq)
  -- Phase 2: Handle last entries xAt n and yAt n.
  -- Obtain ±1 witnesses for positions n.
  have ha_n_pm : xAt Sd n = 1 ∨ xAt Sd n = -1 :=
    pm_entry_of_getD Sd.X.pm (by rw [Sd.X.len]; omega)
  have hb_n_pm : yAt Sd n = 1 ∨ yAt Sd n = -1 :=
    pm_entry_of_getD Sd.Y.pm (by rw [Sd.Y.len]; omega)
  have hc_n_pm : zAt Sd n = 1 ∨ zAt Sd n = -1 :=
    pm_entry_of_getD Sd.Z.pm (by rw [Sd.Z.len]; omega)
  -- Endpoint relation with known first entries substituted.
  have h_ep_raw := endpoint_relation (show 1 < n by omega) Sd
  rw [hSd_a1, hSd_b1, hSd_c1] at h_ep_raw
  -- h_ep_raw : 1 * xAt Sd n + 1 * yAt Sd n + 2 * (1 * zAt Sd n) = 0
  have h_ep : xAt Sd n + yAt Sd n + 2 * zAt Sd n = 0 := by linarith
  -- Case split: are both last entries -1?
  by_cases h_both_neg : xAt Sd n = -1 ∧ yAt Sd n = -1
  · -- Both xAt n and yAt n are -1: apply doAltAll to flip signs of last entries.
    obtain ⟨ha_neg, hb_neg⟩ := h_both_neg
    have hAltAll_a1 : xAt Sd.doAltAll 1 = 1 := by
      rw [step1_xAt_doAltAll_first Sd (by omega)]; exact hSd_a1
    have hAltAll_an : xAt Sd.doAltAll n = 1 := by
      rw [step1_xAt_doAltAll_last Sd hn_even hn, ha_neg]; norm_num
    have hAltAll_b1 : yAt Sd.doAltAll 1 = 1 := by
      rw [step1_yAt_doAltAll_first Sd (by omega)]; exact hSd_b1
    have hAltAll_bn : yAt Sd.doAltAll n = 1 := by
      rw [step1_yAt_doAltAll_last Sd hn_even hn, hb_neg]; norm_num
    have hAltAll_c1 : zAt Sd.doAltAll 1 = 1 := by
      rw [step1_zAt_doAltAll_first Sd (by omega)]; exact hSd_c1
    have hAltAll_d1 : wAt Sd.doAltAll 1 = 1 := by
      rw [step1_wAt_doAltAll_first Sd hn]; exact hSd_d1
    exact ⟨Sd.doAltAll,
      hS_Sd.trans (Elementary.toEquivalent (Elementary.altAll Sd)),
      hAltAll_a1, hAltAll_an, hAltAll_b1, hAltAll_bn, hAltAll_c1, hAltAll_d1⟩
  · -- Not both -1: deduce both must be +1 via exhaustive ±1 case analysis.
    have h_last : xAt Sd n = 1 ∧ yAt Sd n = 1 := by
      rcases ha_n_pm with ha_n | ha_n <;> rcases hb_n_pm with hb_n | hb_n <;>
          rcases hc_n_pm with hc_n | hc_n
      -- xAt=1, yAt=1, zAt=1: 1+1+2*1=4≠0
      · rw [ha_n, hb_n, hc_n] at h_ep; norm_num at h_ep
      -- xAt=1, yAt=1, zAt=-1: 1+1+2*(-1)=0 ✓
      · exact ⟨ha_n, hb_n⟩
      -- xAt=1, yAt=-1, zAt=1: 1+(-1)+2*1=2≠0
      · rw [ha_n, hb_n, hc_n] at h_ep; norm_num at h_ep
      -- xAt=1, yAt=-1, zAt=-1: 1+(-1)+2*(-1)=-2≠0
      · rw [ha_n, hb_n, hc_n] at h_ep; norm_num at h_ep
      -- xAt=-1, yAt=1, zAt=1: -1+1+2*1=2≠0
      · rw [ha_n, hb_n, hc_n] at h_ep; norm_num at h_ep
      -- xAt=-1, yAt=1, zAt=-1: -1+1+2*(-1)=-2≠0
      · rw [ha_n, hb_n, hc_n] at h_ep; norm_num at h_ep
      -- xAt=-1, yAt=-1, zAt=1: contradicts ¬(both=-1)
      · exact absurd ⟨ha_n, hb_n⟩ h_both_neg
      -- xAt=-1, yAt=-1, zAt=-1: -1+(-1)+2*(-1)=-4≠0
      · rw [ha_n, hb_n, hc_n] at h_ep; norm_num at h_ep
    exact ⟨Sd, hS_Sd, hSd_a1, h_last.1, hSd_b1, h_last.2, hSd_c1, hSd_d1⟩

/-! ### Private helpers for step2 -/

private lemma revA_getD_eq {n : Nat} (S : TurynType n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    S.X.reverse.data.getD (j - 1) 0 = S.X.data.getD (n - j) 0 := by
  have hlt : j - 1 < S.X.data.length := by rw [S.X.len]; omega
  show S.X.data.reverse.getD (j - 1) 0 = S.X.data.getD (n - j) 0
  unfold List.getD
  rw [List.getElem?_reverse hlt]
  have : S.X.data.length - 1 - (j - 1) = n - j := by rw [S.X.len]; omega
  rw [this]

private lemma xAt_revA_eq {n : Nat} (S : TurynType n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    xAt S.doRevX j = xAt S (n + 1 - j) := by
  unfold xAt TurynType.doRevX
  have h1 : S.X.reverse.data.getD (j - 1) 0 = S.X.data.getD (n - j) 0 := revA_getD_eq S hj1 hj2
  have h2 : n + 1 - j - 1 = n - j := by omega
  rw [h1, h2]

private lemma xAt_revA_mirror {n : Nat} (S : TurynType n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    xAt S.doRevX (n + 1 - j) = xAt S j := by
  have h1 : 1 ≤ n + 1 - j := by omega
  have h2 : n + 1 - j ≤ n := by omega
  rw [xAt_revA_eq S h1 h2]
  congr 1; omega

private lemma yAt_doRevX_eq {n : Nat} (S : TurynType n) (j : Nat) :
    yAt S.doRevX j = yAt S j := by
  unfold yAt TurynType.doRevX PmSeq.reverse; rfl

private lemma zAt_doRevX_eq {n : Nat} (S : TurynType n) (j : Nat) :
    zAt S.doRevX j = zAt S j := by
  unfold zAt TurynType.doRevX PmSeq.reverse; rfl

private lemma wAt_doRevX_eq {n : Nat} (S : TurynType n) (j : Nat) :
    wAt S.doRevX j = wAt S j := by
  unfold wAt TurynType.doRevX PmSeq.reverse; rfl

private lemma canonical1_doRevX {n : Nat} (hn : 2 ≤ n) (S : TurynType n)
    (h1 : Canonical1 n S) : Canonical1 n S.doRevX := by
  unfold Canonical1 at *
  obtain ⟨ha1, han, hb1, hbn, hc1, hd1⟩ := h1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [xAt_revA_eq S (by omega) (by omega)]
    rw [show n + 1 - 1 = n from by omega]
    exact han
  · rw [xAt_revA_eq S (by omega) (by omega)]
    rw [show n + 1 - n = 1 from by omega]
    exact ha1
  · rw [yAt_doRevX_eq]; exact hb1
  · rw [yAt_doRevX_eq]; exact hbn
  · rw [zAt_doRevX_eq]; exact hc1
  · rw [wAt_doRevX_eq]; exact hd1

private lemma xAt_pm_A {n : Nat} (S : TurynType n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    xAt S j = 1 ∨ xAt S j = -1 := by
  unfold xAt
  exact pm_entry_of_getD S.X.pm (by rw [S.X.len]; omega)

/-- Step 2: enforce condition (2) by optional reversal of `A`. -/
theorem step2_condition2
    (n : Nat) (hn : 2 ≤ n) (S : TurynType n)
    (h1 : Canonical1 n S) :
    ∃ S2 : TurynType n, Equivalent n S S2 ∧ Canonical1 n S2 ∧ Canonical2 n S2 := by
      -- Either S already satisfies Canonical2, or there is a first asymmetric index with xAt = -1.
      by_contra h_neg
      -- Extract a witness: the first index i where A is asymmetric and xAt S i = -1.
      obtain ⟨i, hi_lb, hi_ub, hi_sym, hi_neq, hi_val⟩ :
          ∃ i, 1 ≤ i ∧ i ≤ n ∧
            (∀ j, 1 ≤ j → j < i → xAt S j = xAt S (n + 1 - j)) ∧
            xAt S i ≠ xAt S (n + 1 - i) ∧ xAt S i = -1 := by
        -- If no such i exists, then S itself satisfies Canonical2.
        by_contra h_no_witness
        push_neg at h_no_witness
        exact h_neg ⟨S, Relation.ReflTransGen.refl, h1, fun j hj1 hj2 hj3 hj4 =>
          (xAt_pm_A S hj1 hj2).resolve_right (h_no_witness j hj1 hj2 hj3 hj4)⟩
      -- We claim S.doRevX satisfies Canonical1 and Canonical2.
      exact h_neg ⟨S.doRevX, Relation.ReflTransGen.single (Elementary.revX S),
        canonical1_doRevX hn S h1, fun j hj1 hj2 hj3 hj4 => by
          -- We need: xAt S.doRevX j = 1.
          -- xAt S.doRevX j = xAt S (n + 1 - j) by reversal.
          have h_fwd : xAt S.doRevX j = xAt S (n + 1 - j) := xAt_revA_eq S hj1 hj2
          -- xAt S.doRevX (n + 1 - j) = xAt S j by mirror reversal.
          have h_bwd : xAt S.doRevX (n + 1 - j) = xAt S j := xAt_revA_mirror S hj1 hj2
          -- Case split: j < i, j = i, or j > i.
          rcases lt_trichotomy j i with hjlt | hjeq | hjgt
          · -- j < i: all indices before i are symmetric in S, so xAt S j = xAt S (n+1-j).
            have hsym : xAt S j = xAt S (n + 1 - j) := hi_sym j hj1 hjlt
            -- But xAt S.doRevX j ≠ xAt S.doRevX (n+1-j) by hj4, contradiction.
            rw [h_fwd, h_bwd] at hj4
            exact absurd hsym.symm hj4
          · -- j = i: xAt S.doRevX i = xAt S (n+1-i).
            -- We know xAt S i = -1, so xAt S (n+1-i) must be 1 (since they differ and are ±1).
            subst hjeq
            rw [h_fwd]
            have h_mirror_pm := xAt_pm_A S (show 1 ≤ n + 1 - j from by omega) (show n + 1 - j ≤ n from by omega)
            rcases h_mirror_pm with h_one | h_neg1
            · exact h_one
            · exact absurd (show xAt S j = xAt S (n + 1 - j) by rw [hi_val, h_neg1]) hi_neq
          · -- j > i: We show the predecessors-symmetric hypothesis hj3 fails for i, contradiction.
            -- hj3 says all k < j are symmetric in S.doRevX.
            have h_sym_i : xAt S.doRevX i = xAt S.doRevX (n + 1 - i) := hj3 i hi_lb hjgt
            -- Rewrite using reversal accessors.
            rw [xAt_revA_eq S hi_lb hi_ub, xAt_revA_mirror S hi_lb hi_ub] at h_sym_i
            -- So xAt S (n+1-i) = xAt S i, contradicting hi_neq.
            exact absurd h_sym_i.symm hi_neq⟩

/-
Reversal of a list maps index j to (length-1-j).
-/
lemma revD_getD {D : List Int} {j : Nat} (hj : j < D.length) :
    D.reverse.getD j 0 = D.getD (D.length - 1 - j) 0 := by
  have h1 : j < D.reverse.length := by rw [List.length_reverse]; exact hj
  have h2 : D.length - 1 - j < D.length := by omega
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
  rw [List.getElem_reverse]

/-
After reversing D (length n-1) in a TurynType, the 1-indexed accessor
satisfies wAt(j) = old wAt(n-j) for 1 ≤ j ≤ n-1.
-/
lemma wAt_doRevW {n : Nat} (S : TurynType n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n - 1) :
    wAt S.doRevW j = wAt S (n - j) := by
      convert revD_getD _ using 2;
      · rw [ S.W.len ];
        rw [ show n - 1 - 1 - ( j - 1 ) = n - j - 1 by omega ];
        rfl;
      · convert Nat.lt_of_lt_of_le ( Nat.sub_lt hj1 zero_lt_one ) hj2 using 1;
        exact S.W.len

/-
After reversing and negating D, the 1-indexed accessor
satisfies wAt(j) = -(old wAt(n-j)) for 1 ≤ j ≤ n-1.
-/
lemma wAt_doNegRevW {n : Nat} (S : TurynType n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n - 1) :
    wAt (TurynType.doNegW S.doRevW) j = -(wAt S (n - j)) := by
      have h_negD : wAt (TurynType.doNegW (TurynType.doRevW S)) j = -(wAt (TurynType.doRevW S) j) := by
        convert negSeq_getD _ _ using 1;
      rw [ h_negD, wAt_doRevW S hj1 hj2 ]

/-! ### Reversal accessor lemmas -/

lemma xAt_doRevX_at {n : Nat} (S : TurynType n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    xAt S.doRevX j = xAt S (n + 1 - j) := by
  unfold xAt TurynType.doRevX PmSeq.reverse
  simp only
  convert revD_getD (D := S.X.data) _ using 2
  · rw [S.X.len]; omega
  · convert Nat.lt_of_lt_of_le (Nat.sub_lt hj1 zero_lt_one) hj2 using 1
    exact S.X.len

lemma xAt_doRevX_mirror {n : Nat} (S : TurynType n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    xAt S.doRevX (n + 1 - j) = xAt S j := by
  have h1 : 1 ≤ n + 1 - j := by omega
  have h2 : n + 1 - j ≤ n := by omega
  rw [xAt_doRevX_at S h1 h2]; congr 1; omega

lemma yAt_doRevY_at {n : Nat} (S : TurynType n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    yAt S.doRevY j = yAt S (n + 1 - j) := by
  unfold yAt TurynType.doRevY PmSeq.reverse
  simp only
  convert revD_getD (D := S.Y.data) _ using 2
  · rw [S.Y.len]; omega
  · convert Nat.lt_of_lt_of_le (Nat.sub_lt hj1 zero_lt_one) hj2 using 1
    exact S.Y.len

lemma yAt_doRevY_mirror {n : Nat} (S : TurynType n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    yAt S.doRevY (n + 1 - j) = yAt S j := by
  have h1 : 1 ≤ n + 1 - j := by omega
  have h2 : n + 1 - j ≤ n := by omega
  rw [yAt_doRevY_at S h1 h2]; congr 1; omega

lemma zAt_doRevZ_at {n : Nat} (S : TurynType n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    zAt S.doRevZ j = zAt S (n + 1 - j) := by
  unfold zAt TurynType.doRevZ PmSeq.reverse
  simp only
  convert revD_getD (D := S.Z.data) _ using 2
  · rw [S.Z.len]; omega
  · convert Nat.lt_of_lt_of_le (Nat.sub_lt hj1 zero_lt_one) hj2 using 1
    exact S.Z.len

lemma zAt_doRevZ_mirror {n : Nat} (S : TurynType n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    zAt S.doRevZ (n + 1 - j) = zAt S j := by
  have h1 : 1 ≤ n + 1 - j := by omega
  have h2 : n + 1 - j ≤ n := by omega
  rw [zAt_doRevZ_at S h1 h2]; congr 1; omega

lemma wAt_doRevW_mirror {n : Nat} (S : TurynType n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n - 1) :
    wAt S.doRevW (n - j) = wAt S j := by
  have h1 : 1 ≤ n - j := by omega
  have h2 : n - j ≤ n - 1 := by omega
  rw [wAt_doRevW S h1 h2]; congr 1; omega

/-! ### doRevY preserves other accessors -/

private lemma xAt_doRevY {n : Nat} (S : TurynType n) (i : Nat) :
    xAt S.doRevY i = xAt S i := rfl

private lemma zAt_doRevY {n : Nat} (S : TurynType n) (i : Nat) :
    zAt S.doRevY i = zAt S i := rfl

private lemma wAt_doRevY {n : Nat} (S : TurynType n) (i : Nat) :
    wAt S.doRevY i = wAt S i := rfl

/-- Step 3: enforce condition (3) by optional reversal of `B`. -/
theorem step3_condition3
    (n : Nat) (hn : 2 ≤ n) (S : TurynType n)
    (h12 : Canonical1 n S ∧ Canonical2 n S) :
    ∃ S3 : TurynType n,
      Equivalent n S S3 ∧ Canonical1 n S3 ∧ Canonical2 n S3 ∧ Canonical3 n S3 := by
  -- Decide whether B already satisfies Canonical3 or needs reversal.
  by_cases hB : ∃ i, 1 ≤ i ∧ i ≤ n ∧
      (∀ j, 1 ≤ j → j < i → yAt S j = yAt S (n + 1 - j)) ∧
      yAt S i ≠ yAt S (n + 1 - i) ∧ yAt S i = -1
  -- Case 1: there exists a first asymmetric index i with yAt S i = -1; reverse B.
  · rcases hB with ⟨i, hi1, hi2, hsym, hasym, hval⟩
    refine ⟨S.doRevY, ?_, ?_, ?_, ?_⟩
    -- (a) Equivalence: single elementary step.
    · exact Relation.ReflTransGen.single (Elementary.revY S)
    -- (b) Canonical1 is preserved.
    · have hc1 := h12.1
      unfold Canonical1 at hc1 ⊢
      rcases hc1 with ⟨ha1, han, hb1, hbn, hc1v, hd1⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      -- xAt is unchanged by doRevY
      · rw [xAt_doRevY]; exact ha1
      · rw [xAt_doRevY]; exact han
      -- yAt endpoints swap under reversal
      · rw [yAt_doRevY_at S (by omega : 1 ≤ 1) (by omega : 1 ≤ n)]
        have : n + 1 - 1 = n := by omega
        rw [this]; exact hbn
      · rw [yAt_doRevY_at S (by omega : 1 ≤ n) le_rfl]
        have : n + 1 - n = 1 := by omega
        rw [this]; exact hb1
      -- zAt and wAt are unchanged by doRevY
      · rw [zAt_doRevY]; exact hc1v
      · rw [wAt_doRevY]; exact hd1
    -- (c) Canonical2 is preserved (A is unchanged by doRevY).
    · intro j hj1 hj2 hj3 hj4
      have : xAt S.doRevY j = xAt S j := xAt_doRevY S j
      have : xAt S.doRevY (n + 1 - j) = xAt S (n + 1 - j) := xAt_doRevY S (n + 1 - j)
      have hj3' : ∀ k, 1 ≤ k → k < j → xAt S k = xAt S (n + 1 - k) := by
        intro k hk1 hk2
        have := hj3 k hk1 hk2
        rw [xAt_doRevY, xAt_doRevY] at this
        exact this
      have hj4' : xAt S j ≠ xAt S (n + 1 - j) := by
        rw [← xAt_doRevY S j, ← xAt_doRevY S (n + 1 - j)]
        exact hj4
      rw [xAt_doRevY]
      exact h12.2 j hj1 hj2 hj3' hj4'
    -- (d) Canonical3 holds after reversal.
    · intro j hj1 hj2 hj3 hj4
      -- Translate the symmetry/asymmetry conditions back to S.
      have hrev_j : yAt S.doRevY j = yAt S (n + 1 - j) :=
        yAt_doRevY_at S hj1 hj2
      have hrev_mirror : yAt S.doRevY (n + 1 - j) = yAt S j :=
        yAt_doRevY_mirror S hj1 hj2
      -- All predecessors of j are symmetric in doRevY, hence in S.
      have hsym_S : ∀ k, 1 ≤ k → k < j → yAt S k = yAt S (n + 1 - k) := by
        intro k hk1 hk2
        have hk2n : k ≤ n := le_trans (le_of_lt hk2) hj2
        have := hj3 k hk1 hk2
        rw [yAt_doRevY_at S hk1 hk2n, yAt_doRevY_mirror S hk1 hk2n] at this
        exact this.symm
      -- j is asymmetric in S.
      have hasym_S : yAt S j ≠ yAt S (n + 1 - j) := by
        intro heq
        exact hj4 (by rw [hrev_j, hrev_mirror]; exact heq.symm)
      -- yAt S (n + 1 - j) is ±1.
      have hpm : yAt S (n + 1 - j) = 1 ∨ yAt S (n + 1 - j) = -1 := by
        have hpm_B : AllPmOne S.Y.data := S.Y.pm
        exact pm_entry_of_getD hpm_B (by rw [S.Y.len]; omega)
      -- yAt S j is ±1.
      have hpm_j : yAt S j = 1 ∨ yAt S j = -1 := by
        have hpm_B : AllPmOne S.Y.data := S.Y.pm
        exact pm_entry_of_getD hpm_B (by rw [S.Y.len]; omega)
      -- Since yAt S j ≠ yAt S (n+1-j) and both are ±1, they are opposite.
      -- We need yAt S.doRevY j = yAt S (n+1-j) = 1.
      rw [hrev_j]
      rcases hpm_j with hj_one | hj_neg
      · -- yAt S j = 1. We show this case is impossible.
        -- j must satisfy j ≤ i: if j < i, hsym gives symmetry contradiction;
        -- if j = i, yAt S i = -1 contradicts hj_one; if j > i, i is a predecessor.
        exfalso
        by_cases hjle : j < i
        · exact hasym_S (hsym j hj1 hjle)
        · by_cases hjeq : j = i
          · rw [hjeq] at hj_one; linarith [hval]
          · have hilt : i < j := by omega
            exact hasym (hsym_S i hi1 hilt)
      · -- yAt S j = -1, so yAt S (n+1-j) ≠ -1, hence yAt S (n+1-j) = 1.
        rcases hpm with hm_one | hm_neg
        · exact hm_one
        · exfalso; exact hasym_S (by rw [hj_neg, hm_neg])
  -- Case 2: no first asymmetric index has yAt S i = -1; S already satisfies Canonical3.
  · refine ⟨S, Relation.ReflTransGen.refl, h12.1, h12.2, ?_⟩
    intro i hi1 hi2 hi3 hi4
    -- yAt S i is ±1.
    have hpm : yAt S i = 1 ∨ yAt S i = -1 := by
      exact pm_entry_of_getD S.Y.pm (by rw [S.Y.len]; omega)
    -- If yAt S i = -1, then hB would be satisfied, contradiction.
    rcases hpm with h_one | h_neg
    · exact h_one
    · exfalso
      exact hB ⟨i, hi1, hi2, hi3, hi4, h_neg⟩

/--
Accessor for `zAt` after `doRevZ` then `doNegZ` (the `−C*` transform):
`zAt S.doRevZ.doNegZ j = -(zAt S (n + 1 - j))` for `1 ≤ j ≤ n`.
-/
private lemma zAt_doNegRevZ {n : Nat} (S : TurynType n)
    {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    zAt S.doRevZ.doNegZ j = -(zAt S (n + 1 - j)) := by
  unfold zAt TurynType.doNegZ TurynType.doRevZ PmSeq.neg PmSeq.reverse
  simp only [negSeq_getD]; congr 1
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]; congr 1
  rw [List.getElem?_reverse (by rw [S.Z.len]; omega)]
  congr 1; rw [S.Z.len]; omega

/-- Step 4: enforce condition (4) by optional `−C*`. -/
theorem step4_condition4
    (n : Nat) (hn : 2 ≤ n) (S : TurynType n)
    (h123 : Canonical1 n S ∧ Canonical2 n S ∧ Canonical3 n S) :
    ∃ S4 : TurynType n,
      Equivalent n S S4 ∧ Canonical1 n S4 ∧ Canonical2 n S4 ∧
      Canonical3 n S4 ∧ Canonical4 n S4 := by
  by_cases h_exists : ∃ i, 1 ≤ i ∧ i ≤ n ∧
      (∀ j, 1 ≤ j → j < i → zAt S j ≠ zAt S (n + 1 - j)) ∧
      zAt S i = zAt S (n + 1 - i) ∧ zAt S i = -1
  · -- Positive case: apply the −C* transform (reverse C, then negate C)
    obtain ⟨i, hi1, hi2, hi3, hi4, hi5⟩ := h_exists
    refine ⟨S.doRevZ.doNegZ, ?_, ?_, h123.2.1, h123.2.2, ?_⟩
    · -- Equivalence: revC followed by negC
      exact (Relation.ReflTransGen.single (Elementary.revZ S)).trans
        (Relation.ReflTransGen.single (Elementary.negZ S.doRevZ))
    · -- Canonical1 is preserved (only zAt S' 1 needs work)
      have hcn : zAt S n = -1 := lemma1_endpoint_constraint n (by omega) S h123.1
      unfold Canonical1 at *
      obtain ⟨ha1, han, hb1, hbn, _, hd1⟩ := h123.1
      refine ⟨ha1, han, hb1, hbn, ?_, hd1⟩
      -- zAt S.doRevZ.doNegZ 1 = -(zAt S n) = -(-1) = 1
      unfold zAt TurynType.doNegZ TurynType.doRevZ PmSeq.neg PmSeq.reverse
      simp only [negSeq_getD]
      rw [List.getD_eq_getElem?_getD]
      rw [List.getElem?_reverse (by rw [S.Z.len]; omega)]
      rw [S.Z.len]
      unfold zAt at hcn; rw [List.getD_eq_getElem?_getD] at hcn
      have h0 : n - 1 - 0 = n - 1 := by omega
      rw [h0]; linarith
    · -- Canonical4: the first symmetric index of C is now +1
      intro j hj1 hj2 hj3 hj4
      -- Translate the precondition: all j' < j are asymmetric in the original S
      have hj3' : ∀ j', 1 ≤ j' → j' < j → zAt S j' ≠ zAt S (n + 1 - j') := by
        intro j' hj'1 hj'2
        have h := hj3 j' hj'1 hj'2
        rw [zAt_doNegRevZ S hj'1 (by omega),
            zAt_doNegRevZ S (by omega : 1 ≤ n + 1 - j') (by omega)] at h
        intro heq; apply h
        have : n + 1 - (n + 1 - j') = j' := by omega
        rw [this]; linarith
      -- Translate the equality: j is symmetric in the original S
      have hj4' : zAt S j = zAt S (n + 1 - j) := by
        rw [zAt_doNegRevZ S hj1 hj2,
            zAt_doNegRevZ S (by omega : 1 ≤ n + 1 - j) (by omega)] at hj4
        have : n + 1 - (n + 1 - j) = j := by omega
        rw [this] at hj4; linarith
      -- Since i is the first symmetric index and j is symmetric with all j' < j
      -- asymmetric, we must have j = i.
      have hji : j ≤ i := by
        by_contra h; exact hj3' i hi1 (by omega) hi4
      have hij : i ≤ j := by
        by_contra h; exact hi3 j hj1 (by omega) hj4'
      have heq : j = i := by omega
      subst heq
      rw [zAt_doNegRevZ S hj1 hj2, ← hi4, hi5]; norm_num
  · -- Negative case: S itself already satisfies Canonical4
    refine ⟨S, Relation.ReflTransGen.refl, h123.1, h123.2.1, h123.2.2, ?_⟩
    intro i hi1 hi2 hi3 hi4
    rcases pm_entry_of_getD S.Z.pm
      (show i - 1 < S.Z.data.length by rw [S.Z.len]; omega) with h | h
    · exact h
    · exfalso; exact h_exists ⟨i, hi1, hi2, hi3, hi4, h⟩
private lemma wAt_doNegRevW_mirror {n : Nat} (S : TurynType n) {j : Nat}
    (hj1 : 1 ≤ j) (hj2 : j ≤ n - 1) :
    wAt (TurynType.doNegW S.doRevW) (n - j) = -(wAt S j) := by
  have h1 : 1 ≤ n - j := by omega
  have h2 : n - j ≤ n - 1 := by omega
  rw [wAt_doNegRevW S h1 h2]
  have h3 : n - (n - j) = j := by omega
  rw [h3]

private lemma wAt_pm' {n : Nat} (S : TurynType n) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ n - 1) :
    wAt S i = 1 ∨ wAt S i = -1 :=
  pm_entry_of_getD S.W.pm (by rw [S.W.len]; omega)

private lemma wAt_doRevW_n1 {n : Nat} (S : TurynType n) (hn : 2 ≤ n) :
    wAt S.doRevW (n - 1) = wAt S 1 := by
  rw [wAt_doRevW S (show 1 ≤ n - 1 from by omega) (show n - 1 ≤ n - 1 from le_refl _)]
  congr 1; omega

private lemma wAt_doNegRevW_n1 {n : Nat} (S : TurynType n) (hn : 2 ≤ n) :
    wAt (TurynType.doNegW S.doRevW) (n - 1) = -(wAt S 1) := by
  rw [wAt_doNegRevW S (show 1 ≤ n - 1 from by omega) (show n - 1 ≤ n - 1 from le_refl _)]
  have h : n - (n - 1) = 1 := by omega
  rw [h]

/-- In the doRevW case, the product `wAt S' k * wAt S' (n - k)` equals
    the original product `wAt S k * wAt S (n - k)` by commutativity. -/
private lemma doRevW_product_eq {n : Nat} (S : TurynType n) {k : Nat}
    (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1) :
    wAt S.doRevW k * wAt S.doRevW (n - k) = wAt S k * wAt S (n - k) := by
  rw [wAt_doRevW S hk1 hk2, wAt_doRevW_mirror S hk1 hk2]
  ring

/-- In the doNegRevW case, the product `wAt S5 k * wAt S5 (n - k)` equals
    the original product `wAt S k * wAt S (n - k)`. -/
private lemma doNegRevW_product_eq {n : Nat} (S : TurynType n) {k : Nat}
    (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1) :
    wAt (TurynType.doNegW S.doRevW) k *
      wAt (TurynType.doNegW S.doRevW) (n - k) =
    wAt S k * wAt S (n - k) := by
  rw [wAt_doNegRevW S hk1 hk2, wAt_doNegRevW_mirror S hk1 hk2]
  ring

/-- Step 5: enforce condition (5) by optional `D*` or `−D*`. -/
theorem step5_condition5
    (n : Nat) (hn : 2 ≤ n) (S : TurynType n)
    (h1234 : Canonical1 n S ∧ Canonical2 n S ∧ Canonical3 n S ∧ Canonical4 n S) :
    ∃ S5 : TurynType n,
      Equivalent n S S5 ∧
      Canonical1 n S5 ∧ Canonical2 n S5 ∧ Canonical3 n S5 ∧
      Canonical4 n S5 ∧ Canonical5 n S5 := by
  -- If S already satisfies Canonical5, we are done.
  by_cases h5 : Canonical5 n S
  · exact ⟨S, Relation.ReflTransGen.refl, h1234.1, h1234.2.1, h1234.2.2.1, h1234.2.2.2, h5⟩
  · -- Extract the first failing index i from ¬Canonical5.
    unfold Canonical5 at h5
    push_neg at h5
    obtain ⟨i, hi1, hi2, hi3, hi4, hi5⟩ := h5
    -- Obtain wAt S 1 = 1 from Canonical1.
    have hdS1 : wAt S 1 = 1 := h1234.1.2.2.2.2.2
    -- Case split on wAt S (n - 1).
    by_cases h_case : wAt S (n - 1) = 1
    · /-  Case wAt S (n - 1) = 1: use S.doRevW as the witness.  -/
      refine ⟨S.doRevW, ?_, ?_, ?_, ?_, ?_, ?_⟩
      -- Equivalence
      · exact Relation.ReflTransGen.single (Elementary.revW S)
      -- Canonical1: only wAt changes; wAt S.doRevW 1 = wAt S (n - 1) = 1
      · exact ⟨h1234.1.1, h1234.1.2.1, h1234.1.2.2.1, h1234.1.2.2.2.1, h1234.1.2.2.2.2.1,
               by rw [wAt_doRevW S (by omega : 1 ≤ 1) (by omega : 1 ≤ n - 1)]; exact h_case⟩
      -- Canonical2 (A unchanged)
      · exact h1234.2.1
      -- Canonical3 (B unchanged)
      · exact h1234.2.2.1
      -- Canonical4 (C unchanged)
      · exact h1234.2.2.2
      -- Canonical5 for S.doRevW
      · intro j hj1 hj2 hj3 hj4
        -- Rewrite product and reference value
        rw [doRevW_product_eq S hj1 hj2, wAt_doRevW_n1 S hn, hdS1] at hj4
        -- hj4 : wAt S j * wAt S (n - j) ≠ 1
        rw [wAt_doRevW S hj1 hj2]
        -- Goal: wAt S (n - j) = 1
        -- Three sub-cases: j < i, j = i, j > i.
        by_cases hji_lt : j < i
        · -- j < i: the original hi3 says the product equals wAt S (n - 1) = 1.
          have := hi3 j hj1 hji_lt
          rw [h_case] at this
          exact absurd this hj4
        · by_cases hji_eq : j = i
          · -- j = i: wAt S i = −1 (since ≠ 1 and ±1).
            subst hji_eq
            have hdi_neg : wAt S j = -1 := by
              rcases wAt_pm' S hj1 hj2 with h | h
              · exact absurd h hi5
              · exact h
            -- wAt S (n − j) must be 1 (otherwise product = (−1)(−1) = 1, contradiction).
            rcases wAt_pm' S (show 1 ≤ n - j from by omega) (show n - j ≤ n - 1 from by omega)
              with h | h
            · exact h
            · exfalso; apply hj4; rw [hdi_neg, h]; norm_num
          · -- j > i: hj3 at k = i contradicts hi4.
            have hji_gt : i < j := by omega
            have hk_eq := hj3 i hi1 hji_gt
            rw [doRevW_product_eq S hi1 hi2, wAt_doRevW_n1 S hn, hdS1] at hk_eq
            -- hk_eq : wAt S i * wAt S (n - i) = 1
            rw [h_case] at hi4
            exact absurd hk_eq hi4
    · /- Case wAt S (n - 1) = −1: use doNegW (doRevW S) as the witness. -/
      have h_neg : wAt S (n - 1) = -1 := by
        rcases wAt_pm' S (show 1 ≤ n - 1 from by omega) (show n - 1 ≤ n - 1 from le_refl _)
          with h | h
        · exact absurd h h_case
        · exact h
      refine ⟨TurynType.doNegW S.doRevW, ?_, ?_, ?_, ?_, ?_, ?_⟩
      -- Equivalence: revD then negD
      · exact Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single (Elementary.revW S))
          (Relation.ReflTransGen.single (Elementary.negW _))
      -- Canonical1: wAt S5 1 = −(wAt S (n − 1)) = −(−1) = 1
      · refine ⟨h1234.1.1, h1234.1.2.1, h1234.1.2.2.1, h1234.1.2.2.2.1, h1234.1.2.2.2.2.1, ?_⟩
        rw [wAt_doNegRevW S (by omega : 1 ≤ 1) (by omega : 1 ≤ n - 1)]
        rw [h_neg]; norm_num
      -- Canonical2 (A unchanged)
      · exact h1234.2.1
      -- Canonical3 (B unchanged)
      · exact h1234.2.2.1
      -- Canonical4 (C unchanged)
      · exact h1234.2.2.2
      -- Canonical5 for S5 = doNegW (doRevW S)
      · intro j hj1 hj2 hj3 hj4
        -- Rewrite product and reference value
        rw [doNegRevW_product_eq S hj1 hj2, wAt_doNegRevW_n1 S hn, hdS1] at hj4
        -- hj4 : wAt S j * wAt S (n - j) ≠ -(1) = −1
        have hj4' : wAt S j * wAt S (n - j) ≠ -1 := by norm_num at hj4 ⊢; exact hj4
        rw [wAt_doNegRevW S hj1 hj2]
        -- Goal: -(wAt S (n - j)) = 1, i.e., wAt S (n - j) = −1
        -- Three sub-cases: j < i, j = i, j > i.
        by_cases hji_lt : j < i
        · -- j < i: hi3 says product = wAt S (n − 1) = −1, contradiction.
          have := hi3 j hj1 hji_lt
          rw [h_neg] at this
          exact absurd this hj4'
        · by_cases hji_eq : j = i
          · -- j = i: wAt S i = −1, so wAt S (n − i) = −1, and −(−1) = 1.
            subst hji_eq
            have hdi_neg : wAt S j = -1 := by
              rcases wAt_pm' S hj1 hj2 with h | h
              · exact absurd h hi5
              · exact h
            rcases wAt_pm' S (show 1 ≤ n - j from by omega) (show n - j ≤ n - 1 from by omega)
              with h | h
            · -- wAt S (n - j) = 1: product = (−1)(1) = −1, contradicts hj4'
              exfalso; apply hj4'; rw [hdi_neg, h]; norm_num
            · -- wAt S (n - j) = −1: −(−1) = 1 ✓
              rw [h]; norm_num
          · -- j > i: hj3 at k = i contradicts hi4.
            have hji_gt : i < j := by omega
            have hk_eq := hj3 i hi1 hji_gt
            rw [doNegRevW_product_eq S hi1 hi2, wAt_doNegRevW_n1 S hn, hdS1] at hk_eq
            rw [h_neg] at hi4
            have hk_eq' : wAt S i * wAt S (n - i) = -1 := by linarith
            exact absurd hk_eq' hi4

/-! ### Helper lemmas for step 6 -/

private lemma doSwap_xAt {n : Nat} (S : TurynType n) (i : Nat) :
    xAt S.doSwap i = yAt S i := by
  unfold xAt yAt TurynType.doSwap; rfl

private lemma doSwap_yAt {n : Nat} (S : TurynType n) (i : Nat) :
    yAt S.doSwap i = xAt S i := by
  unfold xAt yAt TurynType.doSwap; rfl

private lemma doSwap_zAt {n : Nat} (S : TurynType n) (i : Nat) :
    zAt S.doSwap i = zAt S i := by
  unfold zAt TurynType.doSwap; rfl

private lemma doSwap_wAt {n : Nat} (S : TurynType n) (i : Nat) :
    wAt S.doSwap i = wAt S i := by
  unfold wAt TurynType.doSwap; rfl

private lemma canonical1_doSwap {n : Nat} {S : TurynType n}
    (h1 : Canonical1 n S) : Canonical1 n S.doSwap := by
  unfold Canonical1 at *
  exact ⟨by rw [doSwap_xAt]; exact h1.2.2.1,
         by rw [doSwap_xAt]; exact h1.2.2.2.1,
         by rw [doSwap_yAt]; exact h1.1,
         by rw [doSwap_yAt]; exact h1.2.1,
         by rw [doSwap_zAt]; exact h1.2.2.2.2.1,
         by rw [doSwap_wAt]; exact h1.2.2.2.2.2⟩

private lemma canonical2_doSwap_of_canonical3 {n : Nat} {S : TurynType n}
    (h3 : Canonical3 n S) : Canonical2 n S.doSwap := by
  intro i hi₁ hi₂ hi₃ hi₄
  have hi₃' : ∀ j, 1 ≤ j → j < i → yAt S j = yAt S (n + 1 - j) := by
    intro j hj₁ hj₂
    have := hi₃ j hj₁ hj₂
    rw [doSwap_xAt, doSwap_xAt] at this
    exact this
  have hi₄' : yAt S i ≠ yAt S (n + 1 - i) := by
    rw [doSwap_xAt, doSwap_xAt] at hi₄
    exact hi₄
  have := h3 i hi₁ hi₂ hi₃' hi₄'
  rw [doSwap_xAt]
  exact this

private lemma canonical3_doSwap_of_canonical2 {n : Nat} {S : TurynType n}
    (h2 : Canonical2 n S) : Canonical3 n S.doSwap := by
  intro i hi₁ hi₂ hi₃ hi₄
  have hi₃' : ∀ j, 1 ≤ j → j < i → xAt S j = xAt S (n + 1 - j) := by
    intro j hj₁ hj₂
    have := hi₃ j hj₁ hj₂
    rw [doSwap_yAt, doSwap_yAt] at this
    exact this
  have hi₄' : xAt S i ≠ xAt S (n + 1 - i) := by
    rw [doSwap_yAt, doSwap_yAt] at hi₄
    exact hi₄
  have := h2 i hi₁ hi₂ hi₃' hi₄'
  rw [doSwap_yAt]
  exact this

private lemma canonical4_doSwap {n : Nat} {S : TurynType n}
    (h4 : Canonical4 n S) : Canonical4 n S.doSwap := by
  intro i hi₁ hi₂ hi₃ hi₄
  have hi₃' : ∀ j, 1 ≤ j → j < i → zAt S j ≠ zAt S (n + 1 - j) := by
    intro j hj₁ hj₂
    have := hi₃ j hj₁ hj₂
    rw [doSwap_zAt, doSwap_zAt] at this
    exact this
  have hi₄' : zAt S i = zAt S (n + 1 - i) := by
    rw [doSwap_zAt, doSwap_zAt] at hi₄
    exact hi₄
  have := h4 i hi₁ hi₂ hi₃' hi₄'
  rw [doSwap_zAt]
  exact this

private lemma canonical5_doSwap {n : Nat} {S : TurynType n}
    (h5 : Canonical5 n S) : Canonical5 n S.doSwap := by
  intro i hi₁ hi₂ hi₃ hi₄
  have hi₃' : ∀ j, 1 ≤ j → j < i → wAt S j * wAt S (n - j) = wAt S (n - 1) := by
    intro j hj₁ hj₂
    have := hi₃ j hj₁ hj₂
    rw [doSwap_wAt, doSwap_wAt, doSwap_wAt] at this
    exact this
  have hi₄' : wAt S i * wAt S (n - i) ≠ wAt S (n - 1) := by
    rw [doSwap_wAt, doSwap_wAt, doSwap_wAt] at hi₄
    exact hi₄
  have := h5 i hi₁ hi₂ hi₃' hi₄'
  rw [doSwap_wAt]
  exact this

private lemma step6_xAt_pm {n : Nat} (S : TurynType n) (i : Nat) (hi : i - 1 < n) :
    xAt S i = 1 ∨ xAt S i = -1 := by
  exact pm_entry_of_getD S.X.pm (by rw [S.X.len]; exact hi)

private lemma step6_yAt_pm {n : Nat} (S : TurynType n) (i : Nat) (hi : i - 1 < n) :
    yAt S i = 1 ∨ yAt S i = -1 := by
  exact pm_entry_of_getD S.Y.pm (by rw [S.Y.len]; exact hi)

private lemma step6_zAt_pm {n : Nat} (S : TurynType n) (i : Nat) (hi : i - 1 < n) :
    zAt S i = 1 ∨ zAt S i = -1 := by
  exact pm_entry_of_getD S.Z.pm (by rw [S.Z.len]; exact hi)

private lemma step6_wAt_pm {n : Nat} (S : TurynType n) (i : Nat) (hi : i - 1 < n - 1) :
    wAt S i = 1 ∨ wAt S i = -1 := by
  exact pm_entry_of_getD S.W.pm (by rw [S.W.len]; exact hi)

/-
Autocorrelation of a length-(m+2) sequence at lag m has exactly 2 terms.
-/
private lemma autocorr_two_terms (X : List Int) (m : Nat) (hlen : X.length = m + 2) :
    aperiodicAutocorr X m = X.getD 0 0 * X.getD m 0 + X.getD 1 0 * X.getD (m + 1) 0 := by
  unfold aperiodicAutocorr
  have hge : ¬(m ≥ X.length) := by omega
  rw [if_neg hge]
  have hlen2 : X.length - m = 2 := by omega
  rw [hlen2]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [zero_add, Nat.add_comm 1 m]

/-
Autocorrelation of a length-(m+1) sequence at lag m has exactly 1 term.
-/
private lemma autocorr_one_term (X : List Int) (m : Nat) (hlen : X.length = m + 1) :
    aperiodicAutocorr X m = X.getD 0 0 * X.getD m 0 := by
  unfold aperiodicAutocorr
  have hge : ¬(m ≥ X.length) := by omega
  rw [if_neg hge]
  have hlen1 : X.length - m = 1 := by omega
  rw [hlen1]
  rw [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [zero_add]

/-
The autocorrelation identity at lag n-2 for Turyn sequences with Canonical1.
-/
private lemma step6_autocorr_lag_n_sub_2
    (n : Nat) (hn3 : 3 ≤ n) (S : TurynType n)
    (h1 : Canonical1 n S) :
    xAt S (n - 1) + xAt S 2 + (yAt S (n - 1) + yAt S 2) +
    2 * (zAt S (n - 1) + zAt S 2 * zAt S n) +
    2 * wAt S (n - 1) = 0 := by
  -- Get vanishing at lag n-2
  have hv := S.vanishing (n - 2) (by omega) (by omega)
  unfold combinedAutocorr at hv
  -- Expand each aperiodicAutocorr
  rw [autocorr_two_terms S.X.data (n - 2) (by rw [S.X.len]; omega),
      autocorr_two_terms S.Y.data (n - 2) (by rw [S.Y.len]; omega),
      autocorr_two_terms S.Z.data (n - 2) (by rw [S.Z.len]; omega),
      autocorr_one_term S.W.data (n - 2) (by rw [S.W.len]; omega)] at hv
  -- Express xAt/yAt/zAt/wAt as getD
  have eqa_n1 : xAt S (n - 1) = S.X.data.getD (n - 2) 0 := by
    show S.X.data.getD (n - 1 - 1) 0 = S.X.data.getD (n - 2) 0; congr 1
  have eqa_2 : xAt S 2 = S.X.data.getD 1 0 := rfl
  have eqb_n1 : yAt S (n - 1) = S.Y.data.getD (n - 2) 0 := by
    show S.Y.data.getD (n - 1 - 1) 0 = S.Y.data.getD (n - 2) 0; congr 1
  have eqb_2 : yAt S 2 = S.Y.data.getD 1 0 := rfl
  have eqc_n1 : zAt S (n - 1) = S.Z.data.getD (n - 2) 0 := by
    show S.Z.data.getD (n - 1 - 1) 0 = S.Z.data.getD (n - 2) 0; congr 1
  have eqc_2 : zAt S 2 = S.Z.data.getD 1 0 := rfl
  have eqc_n : zAt S n = S.Z.data.getD (n - 1) 0 := rfl
  have eqd_n1 : wAt S (n - 1) = S.W.data.getD (n - 2) 0 := by
    show S.W.data.getD (n - 1 - 1) 0 = S.W.data.getD (n - 2) 0; congr 1
  -- Rewrite the goal to use getD
  rw [eqa_n1, eqa_2, eqb_n1, eqb_2, eqc_n1, eqc_2, eqc_n, eqd_n1]
  -- Get Canonical1 in getD form
  have h_a0 : S.X.data.getD 0 0 = 1 := by
    have := h1.1; unfold xAt at this; exact this
  have h_an1 : S.X.data.getD (n - 1) 0 = 1 := by
    have := h1.2.1; unfold xAt at this; exact this
  have h_b0 : S.Y.data.getD 0 0 = 1 := by
    have := h1.2.2.1; unfold yAt at this; exact this
  have h_bn1 : S.Y.data.getD (n - 1) 0 = 1 := by
    have := h1.2.2.2.1; unfold yAt at this; exact this
  have h_c0 : S.Z.data.getD 0 0 = 1 := by
    have := h1.2.2.2.2.1; unfold zAt at this; exact this
  have h_d0 : S.W.data.getD 0 0 = 1 := by
    have := h1.2.2.2.2.2; unfold wAt at this; exact this
  -- First normalize n-2+1 to n-1 in hv
  have hn21 : n - 2 + 1 = n - 1 := by omega
  rw [hn21] at hv
  -- Substitute Canonical1 values into hv
  rw [h_a0, h_an1, h_b0, h_bn1, h_c0, h_d0] at hv
  -- Simplify
  linarith

/-
If a,b are ±1, c,d,e*f,g are ±1, and a+b + 2c + 2d + 2(ef) + 2g = 0, then a+b = 0.
-/
private lemma step6_sum_forces_zero
    (a b c d g : Int) (ef : Int)
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1)
    (hef : ef = 1 ∨ ef = -1) (hg : g = 1 ∨ g = -1)
    (hsum : a + b + 2 * c + 2 * d + 2 * ef + 2 * g = 0) :
    a + b = 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    rcases hef with rfl | rfl <;> rcases hg with rfl | rfl <;>
    (norm_num at hsum) <;> norm_num

private lemma step6_opposite_signs
    (n : Nat) (hn_even : n % 2 = 0) (hn : 2 ≤ n) (S : TurynType n)
    (h1 : Canonical1 n S) (h_eq : xAt S 2 = yAt S 2) :
    n ≤ 2 ∨
    (xAt S (n - 1) = 1 ∧ yAt S (n - 1) = -1) ∨
    (xAt S (n - 1) = -1 ∧ yAt S (n - 1) = 1) := by
  by_cases hn3 : 3 ≤ n;
  · have h_sum : xAt S (n - 1) + yAt S (n - 1) + 2 * xAt S 2 + 2 * zAt S (n - 1) + 2 * (zAt S 2 * zAt S n) + 2 * wAt S (n - 1) = 0 := by
      convert step6_autocorr_lag_n_sub_2 n hn3 S h1 using 1 ; rw [ h_eq ] ; ring!;
    have h_cases : xAt S (n - 1) = 1 ∨ xAt S (n - 1) = -1 := by
      exact step6_xAt_pm S ( n - 1 ) ( by omega )
    have h_cases' : yAt S (n - 1) = 1 ∨ yAt S (n - 1) = -1 := by
      exact step6_yAt_pm S ( n - 1 ) ( by omega )
    have h_cases'' : xAt S 2 = 1 ∨ xAt S 2 = -1 := by
      exact step6_xAt_pm S 2 ( by omega )
    have h_cases''' : zAt S (n - 1) = 1 ∨ zAt S (n - 1) = -1 := by
      apply step6_zAt_pm; omega;
    have h_cases'''' : zAt S 2 * zAt S n = 1 ∨ zAt S 2 * zAt S n = -1 := by
      have h_cases'''' : zAt S 2 = 1 ∨ zAt S 2 = -1 := by
        apply step6_zAt_pm; omega;
      have h_cases''''' : zAt S n = 1 ∨ zAt S n = -1 := by
        apply step6_zAt_pm; omega;
      rcases h_cases'''' with h|h <;> rcases h_cases''''' with j|j <;> norm_num [ h, j ]
    have h_cases''''' : wAt S (n - 1) = 1 ∨ wAt S (n - 1) = -1 := by
      apply step6_wAt_pm; omega;
    have hab0 := step6_sum_forces_zero
      (xAt S (n - 1)) (yAt S (n - 1)) (xAt S 2) (zAt S (n - 1))
      (wAt S (n - 1)) (zAt S 2 * zAt S n)
      h_cases h_cases' h_cases'' h_cases''' h_cases'''' h_cases''''' h_sum
    rcases h_cases with ha1 | ha_neg1
    · have hb : yAt S (n - 1) = -1 := by linarith
      exact Or.inr (Or.inl ⟨ha1, hb⟩)
    · have hb : yAt S (n - 1) = 1 := by linarith
      exact Or.inr (Or.inr ⟨ha_neg1, hb⟩)
  · exact Or.inl (by omega)

/-- Step 6: enforce condition (6) using optional swap. -/
theorem step6_condition6
    (n : Nat) (hn_even : n % 2 = 0) (hn : 2 ≤ n) (S : TurynType n)
    (h12345 : Canonical1 n S ∧ Canonical2 n S ∧ Canonical3 n S ∧
              Canonical4 n S ∧ Canonical5 n S) :
    ∃ S6 : TurynType n,
      Equivalent n S S6 ∧
      Canonical1 n S6 ∧ Canonical2 n S6 ∧ Canonical3 n S6 ∧
      Canonical4 n S6 ∧ Canonical5 n S6 ∧ Canonical6 n S6 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h12345
  -- Case split: xAt S 2 ≠ yAt S 2 vs xAt S 2 = yAt S 2
  by_cases h_neq : xAt S 2 ≠ yAt S 2
  · -- Sub-case: xAt S 2 = 1
    rcases step6_xAt_pm S 2 (by omega) with h_a2_1 | h_a2_neg1
    · -- xAt S 2 = 1: S itself works
      exact ⟨S, Relation.ReflTransGen.refl, h1, h2, h3, h4, h5,
             Or.inr (Or.inl ⟨h_neq, h_a2_1⟩)⟩
    · -- xAt S 2 = -1: then yAt S 2 = 1 (since they differ and are ±1)
      have h_b2 : yAt S 2 = 1 := by
        rcases step6_yAt_pm S 2 (by omega) with h | h
        · exact h
        · exfalso; exact h_neq (by rw [h_a2_neg1, h])
      -- Use S.doSwap
      refine ⟨S.doSwap, Relation.ReflTransGen.single (Elementary.swap S),
              canonical1_doSwap h1,
              canonical2_doSwap_of_canonical3 h3,
              canonical3_doSwap_of_canonical2 h2,
              canonical4_doSwap h4,
              canonical5_doSwap h5,
              ?_⟩
      -- Show Canonical6 for doSwap
      unfold Canonical6
      right; left
      exact ⟨by rw [doSwap_xAt, doSwap_yAt]; exact fun h => h_neq h.symm,
             by rw [doSwap_xAt]; exact h_b2⟩
  · -- xAt S 2 = yAt S 2
    push_neg at h_neq
    -- Use step6_opposite_signs to get sign information at position n-1
    rcases step6_opposite_signs n hn_even hn S h1 h_neq with h_le2 | ⟨ha_pos, hb_neg⟩ | ⟨ha_neg, hb_pos⟩
    · -- n ≤ 2: Canonical6 is trivially satisfied
      exact ⟨S, Relation.ReflTransGen.refl, h1, h2, h3, h4, h5, Or.inl h_le2⟩
    · -- xAt S (n-1) = 1, yAt S (n-1) = -1: S works directly
      exact ⟨S, Relation.ReflTransGen.refl, h1, h2, h3, h4, h5,
             Or.inr (Or.inr ⟨h_neq, ha_pos, hb_neg⟩)⟩
    · -- xAt S (n-1) = -1, yAt S (n-1) = 1: use S.doSwap
      refine ⟨S.doSwap, Relation.ReflTransGen.single (Elementary.swap S),
              canonical1_doSwap h1,
              canonical2_doSwap_of_canonical3 h3,
              canonical3_doSwap_of_canonical2 h2,
              canonical4_doSwap h4,
              canonical5_doSwap h5,
              ?_⟩
      unfold Canonical6
      right; right
      exact ⟨by rw [doSwap_xAt, doSwap_yAt]; exact h_neq.symm,
             by rw [doSwap_xAt]; exact hb_pos,
             by rw [doSwap_yAt]; exact ha_neg⟩

/-- Every equivalence class of Turyn-type sequences has a canonical representative.

This is the main theorem of the normalization theory from
Best–Đoković–Kharaghani–Ramp (arXiv:1206.4107, 2013). -/
theorem canonical_representative_exists
    (n : Nat) (hn_even : n % 2 = 0) (hn : 2 ≤ n) (S : TurynType n) :
    ∃ T : TurynType n, Equivalent n S T ∧ Canonical n T := by
  rcases step1_condition1 n hn_even hn S with ⟨S1, hSS1, h1⟩
  rcases step2_condition2 n hn S1 h1 with ⟨S2, hS1S2, h1S2, h2S2⟩
  rcases step3_condition3 n hn S2 ⟨h1S2, h2S2⟩ with ⟨S3, hS2S3, h1S3, h2S3, h3S3⟩
  rcases step4_condition4 n hn S3 ⟨h1S3, h2S3, h3S3⟩ with ⟨S4, hS3S4, h1S4, h2S4, h3S4, h4S4⟩
  rcases step5_condition5 n hn S4 ⟨h1S4, h2S4, h3S4, h4S4⟩ with
    ⟨S5, hS4S5, h1S5, h2S5, h3S5, h4S5, h5S5⟩
  rcases step6_condition6 n hn_even hn S5 ⟨h1S5, h2S5, h3S5, h4S5, h5S5⟩ with
    ⟨S6, hS5S6, h1S6, h2S6, h3S6, h4S6, h5S6, h6S6⟩
  exact ⟨S6,
    equivalent_trans n (equivalent_trans n (equivalent_trans n
      (equivalent_trans n hSS1 hS1S2) hS2S3) hS3S4)
      (equivalent_trans n hS4S5 hS5S6),
    h1S6, h2S6, h3S6, h4S6, h5S6, h6S6⟩

end Turyn
