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

/-! ### IsTurynTypeProp preservation under each elementary transformation -/

lemma turynProp_negA {n : Nat} {A B C D : List Int}
    (h : IsTurynTypeProp n A B C D) : IsTurynTypeProp n (negSeq A) B C D where
  x_len := by simp [negSeq, h.x_len]
  y_len := h.y_len
  z_len := h.z_len
  w_len := h.w_len
  x_pm := AllPmOne_neg h.x_pm
  y_pm := h.y_pm
  z_pm := h.z_pm
  w_pm := h.w_pm
  vanishing := fun s hs1 hs2 => by
    have := h.vanishing s hs1 hs2
    unfold combinedAutocorr at this ⊢; rw [aperiodicAutocorr_neg]; exact this

lemma turynProp_negB {n : Nat} {A B C D : List Int}
    (h : IsTurynTypeProp n A B C D) : IsTurynTypeProp n A (negSeq B) C D where
  x_len := h.x_len
  y_len := by simp [negSeq, h.y_len]
  z_len := h.z_len
  w_len := h.w_len
  x_pm := h.x_pm
  y_pm := AllPmOne_neg h.y_pm
  z_pm := h.z_pm
  w_pm := h.w_pm
  vanishing := fun s hs1 hs2 => by
    have := h.vanishing s hs1 hs2
    unfold combinedAutocorr at this ⊢; rw [aperiodicAutocorr_neg]; exact this

lemma turynProp_negC {n : Nat} {A B C D : List Int}
    (h : IsTurynTypeProp n A B C D) : IsTurynTypeProp n A B (negSeq C) D where
  x_len := h.x_len
  y_len := h.y_len
  z_len := by simp [negSeq, h.z_len]
  w_len := h.w_len
  x_pm := h.x_pm
  y_pm := h.y_pm
  z_pm := AllPmOne_neg h.z_pm
  w_pm := h.w_pm
  vanishing := fun s hs1 hs2 => by
    have := h.vanishing s hs1 hs2
    unfold combinedAutocorr at this ⊢; rw [aperiodicAutocorr_neg]; exact this

lemma turynProp_negD {n : Nat} {A B C D : List Int}
    (h : IsTurynTypeProp n A B C D) : IsTurynTypeProp n A B C (negSeq D) where
  x_len := h.x_len
  y_len := h.y_len
  z_len := h.z_len
  w_len := by simp [negSeq, h.w_len]
  x_pm := h.x_pm
  y_pm := h.y_pm
  z_pm := h.z_pm
  w_pm := AllPmOne_neg h.w_pm
  vanishing := fun s hs1 hs2 => by
    have := h.vanishing s hs1 hs2
    unfold combinedAutocorr at this ⊢; rw [aperiodicAutocorr_neg]; exact this

lemma turynProp_revA {n : Nat} {A B C D : List Int}
    (h : IsTurynTypeProp n A B C D) : IsTurynTypeProp n A.reverse B C D where
  x_len := by simp [h.x_len]
  y_len := h.y_len
  z_len := h.z_len
  w_len := h.w_len
  x_pm := AllPmOne_reverse h.x_pm
  y_pm := h.y_pm
  z_pm := h.z_pm
  w_pm := h.w_pm
  vanishing := fun s hs1 hs2 => by
    have := h.vanishing s hs1 hs2
    unfold combinedAutocorr at this ⊢; rw [aperiodicAutocorr_rev]; exact this

lemma turynProp_revB {n : Nat} {A B C D : List Int}
    (h : IsTurynTypeProp n A B C D) : IsTurynTypeProp n A B.reverse C D where
  x_len := h.x_len
  y_len := by simp [h.y_len]
  z_len := h.z_len
  w_len := h.w_len
  x_pm := h.x_pm
  y_pm := AllPmOne_reverse h.y_pm
  z_pm := h.z_pm
  w_pm := h.w_pm
  vanishing := fun s hs1 hs2 => by
    have := h.vanishing s hs1 hs2
    unfold combinedAutocorr at this ⊢; rw [aperiodicAutocorr_rev]; exact this

lemma turynProp_revC {n : Nat} {A B C D : List Int}
    (h : IsTurynTypeProp n A B C D) : IsTurynTypeProp n A B C.reverse D where
  x_len := h.x_len
  y_len := h.y_len
  z_len := by simp [h.z_len]
  w_len := h.w_len
  x_pm := h.x_pm
  y_pm := h.y_pm
  z_pm := AllPmOne_reverse h.z_pm
  w_pm := h.w_pm
  vanishing := fun s hs1 hs2 => by
    have := h.vanishing s hs1 hs2
    unfold combinedAutocorr at this ⊢; rw [aperiodicAutocorr_rev]; exact this

lemma turynProp_revD {n : Nat} {A B C D : List Int}
    (h : IsTurynTypeProp n A B C D) : IsTurynTypeProp n A B C D.reverse where
  x_len := h.x_len
  y_len := h.y_len
  z_len := h.z_len
  w_len := by simp [h.w_len]
  x_pm := h.x_pm
  y_pm := h.y_pm
  z_pm := h.z_pm
  w_pm := AllPmOne_reverse h.w_pm
  vanishing := fun s hs1 hs2 => by
    have := h.vanishing s hs1 hs2
    unfold combinedAutocorr at this ⊢; rw [aperiodicAutocorr_rev]; exact this

lemma turynProp_altAll {n : Nat} {A B C D : List Int}
    (h : IsTurynTypeProp n A B C D) :
    IsTurynTypeProp n (Turyn.altSeq A) (Turyn.altSeq B) (Turyn.altSeq C) (Turyn.altSeq D) where
  x_len := by simp [Turyn.altSeq, h.x_len]
  y_len := by simp [Turyn.altSeq, h.y_len]
  z_len := by simp [Turyn.altSeq, h.z_len]
  w_len := by simp [Turyn.altSeq, h.w_len]
  x_pm := AllPmOne_alt h.x_pm
  y_pm := AllPmOne_alt h.y_pm
  z_pm := AllPmOne_alt h.z_pm
  w_pm := AllPmOne_alt h.w_pm
  vanishing := fun s hs1 hs2 => by
    have hv := h.vanishing s hs1 hs2
    unfold combinedAutocorr at hv ⊢
    rw [aperiodicAutocorr_alt, aperiodicAutocorr_alt, aperiodicAutocorr_alt, aperiodicAutocorr_alt]
    have factored : (-1 : Int) ^ s * aperiodicAutocorr A s + (-1 : Int) ^ s * aperiodicAutocorr B s +
        2 * ((-1 : Int) ^ s * aperiodicAutocorr C s) + 2 * ((-1 : Int) ^ s * aperiodicAutocorr D s) =
        (-1 : Int) ^ s * (aperiodicAutocorr A s + aperiodicAutocorr B s +
        2 * aperiodicAutocorr C s + 2 * aperiodicAutocorr D s) := by ring
    rw [factored, hv, mul_zero]

lemma turynProp_swapAB {n : Nat} {A B C D : List Int}
    (h : IsTurynTypeProp n A B C D) : IsTurynTypeProp n B A C D where
  x_len := h.y_len
  y_len := h.x_len
  z_len := h.z_len
  w_len := h.w_len
  x_pm := h.y_pm
  y_pm := h.x_pm
  z_pm := h.z_pm
  w_pm := h.w_pm
  vanishing := fun s hs1 hs2 => by
    have := h.vanishing s hs1 hs2; unfold combinedAutocorr at this ⊢; linarith

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

/-! ### Turyn-type quadruple -/

/-- A Turyn-type quadruple packaged as a single object.  Each component is
a length-indexed `PmSeq`; the only remaining propositional content is the
combined-autocorrelation vanishing identity. -/
structure TurynTypeSeq (n : Nat) where
  A : PmSeq n
  B : PmSeq n
  C : PmSeq n
  D : PmSeq (n - 1)
  vanishing : ∀ s : Nat, 1 ≤ s → s < n →
    combinedAutocorr A.data B.data C.data D.data s = 0

/-- Backward-compat accessor: lift the carrier-level length/pm proofs and
the vanishing field into the raw-list `IsTurynTypeProp` form used by the
existing step lemmas. -/
def TurynTypeSeq.isTuryn {n : Nat} (S : TurynTypeSeq n) :
    IsTurynTypeProp n S.A.data S.B.data S.C.data S.D.data where
  x_len := S.A.len
  y_len := S.B.len
  z_len := S.C.len
  w_len := S.D.len
  x_pm := S.A.pm
  y_pm := S.B.pm
  z_pm := S.C.pm
  w_pm := S.D.pm
  vanishing := S.vanishing

/-- Entry accessor for `A` (1-indexed). -/
def aAt {n : Nat} (S : TurynTypeSeq n) (i : Nat) : Int := S.A.data.getD (i - 1) 0
/-- Entry accessor for `B` (1-indexed). -/
def bAt {n : Nat} (S : TurynTypeSeq n) (i : Nat) : Int := S.B.data.getD (i - 1) 0
/-- Entry accessor for `C` (1-indexed). -/
def cAt {n : Nat} (S : TurynTypeSeq n) (i : Nat) : Int := S.C.data.getD (i - 1) 0
/-- Entry accessor for `D` (1-indexed). -/
def dAt {n : Nat} (S : TurynTypeSeq n) (i : Nat) : Int := S.D.data.getD (i - 1) 0

/-! ### TurynTypeSeq transformations -/

def TurynTypeSeq.doNegA {n : Nat} (S : TurynTypeSeq n) : TurynTypeSeq n :=
  ⟨S.A.neg, S.B, S.C, S.D, (turynProp_negA S.isTuryn).vanishing⟩

def TurynTypeSeq.doNegB {n : Nat} (S : TurynTypeSeq n) : TurynTypeSeq n :=
  ⟨S.A, S.B.neg, S.C, S.D, (turynProp_negB S.isTuryn).vanishing⟩

def TurynTypeSeq.doNegC {n : Nat} (S : TurynTypeSeq n) : TurynTypeSeq n :=
  ⟨S.A, S.B, S.C.neg, S.D, (turynProp_negC S.isTuryn).vanishing⟩

def TurynTypeSeq.doNegD {n : Nat} (S : TurynTypeSeq n) : TurynTypeSeq n :=
  ⟨S.A, S.B, S.C, S.D.neg, (turynProp_negD S.isTuryn).vanishing⟩

def TurynTypeSeq.doRevA {n : Nat} (S : TurynTypeSeq n) : TurynTypeSeq n :=
  ⟨S.A.reverse, S.B, S.C, S.D, (turynProp_revA S.isTuryn).vanishing⟩

def TurynTypeSeq.doRevB {n : Nat} (S : TurynTypeSeq n) : TurynTypeSeq n :=
  ⟨S.A, S.B.reverse, S.C, S.D, (turynProp_revB S.isTuryn).vanishing⟩

def TurynTypeSeq.doRevC {n : Nat} (S : TurynTypeSeq n) : TurynTypeSeq n :=
  ⟨S.A, S.B, S.C.reverse, S.D, (turynProp_revC S.isTuryn).vanishing⟩

def TurynTypeSeq.doRevD {n : Nat} (S : TurynTypeSeq n) : TurynTypeSeq n :=
  ⟨S.A, S.B, S.C, S.D.reverse, (turynProp_revD S.isTuryn).vanishing⟩

def TurynTypeSeq.doAltAll {n : Nat} (S : TurynTypeSeq n) : TurynTypeSeq n :=
  ⟨S.A.alt, S.B.alt, S.C.alt, S.D.alt, (turynProp_altAll S.isTuryn).vanishing⟩

def TurynTypeSeq.doSwap {n : Nat} (S : TurynTypeSeq n) : TurynTypeSeq n :=
  ⟨S.B, S.A, S.C, S.D, (turynProp_swapAB S.isTuryn).vanishing⟩

/-! ### Bridge to typed TurynType -/

/-- Convert a `TurynTypeSeq` to the typed `TurynType` wrapper. -/
def TurynTypeSeq.toTyped {n : Nat} (S : TurynTypeSeq n) : TurynType n :=
  ⟨S.A, S.B, S.C, S.D, S.vanishing⟩

@[simp] lemma TurynTypeSeq.toTyped_x_data {n : Nat} (S : TurynTypeSeq n) :
    (S.toTyped).x.data = S.A.data := rfl

@[simp] lemma TurynTypeSeq.toTyped_y_data {n : Nat} (S : TurynTypeSeq n) :
    (S.toTyped).y.data = S.B.data := rfl

@[simp] lemma TurynTypeSeq.toTyped_z_data {n : Nat} (S : TurynTypeSeq n) :
    (S.toTyped).z.data = S.C.data := rfl

@[simp] lemma TurynTypeSeq.toTyped_w_data {n : Nat} (S : TurynTypeSeq n) :
    (S.toTyped).w.data = S.D.data := rfl

/-! ### Elementary transformations -/

/-- Elementary transformations between Turyn-type sequences.

These encode the four move families from Best–Đoković–Kharaghani–Ramp (2013):
- (T1) Negate one component
- (T2) Reverse one component
- (T3) Alternate all four components
- (T4) Swap A and B -/
inductive Elementary (n : Nat) : TurynTypeSeq n → TurynTypeSeq n → Prop where
  | negA (S : TurynTypeSeq n) : Elementary n S S.doNegA
  | negB (S : TurynTypeSeq n) : Elementary n S S.doNegB
  | negC (S : TurynTypeSeq n) : Elementary n S S.doNegC
  | negD (S : TurynTypeSeq n) : Elementary n S S.doNegD
  | revA (S : TurynTypeSeq n) : Elementary n S S.doRevA
  | revB (S : TurynTypeSeq n) : Elementary n S S.doRevB
  | revC (S : TurynTypeSeq n) : Elementary n S S.doRevC
  | revD (S : TurynTypeSeq n) : Elementary n S S.doRevD
  | altAll (S : TurynTypeSeq n) : Elementary n S S.doAltAll
  | swap (S : TurynTypeSeq n) : Elementary n S S.doSwap

/-- Equivalence is the reflexive-transitive closure of elementary transformations. -/
def Equivalent (n : Nat) (S T : TurynTypeSeq n) : Prop :=
  Relation.ReflTransGen (Elementary n) S T

/-- A single elementary step implies equivalence. -/
lemma Elementary.toEquivalent {n : Nat} {S T : TurynTypeSeq n}
    (h : Elementary n S T) : Equivalent n S T :=
  Relation.ReflTransGen.single h

/-! ### Canonical conditions -/

/-- Canonical condition (1): endpoint signs. -/
def Canonical1 (n : Nat) (S : TurynTypeSeq n) : Prop :=
  aAt S 1 = 1 ∧ aAt S n = 1 ∧
  bAt S 1 = 1 ∧ bAt S n = 1 ∧
  cAt S 1 = 1 ∧ dAt S 1 = 1

/-- Canonical condition (2) for `A`. -/
def Canonical2 (n : Nat) (S : TurynTypeSeq n) : Prop :=
  ∀ i, 1 ≤ i → i ≤ n →
    (∀ j, 1 ≤ j → j < i → aAt S j = aAt S (n + 1 - j)) →
    aAt S i ≠ aAt S (n + 1 - i) →
    aAt S i = 1

/-- Canonical condition (3) for `B`. -/
def Canonical3 (n : Nat) (S : TurynTypeSeq n) : Prop :=
  ∀ i, 1 ≤ i → i ≤ n →
    (∀ j, 1 ≤ j → j < i → bAt S j = bAt S (n + 1 - j)) →
    bAt S i ≠ bAt S (n + 1 - i) →
    bAt S i = 1

/-- Canonical condition (4) for `C`. -/
def Canonical4 (n : Nat) (S : TurynTypeSeq n) : Prop :=
  ∀ i, 1 ≤ i → i ≤ n →
    (∀ j, 1 ≤ j → j < i → cAt S j ≠ cAt S (n + 1 - j)) →
    cAt S i = cAt S (n + 1 - i) →
    cAt S i = 1

/-- Canonical condition (5) for `D`. -/
def Canonical5 (n : Nat) (S : TurynTypeSeq n) : Prop :=
  ∀ i, 1 ≤ i → i ≤ n - 1 →
    (∀ j, 1 ≤ j → j < i → dAt S j * dAt S (n - j) = dAt S (n - 1)) →
    dAt S i * dAt S (n - i) ≠ dAt S (n - 1) →
    dAt S i = 1

/-- Canonical condition (6): tie-breaker between `A` and `B`. -/
def Canonical6 (n : Nat) (S : TurynTypeSeq n) : Prop :=
  n ≤ 2 ∨
  ((aAt S 2 ≠ bAt S 2 ∧ aAt S 2 = 1) ∨
   (aAt S 2 = bAt S 2 ∧ aAt S (n - 1) = 1 ∧ bAt S (n - 1) = -1))

/-- Full canonical predicate. -/
def Canonical (n : Nat) (S : TurynTypeSeq n) : Prop :=
  Canonical1 n S ∧ Canonical2 n S ∧ Canonical3 n S ∧
  Canonical4 n S ∧ Canonical5 n S ∧ Canonical6 n S

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

lemma endpoint_relation {n : Nat} (hn : 1 < n) (S : TurynTypeSeq n) :
    aAt S 1 * aAt S n + bAt S 1 * bAt S n + 2 * (cAt S 1 * cAt S n) = 0 := by
      convert S.isTuryn.vanishing ( n - 1 ) ( Nat.sub_pos_of_lt hn ) ( Nat.sub_lt ( by linarith ) zero_lt_one ) using 1;
      unfold combinedAutocorr;
      unfold aAt bAt cAt; simp +arith +decide [ * ] ;
      rw [ aperiodicAutocorr_last, aperiodicAutocorr_last, aperiodicAutocorr_last ] <;> norm_num [ S.isTuryn.x_len, S.isTuryn.y_len, S.isTuryn.z_len, S.isTuryn.w_len ];
      · unfold aperiodicAutocorr; simp +decide [ S.isTuryn.w_len ] ;
        ring;
      · linarith;
      · linarith;
      · linarith

theorem lemma1_endpoint_constraint
    (n : Nat) (hn : 1 < n) (S : TurynTypeSeq n)
    (h1 : Canonical1 n S) :
    cAt S n = -1 := by
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
    (n : Nat) {S T U : TurynTypeSeq n} :
    Equivalent n S T → Equivalent n T U → Equivalent n S U :=
  Relation.ReflTransGen.trans

/-! ### Private helpers for step1_condition1 -/

private lemma step1_aAt_doNegA {n : Nat} (S : TurynTypeSeq n) (i : Nat) :
    aAt S.doNegA i = -(aAt S i) := by
  unfold aAt TurynTypeSeq.doNegA PmSeq.neg; exact negSeq_getD _ _

private lemma step1_bAt_doNegB {n : Nat} (S : TurynTypeSeq n) (i : Nat) :
    bAt S.doNegB i = -(bAt S i) := by
  unfold bAt TurynTypeSeq.doNegB PmSeq.neg; exact negSeq_getD _ _

private lemma step1_cAt_doNegC {n : Nat} (S : TurynTypeSeq n) (i : Nat) :
    cAt S.doNegC i = -(cAt S i) := by
  unfold cAt TurynTypeSeq.doNegC PmSeq.neg; exact negSeq_getD _ _

private lemma step1_dAt_doNegD {n : Nat} (S : TurynTypeSeq n) (i : Nat) :
    dAt S.doNegD i = -(dAt S i) := by
  unfold dAt TurynTypeSeq.doNegD PmSeq.neg; exact negSeq_getD _ _

private lemma step1_aAt_doAltAll_first {n : Nat} (S : TurynTypeSeq n) (hn : 1 ≤ n) :
    aAt S.doAltAll 1 = aAt S 1 := by
  unfold aAt TurynTypeSeq.doAltAll PmSeq.alt
  exact altSeq_getD_zero S.A.data (by rw [S.isTuryn.x_len]; omega)

private lemma step1_bAt_doAltAll_first {n : Nat} (S : TurynTypeSeq n) (hn : 1 ≤ n) :
    bAt S.doAltAll 1 = bAt S 1 := by
  unfold bAt TurynTypeSeq.doAltAll PmSeq.alt
  exact altSeq_getD_zero S.B.data (by rw [S.isTuryn.y_len]; omega)

private lemma step1_cAt_doAltAll_first {n : Nat} (S : TurynTypeSeq n) (hn : 1 ≤ n) :
    cAt S.doAltAll 1 = cAt S 1 := by
  unfold cAt TurynTypeSeq.doAltAll PmSeq.alt
  exact altSeq_getD_zero S.C.data (by rw [S.isTuryn.z_len]; omega)

private lemma step1_dAt_doAltAll_first {n : Nat} (S : TurynTypeSeq n) (hn : 2 ≤ n) :
    dAt S.doAltAll 1 = dAt S 1 := by
  unfold dAt TurynTypeSeq.doAltAll PmSeq.alt
  exact altSeq_getD_zero S.D.data (by rw [S.isTuryn.w_len]; omega)

private lemma step1_aAt_doAltAll_last {n : Nat} (S : TurynTypeSeq n)
    (hn_even : n % 2 = 0) (hn : 2 ≤ n) :
    aAt S.doAltAll n = -(aAt S n) := by
  unfold aAt TurynTypeSeq.doAltAll PmSeq.alt
  have hlen := S.isTuryn.x_len
  have h := altSeq_getD_last S.A.data (by rw [hlen]; exact hn_even) (by rw [hlen]; exact hn)
  rw [hlen] at h; exact h

private lemma step1_bAt_doAltAll_last {n : Nat} (S : TurynTypeSeq n)
    (hn_even : n % 2 = 0) (hn : 2 ≤ n) :
    bAt S.doAltAll n = -(bAt S n) := by
  unfold bAt TurynTypeSeq.doAltAll PmSeq.alt
  have hlen := S.isTuryn.y_len
  have h := altSeq_getD_last S.B.data (by rw [hlen]; exact hn_even) (by rw [hlen]; exact hn)
  rw [hlen] at h; exact h

/-- Step 1: enforce condition (1) — normalize endpoint signs. -/
theorem step1_condition1
    (n : Nat) (hn_even : n % 2 = 0) (hn : 2 ≤ n) (S : TurynTypeSeq n) :
    ∃ S1 : TurynTypeSeq n, Equivalent n S S1 ∧ Canonical1 n S1 := by
  -- Phase 1: Normalize first entries of A, B, C, D to +1 by optional negations.
  -- Step 1a: Normalize aAt 1 to +1.
  have ha_pm : aAt S 1 = 1 ∨ aAt S 1 = -1 :=
    pm_entry_of_getD S.isTuryn.x_pm (by rw [S.isTuryn.x_len]; omega)
  obtain ⟨Sa, hSa_eq, hSa_a1⟩ : ∃ Sa : TurynTypeSeq n,
      Equivalent n S Sa ∧ aAt Sa 1 = 1 := by
    rcases ha_pm with ha1 | ha1
    · exact ⟨S, Relation.ReflTransGen.refl, ha1⟩
    · exact ⟨S.doNegA, Relation.ReflTransGen.single (Elementary.negA S),
        by rw [step1_aAt_doNegA, ha1]; norm_num⟩
  -- Step 1b: Normalize bAt 1 to +1 (doNegB preserves A).
  have hb_pm : bAt Sa 1 = 1 ∨ bAt Sa 1 = -1 :=
    pm_entry_of_getD Sa.isTuryn.y_pm (by rw [Sa.isTuryn.y_len]; omega)
  obtain ⟨Sb, hSb_eq, hSb_a1, hSb_b1⟩ : ∃ Sb : TurynTypeSeq n,
      Equivalent n Sa Sb ∧ aAt Sb 1 = 1 ∧ bAt Sb 1 = 1 := by
    rcases hb_pm with hb1 | hb1
    · exact ⟨Sa, Relation.ReflTransGen.refl, hSa_a1, hb1⟩
    · exact ⟨Sa.doNegB, Relation.ReflTransGen.single (Elementary.negB Sa),
        hSa_a1, -- aAt Sa.doNegB 1 = aAt Sa 1 = 1 (definitional)
        by rw [step1_bAt_doNegB, hb1]; norm_num⟩
  -- Step 1c: Normalize cAt 1 to +1 (doNegC preserves A, B).
  have hc_pm : cAt Sb 1 = 1 ∨ cAt Sb 1 = -1 :=
    pm_entry_of_getD Sb.isTuryn.z_pm (by rw [Sb.isTuryn.z_len]; omega)
  obtain ⟨Sc, hSc_eq, hSc_a1, hSc_b1, hSc_c1⟩ : ∃ Sc : TurynTypeSeq n,
      Equivalent n Sb Sc ∧ aAt Sc 1 = 1 ∧ bAt Sc 1 = 1 ∧ cAt Sc 1 = 1 := by
    rcases hc_pm with hc1 | hc1
    · exact ⟨Sb, Relation.ReflTransGen.refl, hSb_a1, hSb_b1, hc1⟩
    · exact ⟨Sb.doNegC, Relation.ReflTransGen.single (Elementary.negC Sb),
        hSb_a1, -- aAt Sb.doNegC 1 = aAt Sb 1 (definitional)
        hSb_b1, -- bAt Sb.doNegC 1 = bAt Sb 1 (definitional)
        by rw [step1_cAt_doNegC, hc1]; norm_num⟩
  -- Step 1d: Normalize dAt 1 to +1 (doNegD preserves A, B, C).
  have hd_pm : dAt Sc 1 = 1 ∨ dAt Sc 1 = -1 :=
    pm_entry_of_getD Sc.isTuryn.w_pm (by rw [Sc.isTuryn.w_len]; omega)
  obtain ⟨Sd, hSd_eq, hSd_a1, hSd_b1, hSd_c1, hSd_d1⟩ : ∃ Sd : TurynTypeSeq n,
      Equivalent n Sc Sd ∧ aAt Sd 1 = 1 ∧ bAt Sd 1 = 1 ∧ cAt Sd 1 = 1 ∧ dAt Sd 1 = 1 := by
    rcases hd_pm with hd1 | hd1
    · exact ⟨Sc, Relation.ReflTransGen.refl, hSc_a1, hSc_b1, hSc_c1, hd1⟩
    · exact ⟨Sc.doNegD, Relation.ReflTransGen.single (Elementary.negD Sc),
        hSc_a1, hSc_b1, hSc_c1,
        by rw [step1_dAt_doNegD, hd1]; norm_num⟩
  -- Chain equivalences: S ~ Sa ~ Sb ~ Sc ~ Sd.
  have hS_Sd : Equivalent n S Sd :=
    (hSa_eq.trans hSb_eq).trans (hSc_eq.trans hSd_eq)
  -- Phase 2: Handle last entries aAt n and bAt n.
  -- Obtain ±1 witnesses for positions n.
  have ha_n_pm : aAt Sd n = 1 ∨ aAt Sd n = -1 :=
    pm_entry_of_getD Sd.isTuryn.x_pm (by rw [Sd.isTuryn.x_len]; omega)
  have hb_n_pm : bAt Sd n = 1 ∨ bAt Sd n = -1 :=
    pm_entry_of_getD Sd.isTuryn.y_pm (by rw [Sd.isTuryn.y_len]; omega)
  have hc_n_pm : cAt Sd n = 1 ∨ cAt Sd n = -1 :=
    pm_entry_of_getD Sd.isTuryn.z_pm (by rw [Sd.isTuryn.z_len]; omega)
  -- Endpoint relation with known first entries substituted.
  have h_ep_raw := endpoint_relation (show 1 < n by omega) Sd
  rw [hSd_a1, hSd_b1, hSd_c1] at h_ep_raw
  -- h_ep_raw : 1 * aAt Sd n + 1 * bAt Sd n + 2 * (1 * cAt Sd n) = 0
  have h_ep : aAt Sd n + bAt Sd n + 2 * cAt Sd n = 0 := by linarith
  -- Case split: are both last entries -1?
  by_cases h_both_neg : aAt Sd n = -1 ∧ bAt Sd n = -1
  · -- Both aAt n and bAt n are -1: apply doAltAll to flip signs of last entries.
    obtain ⟨ha_neg, hb_neg⟩ := h_both_neg
    have hAltAll_a1 : aAt Sd.doAltAll 1 = 1 := by
      rw [step1_aAt_doAltAll_first Sd (by omega)]; exact hSd_a1
    have hAltAll_an : aAt Sd.doAltAll n = 1 := by
      rw [step1_aAt_doAltAll_last Sd hn_even hn, ha_neg]; norm_num
    have hAltAll_b1 : bAt Sd.doAltAll 1 = 1 := by
      rw [step1_bAt_doAltAll_first Sd (by omega)]; exact hSd_b1
    have hAltAll_bn : bAt Sd.doAltAll n = 1 := by
      rw [step1_bAt_doAltAll_last Sd hn_even hn, hb_neg]; norm_num
    have hAltAll_c1 : cAt Sd.doAltAll 1 = 1 := by
      rw [step1_cAt_doAltAll_first Sd (by omega)]; exact hSd_c1
    have hAltAll_d1 : dAt Sd.doAltAll 1 = 1 := by
      rw [step1_dAt_doAltAll_first Sd hn]; exact hSd_d1
    exact ⟨Sd.doAltAll,
      hS_Sd.trans (Elementary.toEquivalent (Elementary.altAll Sd)),
      hAltAll_a1, hAltAll_an, hAltAll_b1, hAltAll_bn, hAltAll_c1, hAltAll_d1⟩
  · -- Not both -1: deduce both must be +1 via exhaustive ±1 case analysis.
    have h_last : aAt Sd n = 1 ∧ bAt Sd n = 1 := by
      rcases ha_n_pm with ha_n | ha_n <;> rcases hb_n_pm with hb_n | hb_n <;>
          rcases hc_n_pm with hc_n | hc_n
      -- aAt=1, bAt=1, cAt=1: 1+1+2*1=4≠0
      · rw [ha_n, hb_n, hc_n] at h_ep; norm_num at h_ep
      -- aAt=1, bAt=1, cAt=-1: 1+1+2*(-1)=0 ✓
      · exact ⟨ha_n, hb_n⟩
      -- aAt=1, bAt=-1, cAt=1: 1+(-1)+2*1=2≠0
      · rw [ha_n, hb_n, hc_n] at h_ep; norm_num at h_ep
      -- aAt=1, bAt=-1, cAt=-1: 1+(-1)+2*(-1)=-2≠0
      · rw [ha_n, hb_n, hc_n] at h_ep; norm_num at h_ep
      -- aAt=-1, bAt=1, cAt=1: -1+1+2*1=2≠0
      · rw [ha_n, hb_n, hc_n] at h_ep; norm_num at h_ep
      -- aAt=-1, bAt=1, cAt=-1: -1+1+2*(-1)=-2≠0
      · rw [ha_n, hb_n, hc_n] at h_ep; norm_num at h_ep
      -- aAt=-1, bAt=-1, cAt=1: contradicts ¬(both=-1)
      · exact absurd ⟨ha_n, hb_n⟩ h_both_neg
      -- aAt=-1, bAt=-1, cAt=-1: -1+(-1)+2*(-1)=-4≠0
      · rw [ha_n, hb_n, hc_n] at h_ep; norm_num at h_ep
    exact ⟨Sd, hS_Sd, hSd_a1, h_last.1, hSd_b1, h_last.2, hSd_c1, hSd_d1⟩

/-! ### Private helpers for step2 -/

private lemma revA_getD_eq {n : Nat} (S : TurynTypeSeq n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    S.A.reverse.data.getD (j - 1) 0 = S.A.data.getD (n - j) 0 := by
  have hlt : j - 1 < S.A.data.length := by rw [S.isTuryn.x_len]; omega
  show S.A.data.reverse.getD (j - 1) 0 = S.A.data.getD (n - j) 0
  unfold List.getD
  rw [List.getElem?_reverse hlt]
  have : S.A.data.length - 1 - (j - 1) = n - j := by rw [S.isTuryn.x_len]; omega
  rw [this]

private lemma aAt_revA_eq {n : Nat} (S : TurynTypeSeq n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    aAt S.doRevA j = aAt S (n + 1 - j) := by
  unfold aAt TurynTypeSeq.doRevA
  have h1 : S.A.reverse.data.getD (j - 1) 0 = S.A.data.getD (n - j) 0 := revA_getD_eq S hj1 hj2
  have h2 : n + 1 - j - 1 = n - j := by omega
  rw [h1, h2]

private lemma aAt_revA_mirror {n : Nat} (S : TurynTypeSeq n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    aAt S.doRevA (n + 1 - j) = aAt S j := by
  have h1 : 1 ≤ n + 1 - j := by omega
  have h2 : n + 1 - j ≤ n := by omega
  rw [aAt_revA_eq S h1 h2]
  congr 1; omega

private lemma bAt_doRevA_eq {n : Nat} (S : TurynTypeSeq n) (j : Nat) :
    bAt S.doRevA j = bAt S j := by
  unfold bAt TurynTypeSeq.doRevA PmSeq.reverse; rfl

private lemma cAt_doRevA_eq {n : Nat} (S : TurynTypeSeq n) (j : Nat) :
    cAt S.doRevA j = cAt S j := by
  unfold cAt TurynTypeSeq.doRevA PmSeq.reverse; rfl

private lemma dAt_doRevA_eq {n : Nat} (S : TurynTypeSeq n) (j : Nat) :
    dAt S.doRevA j = dAt S j := by
  unfold dAt TurynTypeSeq.doRevA PmSeq.reverse; rfl

private lemma canonical1_doRevA {n : Nat} (hn : 2 ≤ n) (S : TurynTypeSeq n)
    (h1 : Canonical1 n S) : Canonical1 n S.doRevA := by
  unfold Canonical1 at *
  obtain ⟨ha1, han, hb1, hbn, hc1, hd1⟩ := h1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [aAt_revA_eq S (by omega) (by omega)]
    rw [show n + 1 - 1 = n from by omega]
    exact han
  · rw [aAt_revA_eq S (by omega) (by omega)]
    rw [show n + 1 - n = 1 from by omega]
    exact ha1
  · rw [bAt_doRevA_eq]; exact hb1
  · rw [bAt_doRevA_eq]; exact hbn
  · rw [cAt_doRevA_eq]; exact hc1
  · rw [dAt_doRevA_eq]; exact hd1

private lemma aAt_pm_A {n : Nat} (S : TurynTypeSeq n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    aAt S j = 1 ∨ aAt S j = -1 := by
  unfold aAt
  exact pm_entry_of_getD S.isTuryn.x_pm (by rw [S.isTuryn.x_len]; omega)

/-- Step 2: enforce condition (2) by optional reversal of `A`. -/
theorem step2_condition2
    (n : Nat) (hn : 2 ≤ n) (S : TurynTypeSeq n)
    (h1 : Canonical1 n S) :
    ∃ S2 : TurynTypeSeq n, Equivalent n S S2 ∧ Canonical1 n S2 ∧ Canonical2 n S2 := by
      -- Either S already satisfies Canonical2, or there is a first asymmetric index with aAt = -1.
      by_contra h_neg
      -- Extract a witness: the first index i where A is asymmetric and aAt S i = -1.
      obtain ⟨i, hi_lb, hi_ub, hi_sym, hi_neq, hi_val⟩ :
          ∃ i, 1 ≤ i ∧ i ≤ n ∧
            (∀ j, 1 ≤ j → j < i → aAt S j = aAt S (n + 1 - j)) ∧
            aAt S i ≠ aAt S (n + 1 - i) ∧ aAt S i = -1 := by
        -- If no such i exists, then S itself satisfies Canonical2.
        by_contra h_no_witness
        push_neg at h_no_witness
        exact h_neg ⟨S, Relation.ReflTransGen.refl, h1, fun j hj1 hj2 hj3 hj4 =>
          (aAt_pm_A S hj1 hj2).resolve_right (h_no_witness j hj1 hj2 hj3 hj4)⟩
      -- We claim S.doRevA satisfies Canonical1 and Canonical2.
      exact h_neg ⟨S.doRevA, Relation.ReflTransGen.single (Elementary.revA S),
        canonical1_doRevA hn S h1, fun j hj1 hj2 hj3 hj4 => by
          -- We need: aAt S.doRevA j = 1.
          -- aAt S.doRevA j = aAt S (n + 1 - j) by reversal.
          have h_fwd : aAt S.doRevA j = aAt S (n + 1 - j) := aAt_revA_eq S hj1 hj2
          -- aAt S.doRevA (n + 1 - j) = aAt S j by mirror reversal.
          have h_bwd : aAt S.doRevA (n + 1 - j) = aAt S j := aAt_revA_mirror S hj1 hj2
          -- Case split: j < i, j = i, or j > i.
          rcases lt_trichotomy j i with hjlt | hjeq | hjgt
          · -- j < i: all indices before i are symmetric in S, so aAt S j = aAt S (n+1-j).
            have hsym : aAt S j = aAt S (n + 1 - j) := hi_sym j hj1 hjlt
            -- But aAt S.doRevA j ≠ aAt S.doRevA (n+1-j) by hj4, contradiction.
            rw [h_fwd, h_bwd] at hj4
            exact absurd hsym.symm hj4
          · -- j = i: aAt S.doRevA i = aAt S (n+1-i).
            -- We know aAt S i = -1, so aAt S (n+1-i) must be 1 (since they differ and are ±1).
            subst hjeq
            rw [h_fwd]
            have h_mirror_pm := aAt_pm_A S (show 1 ≤ n + 1 - j from by omega) (show n + 1 - j ≤ n from by omega)
            rcases h_mirror_pm with h_one | h_neg1
            · exact h_one
            · exact absurd (show aAt S j = aAt S (n + 1 - j) by rw [hi_val, h_neg1]) hi_neq
          · -- j > i: We show the predecessors-symmetric hypothesis hj3 fails for i, contradiction.
            -- hj3 says all k < j are symmetric in S.doRevA.
            have h_sym_i : aAt S.doRevA i = aAt S.doRevA (n + 1 - i) := hj3 i hi_lb hjgt
            -- Rewrite using reversal accessors.
            rw [aAt_revA_eq S hi_lb hi_ub, aAt_revA_mirror S hi_lb hi_ub] at h_sym_i
            -- So aAt S (n+1-i) = aAt S i, contradicting hi_neq.
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
After reversing D (length n-1) in a TurynTypeSeq, the 1-indexed accessor
satisfies dAt(j) = old dAt(n-j) for 1 ≤ j ≤ n-1.
-/
lemma dAt_doRevD {n : Nat} (S : TurynTypeSeq n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n - 1) :
    dAt S.doRevD j = dAt S (n - j) := by
      convert revD_getD _ using 2;
      · rw [ S.isTuryn.w_len ];
        rw [ show n - 1 - 1 - ( j - 1 ) = n - j - 1 by omega ];
        rfl;
      · convert Nat.lt_of_lt_of_le ( Nat.sub_lt hj1 zero_lt_one ) hj2 using 1;
        exact S.isTuryn.w_len

/-
After reversing and negating D, the 1-indexed accessor
satisfies dAt(j) = -(old dAt(n-j)) for 1 ≤ j ≤ n-1.
-/
lemma dAt_doNegRevD {n : Nat} (S : TurynTypeSeq n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n - 1) :
    dAt (TurynTypeSeq.doNegD S.doRevD) j = -(dAt S (n - j)) := by
      have h_negD : dAt (TurynTypeSeq.doNegD (TurynTypeSeq.doRevD S)) j = -(dAt (TurynTypeSeq.doRevD S) j) := by
        convert negSeq_getD _ _ using 1;
      rw [ h_negD, dAt_doRevD S hj1 hj2 ]

/-! ### Reversal accessor lemmas -/

lemma aAt_doRevA_at {n : Nat} (S : TurynTypeSeq n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    aAt S.doRevA j = aAt S (n + 1 - j) := by
  unfold aAt TurynTypeSeq.doRevA PmSeq.reverse
  simp only
  convert revD_getD (D := S.A.data) _ using 2
  · rw [S.isTuryn.x_len]; omega
  · convert Nat.lt_of_lt_of_le (Nat.sub_lt hj1 zero_lt_one) hj2 using 1
    exact S.isTuryn.x_len

lemma aAt_doRevA_mirror {n : Nat} (S : TurynTypeSeq n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    aAt S.doRevA (n + 1 - j) = aAt S j := by
  have h1 : 1 ≤ n + 1 - j := by omega
  have h2 : n + 1 - j ≤ n := by omega
  rw [aAt_doRevA_at S h1 h2]; congr 1; omega

lemma bAt_doRevB_at {n : Nat} (S : TurynTypeSeq n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    bAt S.doRevB j = bAt S (n + 1 - j) := by
  unfold bAt TurynTypeSeq.doRevB PmSeq.reverse
  simp only
  convert revD_getD (D := S.B.data) _ using 2
  · rw [S.isTuryn.y_len]; omega
  · convert Nat.lt_of_lt_of_le (Nat.sub_lt hj1 zero_lt_one) hj2 using 1
    exact S.isTuryn.y_len

lemma bAt_doRevB_mirror {n : Nat} (S : TurynTypeSeq n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    bAt S.doRevB (n + 1 - j) = bAt S j := by
  have h1 : 1 ≤ n + 1 - j := by omega
  have h2 : n + 1 - j ≤ n := by omega
  rw [bAt_doRevB_at S h1 h2]; congr 1; omega

lemma cAt_doRevC_at {n : Nat} (S : TurynTypeSeq n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    cAt S.doRevC j = cAt S (n + 1 - j) := by
  unfold cAt TurynTypeSeq.doRevC PmSeq.reverse
  simp only
  convert revD_getD (D := S.C.data) _ using 2
  · rw [S.isTuryn.z_len]; omega
  · convert Nat.lt_of_lt_of_le (Nat.sub_lt hj1 zero_lt_one) hj2 using 1
    exact S.isTuryn.z_len

lemma cAt_doRevC_mirror {n : Nat} (S : TurynTypeSeq n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    cAt S.doRevC (n + 1 - j) = cAt S j := by
  have h1 : 1 ≤ n + 1 - j := by omega
  have h2 : n + 1 - j ≤ n := by omega
  rw [cAt_doRevC_at S h1 h2]; congr 1; omega

lemma dAt_doRevD_mirror {n : Nat} (S : TurynTypeSeq n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n - 1) :
    dAt S.doRevD (n - j) = dAt S j := by
  have h1 : 1 ≤ n - j := by omega
  have h2 : n - j ≤ n - 1 := by omega
  rw [dAt_doRevD S h1 h2]; congr 1; omega

/-! ### doRevB preserves other accessors -/

private lemma aAt_doRevB {n : Nat} (S : TurynTypeSeq n) (i : Nat) :
    aAt S.doRevB i = aAt S i := rfl

private lemma cAt_doRevB {n : Nat} (S : TurynTypeSeq n) (i : Nat) :
    cAt S.doRevB i = cAt S i := rfl

private lemma dAt_doRevB {n : Nat} (S : TurynTypeSeq n) (i : Nat) :
    dAt S.doRevB i = dAt S i := rfl

/-- Step 3: enforce condition (3) by optional reversal of `B`. -/
theorem step3_condition3
    (n : Nat) (hn : 2 ≤ n) (S : TurynTypeSeq n)
    (h12 : Canonical1 n S ∧ Canonical2 n S) :
    ∃ S3 : TurynTypeSeq n,
      Equivalent n S S3 ∧ Canonical1 n S3 ∧ Canonical2 n S3 ∧ Canonical3 n S3 := by
  -- Decide whether B already satisfies Canonical3 or needs reversal.
  by_cases hB : ∃ i, 1 ≤ i ∧ i ≤ n ∧
      (∀ j, 1 ≤ j → j < i → bAt S j = bAt S (n + 1 - j)) ∧
      bAt S i ≠ bAt S (n + 1 - i) ∧ bAt S i = -1
  -- Case 1: there exists a first asymmetric index i with bAt S i = -1; reverse B.
  · rcases hB with ⟨i, hi1, hi2, hsym, hasym, hval⟩
    refine ⟨S.doRevB, ?_, ?_, ?_, ?_⟩
    -- (a) Equivalence: single elementary step.
    · exact Relation.ReflTransGen.single (Elementary.revB S)
    -- (b) Canonical1 is preserved.
    · have hc1 := h12.1
      unfold Canonical1 at hc1 ⊢
      rcases hc1 with ⟨ha1, han, hb1, hbn, hc1v, hd1⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      -- aAt is unchanged by doRevB
      · rw [aAt_doRevB]; exact ha1
      · rw [aAt_doRevB]; exact han
      -- bAt endpoints swap under reversal
      · rw [bAt_doRevB_at S (by omega : 1 ≤ 1) (by omega : 1 ≤ n)]
        have : n + 1 - 1 = n := by omega
        rw [this]; exact hbn
      · rw [bAt_doRevB_at S (by omega : 1 ≤ n) le_rfl]
        have : n + 1 - n = 1 := by omega
        rw [this]; exact hb1
      -- cAt and dAt are unchanged by doRevB
      · rw [cAt_doRevB]; exact hc1v
      · rw [dAt_doRevB]; exact hd1
    -- (c) Canonical2 is preserved (A is unchanged by doRevB).
    · intro j hj1 hj2 hj3 hj4
      have : aAt S.doRevB j = aAt S j := aAt_doRevB S j
      have : aAt S.doRevB (n + 1 - j) = aAt S (n + 1 - j) := aAt_doRevB S (n + 1 - j)
      have hj3' : ∀ k, 1 ≤ k → k < j → aAt S k = aAt S (n + 1 - k) := by
        intro k hk1 hk2
        have := hj3 k hk1 hk2
        rw [aAt_doRevB, aAt_doRevB] at this
        exact this
      have hj4' : aAt S j ≠ aAt S (n + 1 - j) := by
        rw [← aAt_doRevB S j, ← aAt_doRevB S (n + 1 - j)]
        exact hj4
      rw [aAt_doRevB]
      exact h12.2 j hj1 hj2 hj3' hj4'
    -- (d) Canonical3 holds after reversal.
    · intro j hj1 hj2 hj3 hj4
      -- Translate the symmetry/asymmetry conditions back to S.
      have hrev_j : bAt S.doRevB j = bAt S (n + 1 - j) :=
        bAt_doRevB_at S hj1 hj2
      have hrev_mirror : bAt S.doRevB (n + 1 - j) = bAt S j :=
        bAt_doRevB_mirror S hj1 hj2
      -- All predecessors of j are symmetric in doRevB, hence in S.
      have hsym_S : ∀ k, 1 ≤ k → k < j → bAt S k = bAt S (n + 1 - k) := by
        intro k hk1 hk2
        have hk2n : k ≤ n := le_trans (le_of_lt hk2) hj2
        have := hj3 k hk1 hk2
        rw [bAt_doRevB_at S hk1 hk2n, bAt_doRevB_mirror S hk1 hk2n] at this
        exact this.symm
      -- j is asymmetric in S.
      have hasym_S : bAt S j ≠ bAt S (n + 1 - j) := by
        intro heq
        exact hj4 (by rw [hrev_j, hrev_mirror]; exact heq.symm)
      -- bAt S (n + 1 - j) is ±1.
      have hpm : bAt S (n + 1 - j) = 1 ∨ bAt S (n + 1 - j) = -1 := by
        have hpm_B : AllPmOne S.B.data := S.isTuryn.y_pm
        exact pm_entry_of_getD hpm_B (by rw [S.isTuryn.y_len]; omega)
      -- bAt S j is ±1.
      have hpm_j : bAt S j = 1 ∨ bAt S j = -1 := by
        have hpm_B : AllPmOne S.B.data := S.isTuryn.y_pm
        exact pm_entry_of_getD hpm_B (by rw [S.isTuryn.y_len]; omega)
      -- Since bAt S j ≠ bAt S (n+1-j) and both are ±1, they are opposite.
      -- We need bAt S.doRevB j = bAt S (n+1-j) = 1.
      rw [hrev_j]
      rcases hpm_j with hj_one | hj_neg
      · -- bAt S j = 1. We show this case is impossible.
        -- j must satisfy j ≤ i: if j < i, hsym gives symmetry contradiction;
        -- if j = i, bAt S i = -1 contradicts hj_one; if j > i, i is a predecessor.
        exfalso
        by_cases hjle : j < i
        · exact hasym_S (hsym j hj1 hjle)
        · by_cases hjeq : j = i
          · rw [hjeq] at hj_one; linarith [hval]
          · have hilt : i < j := by omega
            exact hasym (hsym_S i hi1 hilt)
      · -- bAt S j = -1, so bAt S (n+1-j) ≠ -1, hence bAt S (n+1-j) = 1.
        rcases hpm with hm_one | hm_neg
        · exact hm_one
        · exfalso; exact hasym_S (by rw [hj_neg, hm_neg])
  -- Case 2: no first asymmetric index has bAt S i = -1; S already satisfies Canonical3.
  · refine ⟨S, Relation.ReflTransGen.refl, h12.1, h12.2, ?_⟩
    intro i hi1 hi2 hi3 hi4
    -- bAt S i is ±1.
    have hpm : bAt S i = 1 ∨ bAt S i = -1 := by
      exact pm_entry_of_getD S.isTuryn.y_pm (by rw [S.isTuryn.y_len]; omega)
    -- If bAt S i = -1, then hB would be satisfied, contradiction.
    rcases hpm with h_one | h_neg
    · exact h_one
    · exfalso
      exact hB ⟨i, hi1, hi2, hi3, hi4, h_neg⟩

/--
Accessor for `cAt` after `doRevC` then `doNegC` (the `−C*` transform):
`cAt S.doRevC.doNegC j = -(cAt S (n + 1 - j))` for `1 ≤ j ≤ n`.
-/
private lemma cAt_doNegRevC {n : Nat} (S : TurynTypeSeq n)
    {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    cAt S.doRevC.doNegC j = -(cAt S (n + 1 - j)) := by
  unfold cAt TurynTypeSeq.doNegC TurynTypeSeq.doRevC PmSeq.neg PmSeq.reverse
  simp only [negSeq_getD]; congr 1
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]; congr 1
  rw [List.getElem?_reverse (by rw [S.isTuryn.z_len]; omega)]
  congr 1; rw [S.isTuryn.z_len]; omega

/-- Step 4: enforce condition (4) by optional `−C*`. -/
theorem step4_condition4
    (n : Nat) (hn : 2 ≤ n) (S : TurynTypeSeq n)
    (h123 : Canonical1 n S ∧ Canonical2 n S ∧ Canonical3 n S) :
    ∃ S4 : TurynTypeSeq n,
      Equivalent n S S4 ∧ Canonical1 n S4 ∧ Canonical2 n S4 ∧
      Canonical3 n S4 ∧ Canonical4 n S4 := by
  by_cases h_exists : ∃ i, 1 ≤ i ∧ i ≤ n ∧
      (∀ j, 1 ≤ j → j < i → cAt S j ≠ cAt S (n + 1 - j)) ∧
      cAt S i = cAt S (n + 1 - i) ∧ cAt S i = -1
  · -- Positive case: apply the −C* transform (reverse C, then negate C)
    obtain ⟨i, hi1, hi2, hi3, hi4, hi5⟩ := h_exists
    refine ⟨S.doRevC.doNegC, ?_, ?_, h123.2.1, h123.2.2, ?_⟩
    · -- Equivalence: revC followed by negC
      exact (Relation.ReflTransGen.single (Elementary.revC S)).trans
        (Relation.ReflTransGen.single (Elementary.negC S.doRevC))
    · -- Canonical1 is preserved (only cAt S' 1 needs work)
      have hcn : cAt S n = -1 := lemma1_endpoint_constraint n (by omega) S h123.1
      unfold Canonical1 at *
      obtain ⟨ha1, han, hb1, hbn, _, hd1⟩ := h123.1
      refine ⟨ha1, han, hb1, hbn, ?_, hd1⟩
      -- cAt S.doRevC.doNegC 1 = -(cAt S n) = -(-1) = 1
      unfold cAt TurynTypeSeq.doNegC TurynTypeSeq.doRevC PmSeq.neg PmSeq.reverse
      simp only [negSeq_getD]
      rw [List.getD_eq_getElem?_getD]
      rw [List.getElem?_reverse (by rw [S.isTuryn.z_len]; omega)]
      rw [S.isTuryn.z_len]
      unfold cAt at hcn; rw [List.getD_eq_getElem?_getD] at hcn
      have h0 : n - 1 - 0 = n - 1 := by omega
      rw [h0]; linarith
    · -- Canonical4: the first symmetric index of C is now +1
      intro j hj1 hj2 hj3 hj4
      -- Translate the precondition: all j' < j are asymmetric in the original S
      have hj3' : ∀ j', 1 ≤ j' → j' < j → cAt S j' ≠ cAt S (n + 1 - j') := by
        intro j' hj'1 hj'2
        have h := hj3 j' hj'1 hj'2
        rw [cAt_doNegRevC S hj'1 (by omega),
            cAt_doNegRevC S (by omega : 1 ≤ n + 1 - j') (by omega)] at h
        intro heq; apply h
        have : n + 1 - (n + 1 - j') = j' := by omega
        rw [this]; linarith
      -- Translate the equality: j is symmetric in the original S
      have hj4' : cAt S j = cAt S (n + 1 - j) := by
        rw [cAt_doNegRevC S hj1 hj2,
            cAt_doNegRevC S (by omega : 1 ≤ n + 1 - j) (by omega)] at hj4
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
      rw [cAt_doNegRevC S hj1 hj2, ← hi4, hi5]; norm_num
  · -- Negative case: S itself already satisfies Canonical4
    refine ⟨S, Relation.ReflTransGen.refl, h123.1, h123.2.1, h123.2.2, ?_⟩
    intro i hi1 hi2 hi3 hi4
    rcases pm_entry_of_getD S.isTuryn.z_pm
      (show i - 1 < S.C.data.length by rw [S.isTuryn.z_len]; omega) with h | h
    · exact h
    · exfalso; exact h_exists ⟨i, hi1, hi2, hi3, hi4, h⟩
private lemma dAt_doNegRevD_mirror {n : Nat} (S : TurynTypeSeq n) {j : Nat}
    (hj1 : 1 ≤ j) (hj2 : j ≤ n - 1) :
    dAt (TurynTypeSeq.doNegD S.doRevD) (n - j) = -(dAt S j) := by
  have h1 : 1 ≤ n - j := by omega
  have h2 : n - j ≤ n - 1 := by omega
  rw [dAt_doNegRevD S h1 h2]
  have h3 : n - (n - j) = j := by omega
  rw [h3]

private lemma dAt_pm' {n : Nat} (S : TurynTypeSeq n) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ n - 1) :
    dAt S i = 1 ∨ dAt S i = -1 :=
  pm_entry_of_getD S.isTuryn.w_pm (by rw [S.isTuryn.w_len]; omega)

private lemma dAt_doRevD_n1 {n : Nat} (S : TurynTypeSeq n) (hn : 2 ≤ n) :
    dAt S.doRevD (n - 1) = dAt S 1 := by
  rw [dAt_doRevD S (show 1 ≤ n - 1 from by omega) (show n - 1 ≤ n - 1 from le_refl _)]
  congr 1; omega

private lemma dAt_doNegRevD_n1 {n : Nat} (S : TurynTypeSeq n) (hn : 2 ≤ n) :
    dAt (TurynTypeSeq.doNegD S.doRevD) (n - 1) = -(dAt S 1) := by
  rw [dAt_doNegRevD S (show 1 ≤ n - 1 from by omega) (show n - 1 ≤ n - 1 from le_refl _)]
  have h : n - (n - 1) = 1 := by omega
  rw [h]

/-- In the doRevD case, the product `dAt S' k * dAt S' (n - k)` equals
    the original product `dAt S k * dAt S (n - k)` by commutativity. -/
private lemma doRevD_product_eq {n : Nat} (S : TurynTypeSeq n) {k : Nat}
    (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1) :
    dAt S.doRevD k * dAt S.doRevD (n - k) = dAt S k * dAt S (n - k) := by
  rw [dAt_doRevD S hk1 hk2, dAt_doRevD_mirror S hk1 hk2]
  ring

/-- In the doNegRevD case, the product `dAt S5 k * dAt S5 (n - k)` equals
    the original product `dAt S k * dAt S (n - k)`. -/
private lemma doNegRevD_product_eq {n : Nat} (S : TurynTypeSeq n) {k : Nat}
    (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1) :
    dAt (TurynTypeSeq.doNegD S.doRevD) k *
      dAt (TurynTypeSeq.doNegD S.doRevD) (n - k) =
    dAt S k * dAt S (n - k) := by
  rw [dAt_doNegRevD S hk1 hk2, dAt_doNegRevD_mirror S hk1 hk2]
  ring

/-- Step 5: enforce condition (5) by optional `D*` or `−D*`. -/
theorem step5_condition5
    (n : Nat) (hn : 2 ≤ n) (S : TurynTypeSeq n)
    (h1234 : Canonical1 n S ∧ Canonical2 n S ∧ Canonical3 n S ∧ Canonical4 n S) :
    ∃ S5 : TurynTypeSeq n,
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
    -- Obtain dAt S 1 = 1 from Canonical1.
    have hdS1 : dAt S 1 = 1 := h1234.1.2.2.2.2.2
    -- Case split on dAt S (n - 1).
    by_cases h_case : dAt S (n - 1) = 1
    · /-  Case dAt S (n - 1) = 1: use S.doRevD as the witness.  -/
      refine ⟨S.doRevD, ?_, ?_, ?_, ?_, ?_, ?_⟩
      -- Equivalence
      · exact Relation.ReflTransGen.single (Elementary.revD S)
      -- Canonical1: only dAt changes; dAt S.doRevD 1 = dAt S (n - 1) = 1
      · exact ⟨h1234.1.1, h1234.1.2.1, h1234.1.2.2.1, h1234.1.2.2.2.1, h1234.1.2.2.2.2.1,
               by rw [dAt_doRevD S (by omega : 1 ≤ 1) (by omega : 1 ≤ n - 1)]; exact h_case⟩
      -- Canonical2 (A unchanged)
      · exact h1234.2.1
      -- Canonical3 (B unchanged)
      · exact h1234.2.2.1
      -- Canonical4 (C unchanged)
      · exact h1234.2.2.2
      -- Canonical5 for S.doRevD
      · intro j hj1 hj2 hj3 hj4
        -- Rewrite product and reference value
        rw [doRevD_product_eq S hj1 hj2, dAt_doRevD_n1 S hn, hdS1] at hj4
        -- hj4 : dAt S j * dAt S (n - j) ≠ 1
        rw [dAt_doRevD S hj1 hj2]
        -- Goal: dAt S (n - j) = 1
        -- Three sub-cases: j < i, j = i, j > i.
        by_cases hji_lt : j < i
        · -- j < i: the original hi3 says the product equals dAt S (n - 1) = 1.
          have := hi3 j hj1 hji_lt
          rw [h_case] at this
          exact absurd this hj4
        · by_cases hji_eq : j = i
          · -- j = i: dAt S i = −1 (since ≠ 1 and ±1).
            subst hji_eq
            have hdi_neg : dAt S j = -1 := by
              rcases dAt_pm' S hj1 hj2 with h | h
              · exact absurd h hi5
              · exact h
            -- dAt S (n − j) must be 1 (otherwise product = (−1)(−1) = 1, contradiction).
            rcases dAt_pm' S (show 1 ≤ n - j from by omega) (show n - j ≤ n - 1 from by omega)
              with h | h
            · exact h
            · exfalso; apply hj4; rw [hdi_neg, h]; norm_num
          · -- j > i: hj3 at k = i contradicts hi4.
            have hji_gt : i < j := by omega
            have hk_eq := hj3 i hi1 hji_gt
            rw [doRevD_product_eq S hi1 hi2, dAt_doRevD_n1 S hn, hdS1] at hk_eq
            -- hk_eq : dAt S i * dAt S (n - i) = 1
            rw [h_case] at hi4
            exact absurd hk_eq hi4
    · /- Case dAt S (n - 1) = −1: use doNegD (doRevD S) as the witness. -/
      have h_neg : dAt S (n - 1) = -1 := by
        rcases dAt_pm' S (show 1 ≤ n - 1 from by omega) (show n - 1 ≤ n - 1 from le_refl _)
          with h | h
        · exact absurd h h_case
        · exact h
      set S5 := TurynTypeSeq.doNegD S.doRevD with hS5_def
      refine ⟨S5, ?_, ?_, ?_, ?_, ?_, ?_⟩
      -- Equivalence: revD then negD
      · exact Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single (Elementary.revD S))
          (Relation.ReflTransGen.single (Elementary.negD _))
      -- Canonical1: dAt S5 1 = −(dAt S (n − 1)) = −(−1) = 1
      · refine ⟨h1234.1.1, h1234.1.2.1, h1234.1.2.2.1, h1234.1.2.2.2.1, h1234.1.2.2.2.2.1, ?_⟩
        rw [dAt_doNegRevD S (by omega : 1 ≤ 1) (by omega : 1 ≤ n - 1)]
        rw [h_neg]; norm_num
      -- Canonical2 (A unchanged)
      · exact h1234.2.1
      -- Canonical3 (B unchanged)
      · exact h1234.2.2.1
      -- Canonical4 (C unchanged)
      · exact h1234.2.2.2
      -- Canonical5 for S5 = doNegD (doRevD S)
      · intro j hj1 hj2 hj3 hj4
        -- Rewrite product and reference value
        rw [doNegRevD_product_eq S hj1 hj2, dAt_doNegRevD_n1 S hn, hdS1] at hj4
        -- hj4 : dAt S j * dAt S (n - j) ≠ -(1) = −1
        have hj4' : dAt S j * dAt S (n - j) ≠ -1 := by norm_num at hj4 ⊢; exact hj4
        rw [dAt_doNegRevD S hj1 hj2]
        -- Goal: -(dAt S (n - j)) = 1, i.e., dAt S (n - j) = −1
        -- Three sub-cases: j < i, j = i, j > i.
        by_cases hji_lt : j < i
        · -- j < i: hi3 says product = dAt S (n − 1) = −1, contradiction.
          have := hi3 j hj1 hji_lt
          rw [h_neg] at this
          exact absurd this hj4'
        · by_cases hji_eq : j = i
          · -- j = i: dAt S i = −1, so dAt S (n − i) = −1, and −(−1) = 1.
            subst hji_eq
            have hdi_neg : dAt S j = -1 := by
              rcases dAt_pm' S hj1 hj2 with h | h
              · exact absurd h hi5
              · exact h
            rcases dAt_pm' S (show 1 ≤ n - j from by omega) (show n - j ≤ n - 1 from by omega)
              with h | h
            · -- dAt S (n - j) = 1: product = (−1)(1) = −1, contradicts hj4'
              exfalso; apply hj4'; rw [hdi_neg, h]; norm_num
            · -- dAt S (n - j) = −1: −(−1) = 1 ✓
              rw [h]; norm_num
          · -- j > i: hj3 at k = i contradicts hi4.
            have hji_gt : i < j := by omega
            have hk_eq := hj3 i hi1 hji_gt
            rw [doNegRevD_product_eq S hi1 hi2, dAt_doNegRevD_n1 S hn, hdS1] at hk_eq
            rw [h_neg] at hi4
            have hk_eq' : dAt S i * dAt S (n - i) = -1 := by linarith
            exact absurd hk_eq' hi4

/-! ### Helper lemmas for step 6 -/

private lemma doSwap_aAt {n : Nat} (S : TurynTypeSeq n) (i : Nat) :
    aAt S.doSwap i = bAt S i := by
  unfold aAt bAt TurynTypeSeq.doSwap; rfl

private lemma doSwap_bAt {n : Nat} (S : TurynTypeSeq n) (i : Nat) :
    bAt S.doSwap i = aAt S i := by
  unfold aAt bAt TurynTypeSeq.doSwap; rfl

private lemma doSwap_cAt {n : Nat} (S : TurynTypeSeq n) (i : Nat) :
    cAt S.doSwap i = cAt S i := by
  unfold cAt TurynTypeSeq.doSwap; rfl

private lemma doSwap_dAt {n : Nat} (S : TurynTypeSeq n) (i : Nat) :
    dAt S.doSwap i = dAt S i := by
  unfold dAt TurynTypeSeq.doSwap; rfl

private lemma canonical1_doSwap {n : Nat} {S : TurynTypeSeq n}
    (h1 : Canonical1 n S) : Canonical1 n S.doSwap := by
  unfold Canonical1 at *
  exact ⟨by rw [doSwap_aAt]; exact h1.2.2.1,
         by rw [doSwap_aAt]; exact h1.2.2.2.1,
         by rw [doSwap_bAt]; exact h1.1,
         by rw [doSwap_bAt]; exact h1.2.1,
         by rw [doSwap_cAt]; exact h1.2.2.2.2.1,
         by rw [doSwap_dAt]; exact h1.2.2.2.2.2⟩

private lemma canonical2_doSwap_of_canonical3 {n : Nat} {S : TurynTypeSeq n}
    (h3 : Canonical3 n S) : Canonical2 n S.doSwap := by
  intro i hi₁ hi₂ hi₃ hi₄
  have hi₃' : ∀ j, 1 ≤ j → j < i → bAt S j = bAt S (n + 1 - j) := by
    intro j hj₁ hj₂
    have := hi₃ j hj₁ hj₂
    rw [doSwap_aAt, doSwap_aAt] at this
    exact this
  have hi₄' : bAt S i ≠ bAt S (n + 1 - i) := by
    rw [doSwap_aAt, doSwap_aAt] at hi₄
    exact hi₄
  have := h3 i hi₁ hi₂ hi₃' hi₄'
  rw [doSwap_aAt]
  exact this

private lemma canonical3_doSwap_of_canonical2 {n : Nat} {S : TurynTypeSeq n}
    (h2 : Canonical2 n S) : Canonical3 n S.doSwap := by
  intro i hi₁ hi₂ hi₃ hi₄
  have hi₃' : ∀ j, 1 ≤ j → j < i → aAt S j = aAt S (n + 1 - j) := by
    intro j hj₁ hj₂
    have := hi₃ j hj₁ hj₂
    rw [doSwap_bAt, doSwap_bAt] at this
    exact this
  have hi₄' : aAt S i ≠ aAt S (n + 1 - i) := by
    rw [doSwap_bAt, doSwap_bAt] at hi₄
    exact hi₄
  have := h2 i hi₁ hi₂ hi₃' hi₄'
  rw [doSwap_bAt]
  exact this

private lemma canonical4_doSwap {n : Nat} {S : TurynTypeSeq n}
    (h4 : Canonical4 n S) : Canonical4 n S.doSwap := by
  intro i hi₁ hi₂ hi₃ hi₄
  have hi₃' : ∀ j, 1 ≤ j → j < i → cAt S j ≠ cAt S (n + 1 - j) := by
    intro j hj₁ hj₂
    have := hi₃ j hj₁ hj₂
    rw [doSwap_cAt, doSwap_cAt] at this
    exact this
  have hi₄' : cAt S i = cAt S (n + 1 - i) := by
    rw [doSwap_cAt, doSwap_cAt] at hi₄
    exact hi₄
  have := h4 i hi₁ hi₂ hi₃' hi₄'
  rw [doSwap_cAt]
  exact this

private lemma canonical5_doSwap {n : Nat} {S : TurynTypeSeq n}
    (h5 : Canonical5 n S) : Canonical5 n S.doSwap := by
  intro i hi₁ hi₂ hi₃ hi₄
  have hi₃' : ∀ j, 1 ≤ j → j < i → dAt S j * dAt S (n - j) = dAt S (n - 1) := by
    intro j hj₁ hj₂
    have := hi₃ j hj₁ hj₂
    rw [doSwap_dAt, doSwap_dAt, doSwap_dAt] at this
    exact this
  have hi₄' : dAt S i * dAt S (n - i) ≠ dAt S (n - 1) := by
    rw [doSwap_dAt, doSwap_dAt, doSwap_dAt] at hi₄
    exact hi₄
  have := h5 i hi₁ hi₂ hi₃' hi₄'
  rw [doSwap_dAt]
  exact this

private lemma step6_aAt_pm {n : Nat} (S : TurynTypeSeq n) (i : Nat) (hi : i - 1 < n) :
    aAt S i = 1 ∨ aAt S i = -1 := by
  exact pm_entry_of_getD S.isTuryn.x_pm (by rw [S.isTuryn.x_len]; exact hi)

private lemma step6_bAt_pm {n : Nat} (S : TurynTypeSeq n) (i : Nat) (hi : i - 1 < n) :
    bAt S i = 1 ∨ bAt S i = -1 := by
  exact pm_entry_of_getD S.isTuryn.y_pm (by rw [S.isTuryn.y_len]; exact hi)

private lemma step6_cAt_pm {n : Nat} (S : TurynTypeSeq n) (i : Nat) (hi : i - 1 < n) :
    cAt S i = 1 ∨ cAt S i = -1 := by
  exact pm_entry_of_getD S.isTuryn.z_pm (by rw [S.isTuryn.z_len]; exact hi)

private lemma step6_dAt_pm {n : Nat} (S : TurynTypeSeq n) (i : Nat) (hi : i - 1 < n - 1) :
    dAt S i = 1 ∨ dAt S i = -1 := by
  exact pm_entry_of_getD S.isTuryn.w_pm (by rw [S.isTuryn.w_len]; exact hi)

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
    (n : Nat) (hn3 : 3 ≤ n) (S : TurynTypeSeq n)
    (h1 : Canonical1 n S) :
    aAt S (n - 1) + aAt S 2 + (bAt S (n - 1) + bAt S 2) +
    2 * (cAt S (n - 1) + cAt S 2 * cAt S n) +
    2 * dAt S (n - 1) = 0 := by
  -- Get vanishing at lag n-2
  have hv := S.isTuryn.vanishing (n - 2) (by omega) (by omega)
  unfold combinedAutocorr at hv
  -- Expand each aperiodicAutocorr
  rw [autocorr_two_terms S.A.data (n - 2) (by rw [S.isTuryn.x_len]; omega),
      autocorr_two_terms S.B.data (n - 2) (by rw [S.isTuryn.y_len]; omega),
      autocorr_two_terms S.C.data (n - 2) (by rw [S.isTuryn.z_len]; omega),
      autocorr_one_term S.D.data (n - 2) (by rw [S.isTuryn.w_len]; omega)] at hv
  -- Express aAt/bAt/cAt/dAt as getD
  have eqa_n1 : aAt S (n - 1) = S.A.data.getD (n - 2) 0 := by
    show S.A.data.getD (n - 1 - 1) 0 = S.A.data.getD (n - 2) 0; congr 1
  have eqa_2 : aAt S 2 = S.A.data.getD 1 0 := rfl
  have eqb_n1 : bAt S (n - 1) = S.B.data.getD (n - 2) 0 := by
    show S.B.data.getD (n - 1 - 1) 0 = S.B.data.getD (n - 2) 0; congr 1
  have eqb_2 : bAt S 2 = S.B.data.getD 1 0 := rfl
  have eqc_n1 : cAt S (n - 1) = S.C.data.getD (n - 2) 0 := by
    show S.C.data.getD (n - 1 - 1) 0 = S.C.data.getD (n - 2) 0; congr 1
  have eqc_2 : cAt S 2 = S.C.data.getD 1 0 := rfl
  have eqc_n : cAt S n = S.C.data.getD (n - 1) 0 := rfl
  have eqd_n1 : dAt S (n - 1) = S.D.data.getD (n - 2) 0 := by
    show S.D.data.getD (n - 1 - 1) 0 = S.D.data.getD (n - 2) 0; congr 1
  -- Rewrite the goal to use getD
  rw [eqa_n1, eqa_2, eqb_n1, eqb_2, eqc_n1, eqc_2, eqc_n, eqd_n1]
  -- Get Canonical1 in getD form
  have h_a0 : S.A.data.getD 0 0 = 1 := by
    have := h1.1; unfold aAt at this; exact this
  have h_an1 : S.A.data.getD (n - 1) 0 = 1 := by
    have := h1.2.1; unfold aAt at this; exact this
  have h_b0 : S.B.data.getD 0 0 = 1 := by
    have := h1.2.2.1; unfold bAt at this; exact this
  have h_bn1 : S.B.data.getD (n - 1) 0 = 1 := by
    have := h1.2.2.2.1; unfold bAt at this; exact this
  have h_c0 : S.C.data.getD 0 0 = 1 := by
    have := h1.2.2.2.2.1; unfold cAt at this; exact this
  have h_d0 : S.D.data.getD 0 0 = 1 := by
    have := h1.2.2.2.2.2; unfold dAt at this; exact this
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
    (n : Nat) (hn_even : n % 2 = 0) (hn : 2 ≤ n) (S : TurynTypeSeq n)
    (h1 : Canonical1 n S) (h_eq : aAt S 2 = bAt S 2) :
    n ≤ 2 ∨
    (aAt S (n - 1) = 1 ∧ bAt S (n - 1) = -1) ∨
    (aAt S (n - 1) = -1 ∧ bAt S (n - 1) = 1) := by
  by_cases hn3 : 3 ≤ n;
  · have h_sum : aAt S (n - 1) + bAt S (n - 1) + 2 * aAt S 2 + 2 * cAt S (n - 1) + 2 * (cAt S 2 * cAt S n) + 2 * dAt S (n - 1) = 0 := by
      convert step6_autocorr_lag_n_sub_2 n hn3 S h1 using 1 ; rw [ h_eq ] ; ring!;
    have h_cases : aAt S (n - 1) = 1 ∨ aAt S (n - 1) = -1 := by
      exact step6_aAt_pm S ( n - 1 ) ( by omega )
    have h_cases' : bAt S (n - 1) = 1 ∨ bAt S (n - 1) = -1 := by
      exact step6_bAt_pm S ( n - 1 ) ( by omega )
    have h_cases'' : aAt S 2 = 1 ∨ aAt S 2 = -1 := by
      exact step6_aAt_pm S 2 ( by omega )
    have h_cases''' : cAt S (n - 1) = 1 ∨ cAt S (n - 1) = -1 := by
      apply step6_cAt_pm; omega;
    have h_cases'''' : cAt S 2 * cAt S n = 1 ∨ cAt S 2 * cAt S n = -1 := by
      have h_cases'''' : cAt S 2 = 1 ∨ cAt S 2 = -1 := by
        apply step6_cAt_pm; omega;
      have h_cases''''' : cAt S n = 1 ∨ cAt S n = -1 := by
        apply step6_cAt_pm; omega;
      rcases h_cases'''' with h|h <;> rcases h_cases''''' with j|j <;> norm_num [ h, j ]
    have h_cases''''' : dAt S (n - 1) = 1 ∨ dAt S (n - 1) = -1 := by
      apply step6_dAt_pm; omega;
    have hab0 := step6_sum_forces_zero
      (aAt S (n - 1)) (bAt S (n - 1)) (aAt S 2) (cAt S (n - 1))
      (dAt S (n - 1)) (cAt S 2 * cAt S n)
      h_cases h_cases' h_cases'' h_cases''' h_cases'''' h_cases''''' h_sum
    rcases h_cases with ha1 | ha_neg1
    · have hb : bAt S (n - 1) = -1 := by linarith
      exact Or.inr (Or.inl ⟨ha1, hb⟩)
    · have hb : bAt S (n - 1) = 1 := by linarith
      exact Or.inr (Or.inr ⟨ha_neg1, hb⟩)
  · exact Or.inl (by omega)

/-- Step 6: enforce condition (6) using optional swap. -/
theorem step6_condition6
    (n : Nat) (hn_even : n % 2 = 0) (hn : 2 ≤ n) (S : TurynTypeSeq n)
    (h12345 : Canonical1 n S ∧ Canonical2 n S ∧ Canonical3 n S ∧
              Canonical4 n S ∧ Canonical5 n S) :
    ∃ S6 : TurynTypeSeq n,
      Equivalent n S S6 ∧
      Canonical1 n S6 ∧ Canonical2 n S6 ∧ Canonical3 n S6 ∧
      Canonical4 n S6 ∧ Canonical5 n S6 ∧ Canonical6 n S6 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h12345
  -- Case split: aAt S 2 ≠ bAt S 2 vs aAt S 2 = bAt S 2
  by_cases h_neq : aAt S 2 ≠ bAt S 2
  · -- Sub-case: aAt S 2 = 1
    rcases step6_aAt_pm S 2 (by omega) with h_a2_1 | h_a2_neg1
    · -- aAt S 2 = 1: S itself works
      exact ⟨S, Relation.ReflTransGen.refl, h1, h2, h3, h4, h5,
             Or.inr (Or.inl ⟨h_neq, h_a2_1⟩)⟩
    · -- aAt S 2 = -1: then bAt S 2 = 1 (since they differ and are ±1)
      have h_b2 : bAt S 2 = 1 := by
        rcases step6_bAt_pm S 2 (by omega) with h | h
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
      exact ⟨by rw [doSwap_aAt, doSwap_bAt]; exact fun h => h_neq h.symm,
             by rw [doSwap_aAt]; exact h_b2⟩
  · -- aAt S 2 = bAt S 2
    push_neg at h_neq
    -- Use step6_opposite_signs to get sign information at position n-1
    rcases step6_opposite_signs n hn_even hn S h1 h_neq with h_le2 | ⟨ha_pos, hb_neg⟩ | ⟨ha_neg, hb_pos⟩
    · -- n ≤ 2: Canonical6 is trivially satisfied
      exact ⟨S, Relation.ReflTransGen.refl, h1, h2, h3, h4, h5, Or.inl h_le2⟩
    · -- aAt S (n-1) = 1, bAt S (n-1) = -1: S works directly
      exact ⟨S, Relation.ReflTransGen.refl, h1, h2, h3, h4, h5,
             Or.inr (Or.inr ⟨h_neq, ha_pos, hb_neg⟩)⟩
    · -- aAt S (n-1) = -1, bAt S (n-1) = 1: use S.doSwap
      refine ⟨S.doSwap, Relation.ReflTransGen.single (Elementary.swap S),
              canonical1_doSwap h1,
              canonical2_doSwap_of_canonical3 h3,
              canonical3_doSwap_of_canonical2 h2,
              canonical4_doSwap h4,
              canonical5_doSwap h5,
              ?_⟩
      unfold Canonical6
      right; right
      exact ⟨by rw [doSwap_aAt, doSwap_bAt]; exact h_neq.symm,
             by rw [doSwap_aAt]; exact hb_pos,
             by rw [doSwap_bAt]; exact ha_neg⟩

/-- Every equivalence class of Turyn-type sequences has a canonical representative.

This is the main theorem of the normalization theory from
Best–Đoković–Kharaghani–Ramp (arXiv:1206.4107, 2013). -/
theorem canonical_representative_exists
    (n : Nat) (hn_even : n % 2 = 0) (hn : 2 ≤ n) (S : TurynTypeSeq n) :
    ∃ T : TurynTypeSeq n, Equivalent n S T ∧ Canonical n T := by
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
