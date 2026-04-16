import Turyn.TurynType
import Mathlib

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

/-- Negation of a ±1 sequence. -/
def Turyn.negSeq (X : PmSeq) : PmSeq := X.map (fun x => -x)

/-- Alternation of a sequence: entry at 0-indexed position `i` gets factor `(-1)^i`. -/
def Turyn.altSeq (X : PmSeq) : PmSeq :=
  (List.range X.length).map (fun i => ((if i % 2 = 0 then 1 else -1) : Int) * X.getD i 0)

/-! ### Length preservation -/

@[simp] lemma Turyn.negSeq_length (X : PmSeq) : (Turyn.negSeq X).length = X.length := by
  simp [Turyn.negSeq]

@[simp] lemma Turyn.altSeq_length (X : PmSeq) : (Turyn.altSeq X).length = X.length := by
  simp [Turyn.altSeq]

/-! ### AllPmOne preservation -/

lemma AllPmOne_neg {X : PmSeq} (h : AllPmOne X) : AllPmOne (Turyn.negSeq X) := by
  intro v hv
  simp only [Turyn.negSeq, List.mem_map] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  rcases h u hu with rfl | rfl <;> simp

lemma AllPmOne_reverse {X : PmSeq} (h : AllPmOne X) : AllPmOne X.reverse := by
  intro v hv; exact h v (List.mem_reverse.mp hv)

lemma AllPmOne_alt {X : PmSeq} (h : AllPmOne X) : AllPmOne (Turyn.altSeq X) := by
  intro x hx; simp_all +decide [ Turyn.altSeq ];
  rcases hx with ⟨ a, ha, rfl ⟩;
  cases h ( X[a]?.getD 0 ) ( by simp [ ha ] ) <;> split_ifs <;> simp_all +decide

/-! ### Autocorrelation preservation -/

/-- Negation preserves aperiodic autocorrelation: `N_{-X}(s) = N_X(s)`. -/
lemma aperiodicAutocorr_neg (a : PmSeq) (s : Nat) :
    aperiodicAutocorr (Turyn.negSeq a) s = aperiodicAutocorr a s := by
      unfold Turyn.negSeq aperiodicAutocorr;
      grind +splitImp

/-- Reversal preserves aperiodic autocorrelation: `N_{X*}(s) = N_X(s)`. -/
lemma aperiodicAutocorr_rev (a : PmSeq) (s : Nat) :
    aperiodicAutocorr a.reverse s = aperiodicAutocorr a s := by
      unfold aperiodicAutocorr;
      split_ifs <;> simp_all +decide [ List.getD_eq_default ];
      rw [ ← Finset.sum_range_reflect ];
      refine' Finset.sum_congr rfl fun i hi => _;
      grind

/-- Alternation scales autocorrelation by `(-1)^s`: `N_{X̂}(s) = (-1)^s · N_X(s)`. -/
lemma aperiodicAutocorr_alt (a : PmSeq) (s : Nat) :
    aperiodicAutocorr (Turyn.altSeq a) s = (-1 : Int) ^ s * aperiodicAutocorr a s := by
      unfold aperiodicAutocorr Turyn.altSeq;
      split_ifs <;> simp_all +decide [ Finset.mul_sum _ _ _ ];
      refine' Finset.sum_congr rfl fun i hi => _;
      by_cases hi' : i < List.length a <;> by_cases hi'' : i + s < List.length a <;> simp_all +decide [ Nat.add_mod, Nat.mod_two_of_bodd ];
      rcases Nat.even_or_odd' i with ⟨ k, rfl | rfl ⟩ <;> rcases Nat.even_or_odd' s with ⟨ l, rfl | rfl ⟩ <;> norm_num [ pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod ]

/-! ### IsTurynTypeProp preservation under each elementary transformation -/

lemma turynProp_negA {n : Nat} {A B C D : PmSeq}
    (h : IsTurynTypeProp n A B C D) : IsTurynTypeProp n (Turyn.negSeq A) B C D where
  x_len := by simp [Turyn.negSeq, h.x_len]
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

lemma turynProp_negB {n : Nat} {A B C D : PmSeq}
    (h : IsTurynTypeProp n A B C D) : IsTurynTypeProp n A (Turyn.negSeq B) C D where
  x_len := h.x_len
  y_len := by simp [Turyn.negSeq, h.y_len]
  z_len := h.z_len
  w_len := h.w_len
  x_pm := h.x_pm
  y_pm := AllPmOne_neg h.y_pm
  z_pm := h.z_pm
  w_pm := h.w_pm
  vanishing := fun s hs1 hs2 => by
    have := h.vanishing s hs1 hs2
    unfold combinedAutocorr at this ⊢; rw [aperiodicAutocorr_neg]; exact this

lemma turynProp_negC {n : Nat} {A B C D : PmSeq}
    (h : IsTurynTypeProp n A B C D) : IsTurynTypeProp n A B (Turyn.negSeq C) D where
  x_len := h.x_len
  y_len := h.y_len
  z_len := by simp [Turyn.negSeq, h.z_len]
  w_len := h.w_len
  x_pm := h.x_pm
  y_pm := h.y_pm
  z_pm := AllPmOne_neg h.z_pm
  w_pm := h.w_pm
  vanishing := fun s hs1 hs2 => by
    have := h.vanishing s hs1 hs2
    unfold combinedAutocorr at this ⊢; rw [aperiodicAutocorr_neg]; exact this

lemma turynProp_negD {n : Nat} {A B C D : PmSeq}
    (h : IsTurynTypeProp n A B C D) : IsTurynTypeProp n A B C (Turyn.negSeq D) where
  x_len := h.x_len
  y_len := h.y_len
  z_len := h.z_len
  w_len := by simp [Turyn.negSeq, h.w_len]
  x_pm := h.x_pm
  y_pm := h.y_pm
  z_pm := h.z_pm
  w_pm := AllPmOne_neg h.w_pm
  vanishing := fun s hs1 hs2 => by
    have := h.vanishing s hs1 hs2
    unfold combinedAutocorr at this ⊢; rw [aperiodicAutocorr_neg]; exact this

lemma turynProp_revA {n : Nat} {A B C D : PmSeq}
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

lemma turynProp_revB {n : Nat} {A B C D : PmSeq}
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

lemma turynProp_revC {n : Nat} {A B C D : PmSeq}
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

lemma turynProp_revD {n : Nat} {A B C D : PmSeq}
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

lemma turynProp_altAll {n : Nat} {A B C D : PmSeq}
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

lemma turynProp_swapAB {n : Nat} {A B C D : PmSeq}
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

/-! ### Turyn-type quadruple -/

/-- A Turyn-type quadruple packaged as a single object, using
propositional validity from `IsTurynTypeProp`. -/
structure TurynTypeSeq (n : Nat) where
  A : PmSeq
  B : PmSeq
  C : PmSeq
  D : PmSeq
  isTuryn : IsTurynTypeProp n A B C D

/-- Entry accessor for `A` (1-indexed). -/
def aAt {n : Nat} (S : TurynTypeSeq n) (i : Nat) : Int := S.A.getD (i - 1) 0
/-- Entry accessor for `B` (1-indexed). -/
def bAt {n : Nat} (S : TurynTypeSeq n) (i : Nat) : Int := S.B.getD (i - 1) 0
/-- Entry accessor for `C` (1-indexed). -/
def cAt {n : Nat} (S : TurynTypeSeq n) (i : Nat) : Int := S.C.getD (i - 1) 0
/-- Entry accessor for `D` (1-indexed). -/
def dAt {n : Nat} (S : TurynTypeSeq n) (i : Nat) : Int := S.D.getD (i - 1) 0

/-! ### TurynTypeSeq transformations -/

def TurynTypeSeq.doNegA {n : Nat} (S : TurynTypeSeq n) : TurynTypeSeq n :=
  ⟨negSeq S.A, S.B, S.C, S.D, turynProp_negA S.isTuryn⟩

def TurynTypeSeq.doNegB {n : Nat} (S : TurynTypeSeq n) : TurynTypeSeq n :=
  ⟨S.A, negSeq S.B, S.C, S.D, turynProp_negB S.isTuryn⟩

def TurynTypeSeq.doNegC {n : Nat} (S : TurynTypeSeq n) : TurynTypeSeq n :=
  ⟨S.A, S.B, negSeq S.C, S.D, turynProp_negC S.isTuryn⟩

def TurynTypeSeq.doNegD {n : Nat} (S : TurynTypeSeq n) : TurynTypeSeq n :=
  ⟨S.A, S.B, S.C, negSeq S.D, turynProp_negD S.isTuryn⟩

def TurynTypeSeq.doRevA {n : Nat} (S : TurynTypeSeq n) : TurynTypeSeq n :=
  ⟨S.A.reverse, S.B, S.C, S.D, turynProp_revA S.isTuryn⟩

def TurynTypeSeq.doRevB {n : Nat} (S : TurynTypeSeq n) : TurynTypeSeq n :=
  ⟨S.A, S.B.reverse, S.C, S.D, turynProp_revB S.isTuryn⟩

def TurynTypeSeq.doRevC {n : Nat} (S : TurynTypeSeq n) : TurynTypeSeq n :=
  ⟨S.A, S.B, S.C.reverse, S.D, turynProp_revC S.isTuryn⟩

def TurynTypeSeq.doRevD {n : Nat} (S : TurynTypeSeq n) : TurynTypeSeq n :=
  ⟨S.A, S.B, S.C, S.D.reverse, turynProp_revD S.isTuryn⟩

def TurynTypeSeq.doAltAll {n : Nat} (S : TurynTypeSeq n) : TurynTypeSeq n :=
  ⟨altSeq S.A, altSeq S.B, altSeq S.C, altSeq S.D, turynProp_altAll S.isTuryn⟩

def TurynTypeSeq.doSwap {n : Nat} (S : TurynTypeSeq n) : TurynTypeSeq n :=
  ⟨S.B, S.A, S.C, S.D, turynProp_swapAB S.isTuryn⟩

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

lemma pm_entry_of_getD {X : PmSeq} (hpm : AllPmOne X) {i : Nat} (hi : i < X.length) :
    X.getD i 0 = 1 ∨ X.getD i 0 = -1 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact hpm X[i] (List.getElem_mem hi)

/-! ### Endpoint constraint from vanishing at s = n-1 -/

lemma aperiodicAutocorr_last {n : Nat} {a : PmSeq} (ha : a.length = n) (hn : 1 < n) :
    aperiodicAutocorr a (n - 1) = a.getD 0 0 * a.getD (n - 1) 0 := by
      unfold aperiodicAutocorr;
      rcases n with ( _ | _ | n ) <;> simp_all +decide [ Finset.sum_range_succ' ]

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
      have := endpoint_relation hn S; simp_all +decide [ Canonical1 ] ;
      linarith

/-! ### Helper lemmas for step proofs -/

/-
negSeq flips the sign at each index.
-/
lemma negSeq_getD (X : PmSeq) (i : Nat) :
    (negSeq X).getD i 0 = -(X.getD i 0) := by
      unfold negSeq;
      grind

/-
altSeq multiplies by (-1)^i at each valid index.
-/
lemma altSeq_getD (X : PmSeq) (i : Nat) (hi : i < X.length) :
    (altSeq X).getD i 0 = (if i % 2 = 0 then 1 else -1) * X.getD i 0 := by
      unfold altSeq; aesop;

/-
altSeq preserves position 0 (factor = 1).
-/
lemma altSeq_getD_zero (X : PmSeq) (hX : 0 < X.length) :
    (altSeq X).getD 0 0 = X.getD 0 0 := by
      unfold altSeq; aesop;

/-
For even length ≥ 2, altSeq at position length-1 has factor -1.
-/
lemma altSeq_getD_last (X : PmSeq) (hn : X.length % 2 = 0) (hX : 2 ≤ X.length) :
    (altSeq X).getD (X.length - 1) 0 = -(X.getD (X.length - 1) 0) := by
      grind +suggestions

/-! ### Step theorems -/

/-- Transitivity of equivalence (closure composition). -/
theorem equivalent_trans
    (n : Nat) {S T U : TurynTypeSeq n} :
    Equivalent n S T → Equivalent n T U → Equivalent n S U :=
  Relation.ReflTransGen.trans

set_option maxHeartbeats 800000 in
/-- Step 1: enforce condition (1) — normalize endpoint signs. -/
theorem step1_condition1
    (n : Nat) (hn_even : n % 2 = 0) (hn : 2 ≤ n) (S : TurynTypeSeq n) :
    ∃ S1 : TurynTypeSeq n, Equivalent n S S1 ∧ Canonical1 n S1 := by
      -- By negating components if necessary, we can ensure that the first elements of A, B, C, and D are all 1.
      have h_neg : ∃ S1 : TurynTypeSeq n, Equivalent n S S1 ∧ (aAt S1 1 = 1 ∧ bAt S1 1 = 1 ∧ cAt S1 1 = 1 ∧ dAt S1 1 = 1) := by
        obtain ⟨S1, hS1⟩ : ∃ S1 : TurynTypeSeq n, Equivalent n S S1 ∧ aAt S1 1 = 1 ∧ bAt S1 1 = 1 ∧ cAt S1 1 = 1 := by
          obtain ⟨S1, hS1⟩ : ∃ S1 : TurynTypeSeq n, Equivalent n S S1 ∧ aAt S1 1 = 1 ∧ bAt S1 1 = 1 := by
            obtain ⟨S1, hS1⟩ : ∃ S1 : TurynTypeSeq n, Equivalent n S S1 ∧ aAt S1 1 = 1 := by
              by_cases h : aAt S 1 = 1;
              · exact ⟨ S, Relation.ReflTransGen.refl, h ⟩;
              · use S.doNegA
                constructor
                · exact Relation.ReflTransGen.single (Elementary.negA S)
                ·
                  have := S.isTuryn.x_pm ( S.A.getD 0 0 ) ; simp_all +decide [ aAt ] ;
                  by_cases h' : 0 < S.A.length <;> simp_all +decide [ TurynTypeSeq.doNegA ];
                  · unfold negSeq; aesop;
                  · have := S.isTuryn.x_len; aesop;
            by_cases h : bAt S1 1 = 1;
            · exact ⟨ S1, hS1.1, hS1.2, h ⟩;
            · use S1.doNegB;
              refine' ⟨ _, _, _ ⟩;
              · exact hS1.1.trans ( Relation.ReflTransGen.single ( Elementary.negB _ ) );
              · unfold aAt at *; aesop;
              · have h_bAt_neg : bAt S1 1 = -1 := by
                  have := S1.isTuryn.y_pm;
                  exact Or.resolve_left ( pm_entry_of_getD this ( show 0 < S1.B.length from by linarith [ S1.isTuryn.y_len ] ) ) h;
                have h_bAt_neg : bAt S1.doNegB 1 = -(bAt S1 1) := by
                  exact negSeq_getD _ _;
                grind;
          by_cases hc : cAt S1 1 = 1;
          · exact ⟨ S1, hS1.1, hS1.2.1, hS1.2.2, hc ⟩;
          · use S1.doNegC;
            refine' ⟨ _, _, _, _ ⟩;
            · exact hS1.1.trans ( Relation.ReflTransGen.single ( Elementary.negC _ ) );
            · unfold aAt TurynTypeSeq.doNegC; aesop;
            · exact hS1.2.2;
            · unfold cAt at *;
              have := S1.isTuryn.x_pm 0; have := S1.isTuryn.y_pm 0; have := S1.isTuryn.z_pm 0; have := S1.isTuryn.w_pm 0; simp_all +decide [ TurynTypeSeq.doNegC ] ;
              cases h : S1.C <;> simp_all +decide [ negSeq ];
              · have := S1.isTuryn.z_len; aesop;
              · have := S1.isTuryn.z_pm; simp_all +decide [ AllPmOne ] ;
        by_cases hd1 : dAt S1 1 = 1;
        · exact ⟨ S1, hS1.1, hS1.2.1, hS1.2.2.1, hS1.2.2.2, hd1 ⟩;
        · refine' ⟨ TurynTypeSeq.doNegD S1, _, _, _, _, _ ⟩ <;> simp_all +decide [ TurynTypeSeq.doNegD ];
          · exact hS1.1.trans ( Relation.ReflTransGen.single ( Elementary.negD _ ) );
          · exact hS1.2.1;
          · exact hS1.2.2.1;
          · exact hS1.2.2.2;
          · -- Since $dAt S1 1 \neq 1$, we have $dAt S1 1 = -1$.
            have hd1_neg : dAt S1 1 = -1 := by
              exact Or.resolve_left ( pm_entry_of_getD ( show AllPmOne S1.D from S1.isTuryn.w_pm ) ( show 0 < S1.D.length from by linarith [ S1.isTuryn.w_len, Nat.sub_add_cancel ( by linarith : 1 ≤ n ) ] ) ) ( by aesop );
            convert congr_arg Neg.neg hd1_neg using 1;
            exact negSeq_getD _ _;
      obtain ⟨ S1, hS1, ha, hb, hc, hd ⟩ := h_neg;
      -- If $aAt n = bAt n = -1$, apply `doAltAll` to flip the signs of the last elements.
      by_cases h_last : aAt S1 n = -1 ∧ bAt S1 n = -1;
      · refine' ⟨ S1.doAltAll, hS1.trans ( Elementary.toEquivalent ( Elementary.altAll S1 ) ), _, _, _, _, _ ⟩ <;> simp_all +decide [ TurynTypeSeq.doAltAll ];
        · convert ha using 1;
          exact altSeq_getD_zero _ ( by linarith [ S1.isTuryn.x_len ] );
        · grind +locals;
        · convert hb using 1;
          exact altSeq_getD_zero _ ( by linarith [ S1.isTuryn.x_len, S1.isTuryn.y_len, S1.isTuryn.z_len, S1.isTuryn.w_len ] );
        · unfold bAt at *;
          unfold altSeq; simp +decide [ *, Nat.even_iff ] ;
          grind +splitImp;
        · simp_all +decide [ aAt, bAt, cAt, dAt, altSeq ];
          grind;
      · have h_last : aAt S1 n = 1 ∧ bAt S1 n = 1 := by
          have h_last : aAt S1 n * aAt S1 1 + bAt S1 n * bAt S1 1 + 2 * (cAt S1 n * cAt S1 1) = 0 := by
            convert endpoint_relation ( show 1 < n from hn ) S1 using 1 ; ring;
          have h_last : aAt S1 n = 1 ∨ aAt S1 n = -1 := by
            apply pm_entry_of_getD S1.isTuryn.x_pm;
            exact S1.isTuryn.x_len.symm ▸ Nat.pred_lt ( ne_bot_of_gt hn )
          have h_last' : bAt S1 n = 1 ∨ bAt S1 n = -1 := by
            apply pm_entry_of_getD S1.isTuryn.y_pm (by
            rw [ S1.isTuryn.y_len ] ; omega)
          have h_last'' : cAt S1 n = 1 ∨ cAt S1 n = -1 := by
            have := S1.isTuryn.z_pm;
            exact pm_entry_of_getD this ( show n - 1 < S1.C.length from by { have := S1.isTuryn.z_len; omega } )
          aesop;
        exact ⟨ S1, hS1, ⟨ ha, h_last.1, hb, h_last.2, hc, hd ⟩ ⟩

set_option maxHeartbeats 800000 in
/-- Step 2: enforce condition (2) by optional reversal of `A`. -/
theorem step2_condition2
    (n : Nat) (hn : 2 ≤ n) (S : TurynTypeSeq n)
    (h1 : Canonical1 n S) :
    ∃ S2 : TurynTypeSeq n, Equivalent n S S2 ∧ Canonical1 n S2 ∧ Canonical2 n S2 := by
      by_contra h;
      -- By definition of $Canonical2$, there exists some $i$ such that $1 \leq i \leq n$, $aAt S i \neq aAt S (n + 1 - i)$, and $aAt S i = -1$.
      obtain ⟨i, hi⟩ : ∃ i, 1 ≤ i ∧ i ≤ n ∧ (∀ j, 1 ≤ j → j < i → aAt S j = aAt S (n + 1 - j)) ∧ aAt S i ≠ aAt S (n + 1 - i) ∧ aAt S i = -1 := by
        contrapose! h;
        refine' ⟨ S, _, h1, _ ⟩;
        · constructor;
        · intro i hi₁ hi₂ hi₃ hi₄;
          have h_pm : aAt S i = 1 ∨ aAt S i = -1 := by
            apply pm_entry_of_getD;
            · exact S.isTuryn.x_pm;
            · have := S.isTuryn.x_len;
              omega;
          exact h_pm.resolve_right ( h i hi₁ hi₂ hi₃ hi₄ );
      refine' h ⟨ S.doRevA, _, _, _ ⟩;
      · exact .single ( Elementary.revA S );
      · unfold Canonical1 at *;
        unfold aAt bAt cAt dAt at *;
        cases n <;> simp_all +decide [ TurynTypeSeq.doRevA ];
        have := S.isTuryn.x_len; simp_all +decide [ List.getElem?_reverse ] ;
      · intro j hj₁ hj₂ hj₃ hj₄;
        -- By definition of $doRevA$, we have $aAt S.doRevA j = aAt S (n + 1 - j)$.
        have h_rev : aAt S.doRevA j = aAt S (n + 1 - j) := by
          unfold aAt TurynTypeSeq.doRevA;
          simp +decide [ List.getD_eq_default, Nat.sub_sub ];
          rw [ List.getElem?_reverse ];
          · rw [ show List.length S.A = n from S.isTuryn.x_len ];
            rw [ show n - 1 - ( j - 1 ) = n - j from by omega ];
          · have := S.isTuryn.x_len;
            omega;
        by_cases h_cases : j < i;
        · have h_rev : aAt S.doRevA (n + 1 - j) = aAt S j := by
            unfold aAt; simp +decide [ TurynTypeSeq.doRevA ] ;
            rw [ List.getElem?_reverse ];
            · rw [ show List.length S.A = n from S.isTuryn.x_len ];
              rw [ show n - 1 - ( n + 1 - j - 1 ) = j - 1 from by omega ];
            · rw [ S.isTuryn.x_len ] ; omega;
          grind;
        · cases lt_or_eq_of_le ( le_of_not_gt h_cases ) <;> simp_all +decide;
          · specialize hj₃ i hi.1 ( by linarith ) ; simp_all +decide [ TurynTypeSeq.doRevA ];
            unfold aAt at * ; simp_all +decide [ List.getElem?_reverse ];
            rw [ List.getElem?_reverse, List.getElem?_reverse ] at *;
            · rw [ show List.length S.A = n from S.isTuryn.x_len ] at *;
              grind;
            · rw [ S.isTuryn.x_len ] ; omega;
            · rw [ S.isTuryn.x_len ] ; omega;
            · exact lt_of_lt_of_le ( Nat.sub_lt hj₁ zero_lt_one ) ( by linarith [ S.isTuryn.x_len ] );
            · grind +splitImp;
          · have h_rev : aAt S (n + 1 - j) = 1 ∨ aAt S (n + 1 - j) = -1 := by
              have := S.isTuryn.x_pm;
              apply pm_entry_of_getD this;
              rw [ S.isTuryn.x_len ] ; omega;
            grind

set_option maxHeartbeats 800000 in
/-- Step 3: enforce condition (3) by optional reversal of `B`. -/
theorem step3_condition3
    (n : Nat) (hn : 2 ≤ n) (S : TurynTypeSeq n)
    (h12 : Canonical1 n S ∧ Canonical2 n S) :
    ∃ S3 : TurynTypeSeq n,
      Equivalent n S S3 ∧ Canonical1 n S3 ∧ Canonical2 n S3 ∧ Canonical3 n S3 := by
        by_contra h_contra;
        -- If `B` does not satisfy condition (3), we reverse `B`.
        by_cases hB : ∃ i, 1 ≤ i ∧ i ≤ n ∧ (∀ j, 1 ≤ j → j < i → bAt S j = bAt S (n + 1 - j)) ∧ bAt S i ≠ bAt S (n + 1 - i) ∧ bAt S i = -1;
        · refine' h_contra ⟨ TurynTypeSeq.doRevB S, _, _, _, _ ⟩ <;> simp_all +decide [ TurynTypeSeq.doRevB ];
          · exact .single ( Elementary.revB S );
          · unfold Canonical1 at *;
            unfold aAt bAt cAt dAt at *;
            simp_all +decide [ List.getD_eq_default ];
            rw [ List.getElem?_reverse, List.getElem?_reverse ];
            · have := S.isTuryn; cases this; aesop;
            · grind;
            · linarith [ S.isTuryn.x_len, S.isTuryn.y_len, S.isTuryn.z_len, S.isTuryn.w_len ];
          · intro j hj1 hj2 hj3 hj4; have := h12.2 j hj1 hj2; simp_all +decide [ TurynTypeSeq.doRevB ] ;
            unfold aAt at *; aesop;
          · intro j hj1 hj2 hj3 hj4; simp_all +decide [ bAt ] ;
            rw [ List.getElem?_reverse, List.getElem?_reverse ] at * ; simp_all +decide [ Nat.sub_sub ];
            · have := S.isTuryn.y_pm; simp_all +decide [ AllPmOne ] ;
              cases this ( S.B[List.length S.B - j]?.getD 0 ) ( by
                have := S.isTuryn.y_len; simp_all +decide [ Nat.sub_sub ] ;
                grind +ring ) <;> simp_all +decide [ Nat.sub_sub ];
              have := S.isTuryn.y_len; simp_all +decide [ Nat.sub_sub ] ;
              grind +ring;
            · have := S.isTuryn.y_len; simp_all +decide [ Nat.sub_sub ] ;
              exact ⟨ by linarith, by linarith ⟩;
            · exact lt_of_lt_of_le ( Nat.sub_lt hj1 zero_lt_one ) ( by simpa [ S.isTuryn.y_len ] using hj2 );
            · exact lt_of_lt_of_le ( Nat.sub_lt hj1 zero_lt_one ) ( by simpa [ S.isTuryn.y_len ] using hj2 );
        · refine' h_contra ⟨ S, _, _, _, _ ⟩;
          · constructor;
          · exact h12.1;
          · exact h12.2;
          · intro i hi₁ hi₂ hi₃ hi₄;
            have h_bAt : bAt S i = 1 ∨ bAt S i = -1 := by
              have hB : AllPmOne S.B := by
                exact S.isTuryn.y_pm;
              convert pm_entry_of_getD hB _;
              exact lt_of_lt_of_le ( Nat.sub_lt hi₁ zero_lt_one ) ( by linarith [ S.isTuryn.y_len ] );
            grind

set_option maxHeartbeats 800000 in
/-- Step 4: enforce condition (4) by optional `−C*`. -/
theorem step4_condition4
    (n : Nat) (hn : 2 ≤ n) (S : TurynTypeSeq n)
    (h123 : Canonical1 n S ∧ Canonical2 n S ∧ Canonical3 n S) :
    ∃ S4 : TurynTypeSeq n,
      Equivalent n S S4 ∧ Canonical1 n S4 ∧ Canonical2 n S4 ∧
      Canonical3 n S4 ∧ Canonical4 n S4 := by
        by_cases h_exists : ∃ i, 1 ≤ i ∧ i ≤ n ∧ (∀ j, 1 ≤ j → j < i → cAt S j ≠ cAt S (n + 1 - j)) ∧ cAt S i = cAt S (n + 1 - i) ∧ cAt S i = -1;
        · obtain ⟨i, hi⟩ := h_exists
          use ⟨S.A, S.B, negSeq (S.C.reverse), S.D, by
            exact turynProp_negC ( turynProp_revC S.isTuryn )⟩
          generalize_proofs at *;
          refine' ⟨ _, _, _, _, _ ⟩;
          · exact Relation.ReflTransGen.single ( Elementary.revC _ ) |> Relation.ReflTransGen.trans <| Relation.ReflTransGen.single ( Elementary.negC _ );
          · unfold Canonical1 at *;
            have := S.isTuryn; rcases this with ⟨ hA, hB, hC, hD, hA', hB', hC', hD', h ⟩ ; simp_all +decide [ negSeq ] ;
            have := lemma1_endpoint_constraint n hn S; simp_all +decide [ cAt ] ;
            unfold Canonical1 at this; simp_all +decide [ aAt, bAt, cAt, dAt ] ;
            grind;
          · exact h123.2.1;
          · exact h123.2.2;
          · intro j hj₁ hj₂ hj₃; simp_all +decide [ negSeq ] ;
            contrapose! hj₃;
            refine' ⟨ i, hi.1, _, _ ⟩ <;> simp_all +decide [ cAt ];
            · grind +suggestions;
            · grind +suggestions;
        · refine' ⟨ S, _, h123.1, h123.2.1, h123.2.2, fun i hi₁ hi₂ hi₃ hi₄ => _ ⟩;
          · constructor;
          · have h_c_i : cAt S i = 1 ∨ cAt S i = -1 := by
              have := S.isTuryn.z_pm; simp_all +decide [ cAt ] ;
              have := pm_entry_of_getD this ( show n + 1 - i - 1 < S.C.length from ?_ ) ; aesop;
              rw [ S.isTuryn.z_len ] ; omega;
            grind

/-
Reversal of a list maps index j to (length-1-j).
-/
lemma revD_getD {D : PmSeq} {j : Nat} (hj : j < D.length) :
    D.reverse.getD j 0 = D.getD (D.length - 1 - j) 0 := by
      grind

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
      -- By definition of `doNegD`, we have `dAt (doNegD S) j = -dAt S j`.
      have h_negD : dAt (TurynTypeSeq.doNegD (TurynTypeSeq.doRevD S)) j = -(dAt (TurynTypeSeq.doRevD S) j) := by
        convert negSeq_getD _ _ using 1;
      rw [ h_negD, dAt_doRevD S hj1 hj2 ]

set_option maxHeartbeats 800000 in
/-- Step 5: enforce condition (5) by optional `D*` or `−D*`. -/
theorem step5_condition5
    (n : Nat) (hn : 2 ≤ n) (S : TurynTypeSeq n)
    (h1234 : Canonical1 n S ∧ Canonical2 n S ∧ Canonical3 n S ∧ Canonical4 n S) :
    ∃ S5 : TurynTypeSeq n,
      Equivalent n S S5 ∧
      Canonical1 n S5 ∧ Canonical2 n S5 ∧ Canonical3 n S5 ∧
      Canonical4 n S5 ∧ Canonical5 n S5 := by
        by_contra h_contra;
        -- By definition of negation, there exists some $i$ such that $1 \leq i \leq n - 1$ and the product condition fails.
        obtain ⟨i, hi1, hi2⟩ : ∃ i, 1 ≤ i ∧ i ≤ n - 1 ∧ (∀ j, 1 ≤ j → j < i → dAt S j * dAt S (n - j) = dAt S (n - 1)) ∧ dAt S i * dAt S (n - i) ≠ dAt S (n - 1) ∧ dAt S i ≠ 1 := by
          simp_all +decide [ Canonical5 ];
          exact h_contra S ( Relation.ReflTransGen.refl ) h1234.1 h1234.2.1 h1234.2.2.1 h1234.2.2.2;
        -- Consider two cases: $dAt S (n - 1) = 1$ or $dAt S (n - 1) = -1$.
        by_cases h_case : dAt S (n - 1) = 1;
        · refine' h_contra ⟨ S.doRevD, _, _, _, _, _, _ ⟩;
          exact Relation.ReflTransGen.single ( Elementary.revD S );
          · unfold Canonical1 at *;
            unfold aAt bAt cAt dAt at *;
            rcases n with ( _ | _ | n ) <;> simp_all +decide [ TurynTypeSeq.doRevD ];
            have := S.isTuryn.w_len; simp_all +decide [ List.getElem?_reverse ] ;
          · exact h1234.2.1;
          · exact h1234.2.2.1;
          · exact h1234.2.2.2;
          · intro j hj1 hj2 hj3 hj4;
            -- By definition of `doRevD`, we have `dAt S.doRevD j = dAt S (n - j)`.
            have h_revD : dAt S.doRevD j = dAt S (n - j) := by
              exact?;
            by_cases hj5 : j < i;
            · have h_revD : dAt S.doRevD (n - j) = dAt S j := by
                convert dAt_doRevD S ( show 1 ≤ n - j from Nat.sub_pos_of_lt ( by omega ) ) ( show n - j ≤ n - 1 from Nat.sub_le_sub_left ( by omega ) _ ) using 1;
                rw [ Nat.sub_sub_self ( by omega ) ];
              have h_revD : dAt S.doRevD (n - 1) = dAt S 1 := by
                convert dAt_doRevD S ( show 1 ≤ n - 1 from Nat.sub_pos_of_lt hn ) ( show n - 1 ≤ n - 1 from le_rfl ) using 1;
                rw [ Nat.sub_sub_self ( by linarith ) ];
              grind;
            · cases lt_or_eq_of_le ( le_of_not_gt hj5 ) <;> simp_all +decide;
              · have h_revD_i : dAt S.doRevD i = dAt S (n - i) := by
                  exact dAt_doRevD S hi1 ( by omega )
                have h_revD_n_i : dAt S.doRevD (n - i) = dAt S i := by
                  convert dAt_doRevD S ( show 1 ≤ n - i from Nat.sub_pos_of_lt ( by omega ) ) ( show n - i ≤ n - 1 from Nat.sub_le_sub_left ( by omega ) _ ) using 1;
                  rw [ Nat.sub_sub_self ( by omega ) ]
                have h_revD_n_1 : dAt S.doRevD (n - 1) = dAt S 1 := by
                  convert dAt_doRevD S ( show 1 ≤ n - 1 from Nat.sub_pos_of_lt hn ) ( show n - 1 ≤ n - 1 from le_rfl ) using 1;
                  lia;
                grind +locals;
              · have h_pm : dAt S j = 1 ∨ dAt S j = -1 := by
                  apply pm_entry_of_getD;
                  · exact S.isTuryn.w_pm;
                  · exact lt_of_lt_of_le ( Nat.sub_lt hj1 zero_lt_one ) ( by simpa [ S.isTuryn.w_len ] using by omega );
                have h_pm : dAt S (n - j) = 1 ∨ dAt S (n - j) = -1 := by
                  have h_pm : ∀ i, 1 ≤ i → i ≤ n - 1 → dAt S i = 1 ∨ dAt S i = -1 := by
                    intros i hi1 hi2;
                    have := S.isTuryn.w_pm;
                    convert pm_entry_of_getD this _;
                    have := S.isTuryn.w_len; omega;
                  exact h_pm _ ( Nat.sub_pos_of_lt ( by omega ) ) ( Nat.sub_le_sub_left hj1 _ );
                grind;
        · -- Since $dAt S (n - 1) \neq 1$, we have $dAt S (n - 1) = -1$.
          have h_case_neg : dAt S (n - 1) = -1 := by
            have h_case_neg : dAt S (n - 1) = 1 ∨ dAt S (n - 1) = -1 := by
              apply pm_entry_of_getD;
              · exact S.isTuryn.w_pm;
              · have := S.isTuryn.w_len; aesop;
            exact h_case_neg.resolve_left h_case;
          -- Apply doRevD then doNegD to S.
          set S5 := TurynTypeSeq.doNegD (TurynTypeSeq.doRevD S);
          refine' h_contra ⟨ S5, _, _, _, _, _, _ ⟩;
          exact .single ( Elementary.revD S ) |> Relation.ReflTransGen.trans <| .single ( Elementary.negD _ );
          · unfold Canonical1 at *;
            convert dAt_doNegRevD S ( by linarith : 1 ≤ 1 ) ( by omega ) using 1 ; aesop;
          · exact h1234.2.1;
          · exact h1234.2.2.1;
          · exact h1234.2.2.2;
          · intro j hj1 hj2 hj3 hj4;
            -- By definition of $S5$, we know that $dAt S5 j = -(dAt S (n - j))$ and $dAt S5 (n - j) = -(dAt S j)$.
            have h_dAt_S5 : dAt S5 j = -(dAt S (n - j)) ∧ dAt S5 (n - j) = -(dAt S j) := by
              have h_dAt_S5 : dAt S5 j = -(dAt S (n - j)) := by
                grind +suggestions
              have h_dAt_S5' : dAt S5 (n - j) = -(dAt S j) := by
                convert dAt_doNegRevD S ( show 1 ≤ n - j from Nat.sub_pos_of_lt ( by omega ) ) ( show n - j ≤ n - 1 from Nat.sub_le_sub_left ( by omega ) _ ) using 1;
                rw [ Nat.sub_sub_self ( by omega ) ]
              exact ⟨h_dAt_S5, h_dAt_S5'⟩;
            by_cases hi : i < j;
            · specialize hj3 i hi1 hi;
              have h_dAt_S5_i : dAt S5 i = -(dAt S (n - i)) ∧ dAt S5 (n - i) = -(dAt S i) := by
                apply And.intro;
                · apply dAt_doNegRevD;
                  · grind +splitIndPred;
                  · linarith;
                · convert dAt_doNegRevD S ( show 1 ≤ n - i from Nat.sub_pos_of_lt ( by omega ) ) ( show n - i ≤ n - 1 from Nat.sub_le_sub_left ( by omega ) _ ) using 1;
                  rw [ Nat.sub_sub_self ( by omega ) ];
              have h_dAt_S5_n_minus_1 : dAt S5 (n - 1) = -(dAt S 1) := by
                convert dAt_doNegRevD S ( show 1 ≤ n - 1 from Nat.le_sub_one_of_lt hn ) ( show n - 1 ≤ n - 1 from le_rfl ) using 1;
                rw [ Nat.sub_sub_self ( by linarith ) ];
              have := h1234.1.2.2.2.2.2; simp_all +decide [ mul_comm ] ;
            · cases lt_or_eq_of_le ( le_of_not_gt hi ) <;> simp_all +decide;
              · have := hi2.2.1 j hj1 ‹_›;
                cases' Int.eq_one_or_neg_one_of_mul_eq_neg_one this with h h <;> simp_all +decide;
                exact hj4 ( by rw [ show dAt S5 ( n - 1 ) = - ( dAt S 1 ) by
                                      convert dAt_doNegRevD S ( show 1 ≤ n - 1 from Nat.sub_pos_of_lt hn ) ( show n - 1 ≤ n - 1 from le_rfl ) using 1;
                                      rw [ Nat.sub_sub_self ( by linarith ) ] ] ; linarith [ h1234.1.2.2.2.2.2 ] );
              · have h_dAt_S_i : dAt S i = 1 ∨ dAt S i = -1 := by
                  have := S.isTuryn.w_pm;
                  have := this ( S.D.getD ( i - 1 ) 0 ) ; simp_all +decide [ dAt ] ;
                  grind
                have h_dAt_S_n_i : dAt S (n - i) = 1 ∨ dAt S (n - i) = -1 := by
                  have := S.isTuryn.w_pm;
                  apply pm_entry_of_getD this;
                  rw [ S.isTuryn.w_len ] ; omega;
                grind

set_option maxHeartbeats 800000 in
/-- Step 6: enforce condition (6) using optional swap. -/
theorem step6_condition6
    (n : Nat) (hn_even : n % 2 = 0) (hn : 2 ≤ n) (S : TurynTypeSeq n)
    (h12345 : Canonical1 n S ∧ Canonical2 n S ∧ Canonical3 n S ∧
              Canonical4 n S ∧ Canonical5 n S) :
    ∃ S6 : TurynTypeSeq n,
      Equivalent n S S6 ∧
      Canonical1 n S6 ∧ Canonical2 n S6 ∧ Canonical3 n S6 ∧
      Canonical4 n S6 ∧ Canonical5 n S6 ∧ Canonical6 n S6 := by
        -- Consider two cases: $aAt 2 \neq bAt 2$ and $aAt 2 = bAt 2$.
        by_cases h_cases : aAt S 2 ≠ bAt S 2;
        · by_cases h_a2 : aAt S 2 = 1;
          · exact ⟨ S, by constructor, h12345.1, h12345.2.1, h12345.2.2.1, h12345.2.2.2.1, h12345.2.2.2.2, by unfold Canonical6; aesop ⟩;
          · -- If `aAt 2 = -1`, then `bAt 2 = 1` (since they're ±1 and different). Apply `doSwap` to satisfy `Canonical6`.
            have h_b2 : bAt S 2 = 1 := by
              have h_b2 : bAt S 2 = 1 ∨ bAt S 2 = -1 := by
                apply pm_entry_of_getD;
                · exact S.isTuryn.y_pm;
                · have := S.isTuryn.y_len; aesop;
              have h_a2 : aAt S 2 = 1 ∨ aAt S 2 = -1 := by
                apply pm_entry_of_getD;
                · exact S.isTuryn.x_pm;
                · have := S.isTuryn.x_len; aesop;
              grind;
            refine' ⟨ S.doSwap, _, _, _, _, _, _ ⟩ <;> simp_all +decide [ Equivalent ];
            exact .single ( Elementary.swap S );
            · exact ⟨ h12345.1.2.2.1, h12345.1.2.2.2.1, h12345.1.1, h12345.1.2.1, h12345.1.2.2.2.2.1, h12345.1.2.2.2.2.2 ⟩;
            · grind +locals;
            · exact h12345.2.1;
            · intro i hi₁ hi₂ hi₃ hi₄; have := h12345.2.2.2.1 i hi₁ hi₂; simp_all +decide [ TurynTypeSeq.doSwap ] ;
              exact this ( fun j hj₁ hj₂ => by simpa using hi₃ j hj₁ hj₂ ) ( by simpa using hi₄ ) |> fun h => by simpa using h;
            · unfold Canonical5 Canonical6; simp_all +decide [ TurynTypeSeq.doSwap ] ;
              unfold aAt bAt dAt at * ; aesop ( simp_config := { singlePass := true } ) ;
        · use if aAt S (n - 1) = 1 ∧ bAt S (n - 1) = -1 then S else S.doSwap;
          split_ifs <;> simp_all +decide [ Canonical6 ];
          · constructor;
          · refine' ⟨ _, _, _, _, _, _, _ ⟩;
            exact .single ( Elementary.swap S );
            all_goals unfold Canonical1 at *; simp_all +decide [ TurynTypeSeq.doSwap ] ;
            all_goals unfold aAt bAt cAt dAt at *; simp_all +decide [ TurynTypeSeq ] ;
            · grind +locals;
            · exact h12345.2.1;
            · exact h12345.2.2.2.1;
            · exact h12345.2.2.2.2;
            · rcases n with ( _ | _ | _ | n ) <;> simp_all +decide [ Nat.sub_sub ];
              have := S.isTuryn; rcases this with ⟨ hA, hB, hC, hD, hA', hB', hC', hD', h ⟩ ; simp_all +decide [ Nat.add_mod, Nat.mod_two_of_bodd ] ;
              cases hA' ( S.A[n + 1] ) ( by simp ) <;> cases hB' ( S.B[n + 1] ) ( by simp ) <;> simp_all +decide only [Nat.succ_eq_add_one] ;
              · specialize h ( n + 1 ) ; simp_all +decide [ combinedAutocorr ] ;
                unfold aperiodicAutocorr at h; simp_all +decide [ List.getElem?_eq_getElem ] ;
                simp_all +decide [ Finset.sum_range_succ ];
                simp_all +decide [ add_comm 1, add_left_comm 1 ];
                cases hB' ( S.B[1] ) ( by simp ) <;> cases hC' ( S.C[n + 1] ) ( by simp ) <;> cases hC' ( S.C[1] ) ( by simp ) <;> cases hC' ( S.C[n + 1 + 1] ) ( by simp ) <;> cases hD' ( S.D[n + 1] ) ( by simp ) <;> simp_all ( config := { decide := Bool.true } ) only [ ] ;
              · norm_num;
              · specialize h ( n + 1 ) ; simp_all +decide [ combinedAutocorr ];
                unfold aperiodicAutocorr at h; simp_all +decide [ List.getElem?_eq_getElem ] ;
                simp_all +decide [ Finset.sum_range_succ ];
                simp_all +decide [ add_comm 1, add_left_comm 1 ];
                cases hB' ( S.B[1] ) ( by simp ) <;> cases hC' ( S.C[n + 1] ) ( by simp ) <;> cases hC' ( S.C[n + 1 + 1] ) ( by simp ) <;> cases hD' ( S.D[n + 1] ) ( by simp ) <;> simp_all +decide only [Nat.succ_eq_add_one] ;
                all_goals cases hC' ( S.C[1] ) ( by simp ) <;> simp_all +decide only [Nat.succ_eq_add_one] ;

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
