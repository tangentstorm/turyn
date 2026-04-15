import Turyn.TurynType

/-!
# Equivalence and canonical representatives for Turyn-type sequences

This file is a best-effort Lean transcription of the full six-step canonical
normalization proof sketch for Turyn-type sequences.

The end theorem follows the same structure as the writeup:
1. normalize endpoints,
2. normalize the first asymmetric index of `A`,
3. normalize the first asymmetric index of `B`,
4. normalize the first symmetric index of `C`,
5. normalize the first exceptional index of `D`,
6. normalize the `A/B` tie-breaking condition.

Several technically heavy preservation lemmas (showing that each elementary
operation preserves the Turyn condition and composes as expected) are stated as
axioms so the theorem can be written in explicit Lean syntax now while the
full mechanization is completed later.
-/

namespace Turyn

/-- A Turyn-type quadruple packaged as a single object. -/
structure TurynTypeSeq (n : Nat) where
  A : PmSeq
  B : PmSeq
  C : PmSeq
  D : PmSeq
  isTuryn : IsTurynType n A B C D

/-- Entry accessor for `A` (1-indexed). -/
def aAt {n : Nat} (S : TurynTypeSeq n) (i : Nat) : Int := S.A.getD (i - 1) 0
/-- Entry accessor for `B` (1-indexed). -/
def bAt {n : Nat} (S : TurynTypeSeq n) (i : Nat) : Int := S.B.getD (i - 1) 0
/-- Entry accessor for `C` (1-indexed). -/
def cAt {n : Nat} (S : TurynTypeSeq n) (i : Nat) : Int := S.C.getD (i - 1) 0
/-- Entry accessor for `D` (1-indexed). -/
def dAt {n : Nat} (S : TurynTypeSeq n) (i : Nat) : Int := S.D.getD (i - 1) 0

/-- Negation of a sequence. -/
def negSeq (X : PmSeq) : PmSeq := X.map (fun x => -x)

/-- Alternation of a sequence: `(x₁, -x₂, x₃, -x₄, ...)`. -/
def altSeq (X : PmSeq) : PmSeq :=
  (List.range X.length).map (fun i => ((if i % 2 = 0 then 1 else -1) : Int) * X.getD i 0)

/-- Elementary transformations from the Turyn canonicalization proof.

This relation is intended to encode the four move families:
(T1) negate one component, (T2) reverse one component,
(T3) alternate all four components, and (T4) swap `A`/`B`.
-/
constant Elementary (n : Nat) : TurynTypeSeq n → TurynTypeSeq n → Prop

/-- Equivalence is the reflexive-transitive closure of elementary transformations. -/
def Equivalent (n : Nat) (S T : TurynTypeSeq n) : Prop := Relation.ReflTransGen (Elementary n) S T

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

/-- Step 1 of the proof sketch: enforce condition (1). -/
axiom step1_condition1
    (n : Nat) (hn : 2 ≤ n) (S : TurynTypeSeq n) :
    ∃ S1 : TurynTypeSeq n, Equivalent n S S1 ∧ Canonical1 n S1

/-- Lemma 1 in the writeup: endpoint constraint `c_n = -1` under condition (1). -/
axiom lemma1_endpoint_constraint
    (n : Nat) (hn : 1 < n) (S : TurynTypeSeq n)
    (h1 : Canonical1 n S) :
    cAt S n = -1

/-- Step 2: enforce condition (2) by optional reversal of `A`. -/
axiom step2_condition2
    (n : Nat) (hn : 2 ≤ n) (S : TurynTypeSeq n)
    (h1 : Canonical1 n S) :
    ∃ S2 : TurynTypeSeq n, Equivalent n S S2 ∧ Canonical1 n S2 ∧ Canonical2 n S2

/-- Step 3: enforce condition (3) by optional reversal of `B`. -/
axiom step3_condition3
    (n : Nat) (hn : 2 ≤ n) (S : TurynTypeSeq n)
    (h12 : Canonical1 n S ∧ Canonical2 n S) :
    ∃ S3 : TurynTypeSeq n, Equivalent n S S3 ∧ Canonical1 n S3 ∧ Canonical2 n S3 ∧ Canonical3 n S3

/-- Step 4: enforce condition (4) by optional `-C'`. -/
axiom step4_condition4
    (n : Nat) (hn : 2 ≤ n) (S : TurynTypeSeq n)
    (h123 : Canonical1 n S ∧ Canonical2 n S ∧ Canonical3 n S) :
    ∃ S4 : TurynTypeSeq n,
      Equivalent n S S4 ∧ Canonical1 n S4 ∧ Canonical2 n S4 ∧ Canonical3 n S4 ∧ Canonical4 n S4

/-- Step 5: enforce condition (5) by optional `D'` or `-D'`. -/
axiom step5_condition5
    (n : Nat) (hn : 2 ≤ n) (S : TurynTypeSeq n)
    (h1234 : Canonical1 n S ∧ Canonical2 n S ∧ Canonical3 n S ∧ Canonical4 n S) :
    ∃ S5 : TurynTypeSeq n,
      Equivalent n S S5 ∧
      Canonical1 n S5 ∧ Canonical2 n S5 ∧ Canonical3 n S5 ∧ Canonical4 n S5 ∧ Canonical5 n S5

/-- Step 6: enforce condition (6) using the `i = n-2` congruence and optional swap. -/
axiom step6_condition6
    (n : Nat) (hn_even : n % 2 = 0) (hn : 2 ≤ n) (S : TurynTypeSeq n)
    (h12345 : Canonical1 n S ∧ Canonical2 n S ∧ Canonical3 n S ∧ Canonical4 n S ∧ Canonical5 n S) :
    ∃ S6 : TurynTypeSeq n,
      Equivalent n S S6 ∧
      Canonical1 n S6 ∧ Canonical2 n S6 ∧ Canonical3 n S6 ∧ Canonical4 n S6 ∧ Canonical5 n S6 ∧ Canonical6 n S6

/-- Transitivity of equivalence (closure composition). -/
theorem equivalent_trans
    (n : Nat) {S T U : TurynTypeSeq n} :
    Equivalent n S T → Equivalent n T U → Equivalent n S U := by
  intro hST hTU
  exact Relation.ReflTransGen.trans hST hTU

/-- Every equivalence class of Turyn-type sequences has a canonical representative. -/
theorem canonical_representative_exists
    (n : Nat) (hn_even : n % 2 = 0) (hn : 2 ≤ n) (S : TurynTypeSeq n) :
    ∃ T : TurynTypeSeq n, Equivalent n S T ∧ Canonical n T := by
  rcases step1_condition1 n hn S with ⟨S1, hSS1, h1⟩
  rcases step2_condition2 n hn S1 h1 with ⟨S2, hS1S2, h1S2, h2S2⟩
  rcases step3_condition3 n hn S2 ⟨h1S2, h2S2⟩ with ⟨S3, hS2S3, h1S3, h2S3, h3S3⟩
  rcases step4_condition4 n hn S3 ⟨h1S3, h2S3, h3S3⟩ with ⟨S4, hS3S4, h1S4, h2S4, h3S4, h4S4⟩
  rcases step5_condition5 n hn S4 ⟨h1S4, h2S4, h3S4, h4S4⟩ with
    ⟨S5, hS4S5, h1S5, h2S5, h3S5, h4S5, h5S5⟩
  rcases step6_condition6 n hn_even hn S5 ⟨h1S5, h2S5, h3S5, h4S5, h5S5⟩ with
    ⟨S6, hS5S6, h1S6, h2S6, h3S6, h4S6, h5S6, h6S6⟩

  refine ⟨S6, ?_, ?_⟩
  exact equivalent_trans n (equivalent_trans n (equivalent_trans n (equivalent_trans n hSS1 hS1S2) hS2S3) hS3S4) (equivalent_trans n hS4S5 hS5S6)
  exact ⟨h1S6, h2S6, h3S6, h4S6, h5S6, h6S6⟩

end Turyn
