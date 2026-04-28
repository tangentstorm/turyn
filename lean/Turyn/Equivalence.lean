import Turyn.TurynType
import Turyn.BaseSequence
import Mathlib

/-!
# Equivalence and canonical representatives for Turyn-type sequences

Based on:
- Best, D.J., Đoković, D.Ž., Kharaghani, H., and Ramp, H.,
  "Turyn-type sequences: Classification, Enumeration and Construction,"
  arXiv:1206.4107v1, 2013.

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

open Finset BigOperators Turyn

namespace Turyn

/-! ### Helper: ±1 entries via lookupNat -/

lemma pm_lookupNat {n : Nat} {a : Fin n → Int} (hpm : AllPmOne a) {i : Nat} (hi : i < n) :
    lookupNat a i = 1 ∨ lookupNat a i = -1 := by
  rw [lookupNat_of_lt a hi]
  exact hpm ⟨i, hi⟩

/-! ### Endpoint constraint from vanishing at s = n-1 -/

lemma aperiodicAutocorr_last {n : Nat} (a : Fin n → Int) (hn : 1 < n) :
    aperiodicAutocorr a (n - 1) = lookupNat a 0 * lookupNat a (n - 1) := by
  unfold aperiodicAutocorr
  rw [if_neg (by omega)]
  rw [show n - (n - 1) = 1 from by omega]
  rw [Finset.sum_range_one]
  simp

lemma endpoint_relation {n : Nat} (hn : 1 < n) (S : TurynType n) :
    xAt S 1 * xAt S n + yAt S 1 * yAt S n + 2 * (zAt S 1 * zAt S n) = 0 := by
  have hv := S.vanishing (n - 1) (by omega) (by omega)
  unfold combinedAutocorr at hv
  rw [aperiodicAutocorr_last S.X.data (by omega),
      aperiodicAutocorr_last S.Y.data (by omega),
      aperiodicAutocorr_last S.Z.data (by omega)] at hv
  have hW : aperiodicAutocorr S.W.data (n - 1) = 0 := by
    unfold aperiodicAutocorr; simp
  unfold xAt yAt zAt
  simp only [show 1 - 1 = 0 from rfl]
  linarith

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

private lemma step1_xAt_doNegX {n : Nat} (S : TurynType n) (i : Nat) :
    xAt S.doNegX i = -(xAt S i) := by
  simp [xAt, TurynType.doNegX, PmSeq.neg_data, lookupNat_negSeqFn]

private lemma step1_yAt_doNegY {n : Nat} (S : TurynType n) (i : Nat) :
    yAt S.doNegY i = -(yAt S i) := by
  simp [yAt, TurynType.doNegY, PmSeq.neg_data, lookupNat_negSeqFn]

private lemma step1_zAt_doNegZ {n : Nat} (S : TurynType n) (i : Nat) :
    zAt S.doNegZ i = -(zAt S i) := by
  simp [zAt, TurynType.doNegZ, PmSeq.neg_data, lookupNat_negSeqFn]

private lemma step1_wAt_doNegW {n : Nat} (S : TurynType n) (i : Nat) :
    wAt S.doNegW i = -(wAt S i) := by
  simp [wAt, TurynType.doNegW, PmSeq.neg_data, lookupNat_negSeqFn]

private lemma altSeqFn_lookupNat_zero {n : Nat} (a : Fin n → Int) (_hn : 0 < n) :
    lookupNat (altSeqFn a) 0 = lookupNat a 0 := by
  rw [lookupNat_altSeqFn]; norm_num

private lemma altSeqFn_lookupNat_last {n : Nat} (a : Fin n → Int)
    (hn_even : n % 2 = 0) (hn : 2 ≤ n) :
    lookupNat (altSeqFn a) (n - 1) = -(lookupNat a (n - 1)) := by
  rw [lookupNat_altSeqFn]
  rw [if_neg (by omega)]
  ring

private lemma step1_xAt_doAltAll_first {n : Nat} (S : TurynType n) (hn : 1 ≤ n) :
    xAt S.doAltAll 1 = xAt S 1 := by
  simp only [xAt, TurynType.doAltAll, PmSeq.alt_data, show 1 - 1 = 0 from rfl]
  exact altSeqFn_lookupNat_zero S.X.data (by omega)

private lemma step1_yAt_doAltAll_first {n : Nat} (S : TurynType n) (hn : 1 ≤ n) :
    yAt S.doAltAll 1 = yAt S 1 := by
  simp only [yAt, TurynType.doAltAll, PmSeq.alt_data, show 1 - 1 = 0 from rfl]
  exact altSeqFn_lookupNat_zero S.Y.data (by omega)

private lemma step1_zAt_doAltAll_first {n : Nat} (S : TurynType n) (hn : 1 ≤ n) :
    zAt S.doAltAll 1 = zAt S 1 := by
  simp only [zAt, TurynType.doAltAll, PmSeq.alt_data, show 1 - 1 = 0 from rfl]
  exact altSeqFn_lookupNat_zero S.Z.data (by omega)

private lemma step1_wAt_doAltAll_first {n : Nat} (S : TurynType n) (hn : 2 ≤ n) :
    wAt S.doAltAll 1 = wAt S 1 := by
  simp only [wAt, TurynType.doAltAll, PmSeq.alt_data, show 1 - 1 = 0 from rfl]
  exact altSeqFn_lookupNat_zero S.W.data (by omega)

private lemma step1_xAt_doAltAll_last {n : Nat} (S : TurynType n)
    (hn_even : n % 2 = 0) (hn : 2 ≤ n) :
    xAt S.doAltAll n = -(xAt S n) := by
  simp only [xAt, TurynType.doAltAll, PmSeq.alt_data]
  exact altSeqFn_lookupNat_last S.X.data hn_even hn

private lemma step1_yAt_doAltAll_last {n : Nat} (S : TurynType n)
    (hn_even : n % 2 = 0) (hn : 2 ≤ n) :
    yAt S.doAltAll n = -(yAt S n) := by
  simp only [yAt, TurynType.doAltAll, PmSeq.alt_data]
  exact altSeqFn_lookupNat_last S.Y.data hn_even hn

/-- Step 1: enforce condition (1) — normalize endpoint signs. -/
theorem step1_condition1
    (n : Nat) (hn_even : n % 2 = 0) (hn : 2 ≤ n) (S : TurynType n) :
    ∃ S1 : TurynType n, Equivalent n S S1 ∧ Canonical1 n S1 := by
  -- Step 1a: Normalize xAt 1 to +1.
  have ha_pm : xAt S 1 = 1 ∨ xAt S 1 = -1 :=
    pm_lookupNat S.X.pm (by omega)
  obtain ⟨Sa, hSa_eq, hSa_a1⟩ : ∃ Sa : TurynType n,
      Equivalent n S Sa ∧ xAt Sa 1 = 1 := by
    rcases ha_pm with ha1 | ha1
    · exact ⟨S, Relation.ReflTransGen.refl, ha1⟩
    · exact ⟨S.doNegX, Relation.ReflTransGen.single (Elementary.negX S),
        by rw [step1_xAt_doNegX, ha1]; norm_num⟩
  -- Step 1b: Normalize yAt 1 to +1.
  have hb_pm : yAt Sa 1 = 1 ∨ yAt Sa 1 = -1 :=
    pm_lookupNat Sa.Y.pm (by omega)
  obtain ⟨Sb, hSb_eq, hSb_a1, hSb_b1⟩ : ∃ Sb : TurynType n,
      Equivalent n Sa Sb ∧ xAt Sb 1 = 1 ∧ yAt Sb 1 = 1 := by
    rcases hb_pm with hb1 | hb1
    · exact ⟨Sa, Relation.ReflTransGen.refl, hSa_a1, hb1⟩
    · exact ⟨Sa.doNegY, Relation.ReflTransGen.single (Elementary.negY Sa),
        hSa_a1,
        by rw [step1_yAt_doNegY, hb1]; norm_num⟩
  -- Step 1c: Normalize zAt 1 to +1.
  have hc_pm : zAt Sb 1 = 1 ∨ zAt Sb 1 = -1 :=
    pm_lookupNat Sb.Z.pm (by omega)
  obtain ⟨Sc, hSc_eq, hSc_a1, hSc_b1, hSc_c1⟩ : ∃ Sc : TurynType n,
      Equivalent n Sb Sc ∧ xAt Sc 1 = 1 ∧ yAt Sc 1 = 1 ∧ zAt Sc 1 = 1 := by
    rcases hc_pm with hc1 | hc1
    · exact ⟨Sb, Relation.ReflTransGen.refl, hSb_a1, hSb_b1, hc1⟩
    · exact ⟨Sb.doNegZ, Relation.ReflTransGen.single (Elementary.negZ Sb),
        hSb_a1, hSb_b1,
        by rw [step1_zAt_doNegZ, hc1]; norm_num⟩
  -- Step 1d: Normalize wAt 1 to +1.
  have hd_pm : wAt Sc 1 = 1 ∨ wAt Sc 1 = -1 :=
    pm_lookupNat Sc.W.pm (by omega)
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
  have ha_n_pm : xAt Sd n = 1 ∨ xAt Sd n = -1 :=
    pm_lookupNat Sd.X.pm (by omega)
  have hb_n_pm : yAt Sd n = 1 ∨ yAt Sd n = -1 :=
    pm_lookupNat Sd.Y.pm (by omega)
  have hc_n_pm : zAt Sd n = 1 ∨ zAt Sd n = -1 :=
    pm_lookupNat Sd.Z.pm (by omega)
  have h_ep_raw := endpoint_relation (show 1 < n by omega) Sd
  rw [hSd_a1, hSd_b1, hSd_c1] at h_ep_raw
  have h_ep : xAt Sd n + yAt Sd n + 2 * zAt Sd n = 0 := by linarith
  by_cases h_both_neg : xAt Sd n = -1 ∧ yAt Sd n = -1
  · obtain ⟨ha_neg, hb_neg⟩ := h_both_neg
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
  · have h_last : xAt Sd n = 1 ∧ yAt Sd n = 1 := by
      rcases ha_n_pm with ha_n | ha_n <;> rcases hb_n_pm with hb_n | hb_n <;>
          rcases hc_n_pm with hc_n | hc_n
      · rw [ha_n, hb_n, hc_n] at h_ep; norm_num at h_ep
      · exact ⟨ha_n, hb_n⟩
      · rw [ha_n, hb_n, hc_n] at h_ep; norm_num at h_ep
      · rw [ha_n, hb_n, hc_n] at h_ep; norm_num at h_ep
      · rw [ha_n, hb_n, hc_n] at h_ep; norm_num at h_ep
      · rw [ha_n, hb_n, hc_n] at h_ep; norm_num at h_ep
      · exact absurd ⟨ha_n, hb_n⟩ h_both_neg
      · rw [ha_n, hb_n, hc_n] at h_ep; norm_num at h_ep
    exact ⟨Sd, hS_Sd, hSd_a1, h_last.1, hSd_b1, h_last.2, hSd_c1, hSd_d1⟩

/-! ### Private helpers for step2 -/

private lemma xAt_revA_eq {n : Nat} (S : TurynType n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    xAt S.doRevX j = xAt S (n + 1 - j) := by
  simp only [xAt, TurynType.doRevX, PmSeq.reverse_data]
  rw [lookupNat_reverseFn S.X.data (j - 1) (by omega)]
  congr 1; omega

private lemma xAt_revA_mirror {n : Nat} (S : TurynType n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    xAt S.doRevX (n + 1 - j) = xAt S j := by
  rw [xAt_revA_eq S (by omega : 1 ≤ n + 1 - j) (by omega : n + 1 - j ≤ n)]
  congr 1; omega

private lemma xAt_pm_A {n : Nat} (S : TurynType n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    xAt S j = 1 ∨ xAt S j = -1 :=
  pm_lookupNat S.X.pm (by omega)

private lemma canonical1_doRevX {n : Nat} (hn : 2 ≤ n) (S : TurynType n)
    (h1 : Canonical1 n S) : Canonical1 n S.doRevX := by
  unfold Canonical1 at *
  obtain ⟨ha1, han, hb1, hbn, hc1, hd1⟩ := h1
  exact ⟨by rw [xAt_revA_eq S (by omega) (by omega), show n + 1 - 1 = n from by omega]; exact han,
         by rw [xAt_revA_eq S (by omega) le_rfl, show n + 1 - n = 1 from by omega]; exact ha1,
         hb1, hbn, hc1, hd1⟩

/-- Step 2: enforce condition (2) by optional reversal of `A`. -/
theorem step2_condition2
    (n : Nat) (hn : 2 ≤ n) (S : TurynType n)
    (h1 : Canonical1 n S) :
    ∃ S2 : TurynType n, Equivalent n S S2 ∧ Canonical1 n S2 ∧ Canonical2 n S2 := by
  by_contra h_neg
  obtain ⟨i, hi_lb, hi_ub, hi_sym, hi_neq, hi_val⟩ :
      ∃ i, 1 ≤ i ∧ i ≤ n ∧
        (∀ j, 1 ≤ j → j < i → xAt S j = xAt S (n + 1 - j)) ∧
        xAt S i ≠ xAt S (n + 1 - i) ∧ xAt S i = -1 := by
    by_contra h_no_witness
    push_neg at h_no_witness
    exact h_neg ⟨S, Relation.ReflTransGen.refl, h1, fun j hj1 hj2 hj3 hj4 =>
      (xAt_pm_A S hj1 hj2).resolve_right (h_no_witness j hj1 hj2 hj3 hj4)⟩
  exact h_neg ⟨S.doRevX, Relation.ReflTransGen.single (Elementary.revX S),
    canonical1_doRevX hn S h1, fun j hj1 hj2 hj3 hj4 => by
      have h_fwd : xAt S.doRevX j = xAt S (n + 1 - j) := xAt_revA_eq S hj1 hj2
      have h_bwd : xAt S.doRevX (n + 1 - j) = xAt S j := xAt_revA_mirror S hj1 hj2
      rcases lt_trichotomy j i with hjlt | hjeq | hjgt
      · have hsym : xAt S j = xAt S (n + 1 - j) := hi_sym j hj1 hjlt
        rw [h_fwd, h_bwd] at hj4
        exact absurd hsym.symm hj4
      · subst hjeq
        rw [h_fwd]
        have h_mirror_pm := xAt_pm_A S (by omega : 1 ≤ n + 1 - j) (by omega : n + 1 - j ≤ n)
        rcases h_mirror_pm with h_one | h_neg1
        · exact h_one
        · exact absurd (show xAt S j = xAt S (n + 1 - j) by rw [hi_val, h_neg1]) hi_neq
      · have h_sym_i : xAt S.doRevX i = xAt S.doRevX (n + 1 - i) := hj3 i hi_lb hjgt
        rw [xAt_revA_eq S hi_lb hi_ub, xAt_revA_mirror S hi_lb hi_ub] at h_sym_i
        exact absurd h_sym_i.symm hi_neq⟩

/-! ### Reversal accessor lemmas -/

lemma yAt_doRevY_at {n : Nat} (S : TurynType n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    yAt S.doRevY j = yAt S (n + 1 - j) := by
  simp only [yAt, TurynType.doRevY, PmSeq.reverse_data]
  rw [lookupNat_reverseFn S.Y.data (j - 1) (by omega)]
  congr 1; omega

lemma yAt_doRevY_mirror {n : Nat} (S : TurynType n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    yAt S.doRevY (n + 1 - j) = yAt S j := by
  rw [yAt_doRevY_at S (by omega) (by omega)]
  congr 1; omega

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
  by_cases hB : ∃ i, 1 ≤ i ∧ i ≤ n ∧
      (∀ j, 1 ≤ j → j < i → yAt S j = yAt S (n + 1 - j)) ∧
      yAt S i ≠ yAt S (n + 1 - i) ∧ yAt S i = -1
  · rcases hB with ⟨i, hi1, hi2, hsym, hasym, hval⟩
    refine ⟨S.doRevY, ?_, ?_, ?_, ?_⟩
    · exact Relation.ReflTransGen.single (Elementary.revY S)
    · have hc1 := h12.1
      unfold Canonical1 at hc1 ⊢
      rcases hc1 with ⟨ha1, han, hb1, hbn, hc1v, hd1⟩
      exact ⟨by rw [xAt_doRevY]; exact ha1,
             by rw [xAt_doRevY]; exact han,
             by rw [yAt_doRevY_at S (by omega) (by omega), show n + 1 - 1 = n from by omega]; exact hbn,
             by rw [yAt_doRevY_at S (by omega) le_rfl, show n + 1 - n = 1 from by omega]; exact hb1,
             by rw [zAt_doRevY]; exact hc1v,
             by rw [wAt_doRevY]; exact hd1⟩
    · intro j hj1 hj2 hj3 hj4
      have hj3' : ∀ k, 1 ≤ k → k < j → xAt S k = xAt S (n + 1 - k) := by
        intro k hk1 hk2
        have := hj3 k hk1 hk2
        rw [xAt_doRevY, xAt_doRevY] at this
        exact this
      have hj4' : xAt S j ≠ xAt S (n + 1 - j) := by
        rw [← xAt_doRevY S j, ← xAt_doRevY S (n + 1 - j)]; exact hj4
      rw [xAt_doRevY]
      exact h12.2 j hj1 hj2 hj3' hj4'
    · intro j hj1 hj2 hj3 hj4
      have hrev_j : yAt S.doRevY j = yAt S (n + 1 - j) :=
        yAt_doRevY_at S hj1 hj2
      have hrev_mirror : yAt S.doRevY (n + 1 - j) = yAt S j :=
        yAt_doRevY_mirror S hj1 hj2
      have hsym_S : ∀ k, 1 ≤ k → k < j → yAt S k = yAt S (n + 1 - k) := by
        intro k hk1 hk2
        have hk2n : k ≤ n := le_trans (le_of_lt hk2) hj2
        have := hj3 k hk1 hk2
        rw [yAt_doRevY_at S hk1 hk2n, yAt_doRevY_mirror S hk1 hk2n] at this
        exact this.symm
      have hasym_S : yAt S j ≠ yAt S (n + 1 - j) := by
        intro heq; exact hj4 (by rw [hrev_j, hrev_mirror]; exact heq.symm)
      have hpm : yAt S (n + 1 - j) = 1 ∨ yAt S (n + 1 - j) = -1 :=
        pm_lookupNat S.Y.pm (by omega)
      have hpm_j : yAt S j = 1 ∨ yAt S j = -1 :=
        pm_lookupNat S.Y.pm (by omega)
      rw [hrev_j]
      rcases hpm_j with hj_one | hj_neg
      · exfalso
        by_cases hjle : j < i
        · exact hasym_S (hsym j hj1 hjle)
        · by_cases hjeq : j = i
          · rw [hjeq] at hj_one; linarith [hval]
          · exact hasym (hsym_S i hi1 (by omega))
      · rcases hpm with hm_one | hm_neg
        · exact hm_one
        · exfalso; exact hasym_S (by rw [hj_neg, hm_neg])
  · refine ⟨S, Relation.ReflTransGen.refl, h12.1, h12.2, ?_⟩
    intro i hi1 hi2 hi3 hi4
    have hpm : yAt S i = 1 ∨ yAt S i = -1 :=
      pm_lookupNat S.Y.pm (by omega)
    rcases hpm with h_one | h_neg
    · exact h_one
    · exfalso; exact hB ⟨i, hi1, hi2, hi3, hi4, h_neg⟩

/-! ### Step 4 helpers -/

private lemma zAt_doNegRevZ {n : Nat} (S : TurynType n)
    {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    zAt S.doRevZ.doNegZ j = -(zAt S (n + 1 - j)) := by
  simp only [zAt, TurynType.doNegZ, TurynType.doRevZ, PmSeq.neg_data, PmSeq.reverse_data,
             lookupNat_negSeqFn]
  rw [lookupNat_reverseFn S.Z.data (j - 1) (by omega)]
  show -lookupNat S.Z.data (n - 1 - (j - 1)) = -lookupNat S.Z.data (n + 1 - j - 1)
  congr 2; omega

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
  · obtain ⟨i, hi1, hi2, hi3, hi4, hi5⟩ := h_exists
    refine ⟨S.doRevZ.doNegZ, ?_, ?_, h123.2.1, h123.2.2, ?_⟩
    · exact (Relation.ReflTransGen.single (Elementary.revZ S)).trans
        (Relation.ReflTransGen.single (Elementary.negZ S.doRevZ))
    · have hcn : zAt S n = -1 := lemma1_endpoint_constraint n (by omega) S h123.1
      unfold Canonical1 at *
      obtain ⟨ha1, han, hb1, hbn, _, hd1⟩ := h123.1
      refine ⟨ha1, han, hb1, hbn, ?_, hd1⟩
      rw [zAt_doNegRevZ S (by omega) (by omega)]
      rw [show n + 1 - 1 = n from by omega, hcn]; norm_num
    · intro j hj1 hj2 hj3 hj4
      have hj3' : ∀ j', 1 ≤ j' → j' < j → zAt S j' ≠ zAt S (n + 1 - j') := by
        intro j' hj'1 hj'2
        have h := hj3 j' hj'1 hj'2
        rw [zAt_doNegRevZ S hj'1 (by omega),
            zAt_doNegRevZ S (by omega : 1 ≤ n + 1 - j') (by omega)] at h
        intro heq; apply h
        have : n + 1 - (n + 1 - j') = j' := by omega
        rw [this]; linarith
      have hj4' : zAt S j = zAt S (n + 1 - j) := by
        rw [zAt_doNegRevZ S hj1 hj2,
            zAt_doNegRevZ S (by omega : 1 ≤ n + 1 - j) (by omega)] at hj4
        have : n + 1 - (n + 1 - j) = j := by omega
        rw [this] at hj4; linarith
      have hji : j ≤ i := by
        by_contra h; exact hj3' i hi1 (by omega) hi4
      have hij : i ≤ j := by
        by_contra h; exact hi3 j hj1 (by omega) hj4'
      have heq : j = i := by omega
      subst heq
      rw [zAt_doNegRevZ S hj1 hj2, ← hi4, hi5]; norm_num
  · refine ⟨S, Relation.ReflTransGen.refl, h123.1, h123.2.1, h123.2.2, ?_⟩
    intro i hi1 hi2 hi3 hi4
    rcases pm_lookupNat S.Z.pm (by omega : i - 1 < n) with h | h
    · exact h
    · exfalso; exact h_exists ⟨i, hi1, hi2, hi3, hi4, h⟩

/-! ### Step 5 helpers -/

private lemma wAt_doRevW {n : Nat} (S : TurynType n) {j : Nat} (hj1 : 1 ≤ j) (hj2 : j ≤ n - 1) :
    wAt S.doRevW j = wAt S (n - j) := by
  simp only [wAt, TurynType.doRevW, PmSeq.reverse_data]
  rw [lookupNat_reverseFn S.W.data (j - 1) (by omega)]
  congr 1; omega

private lemma wAt_doRevW_mirror {n : Nat} (S : TurynType n) {j : Nat}
    (hj1 : 1 ≤ j) (hj2 : j ≤ n - 1) :
    wAt S.doRevW (n - j) = wAt S j := by
  rw [wAt_doRevW S (by omega : 1 ≤ n - j) (by omega : n - j ≤ n - 1)]
  congr 1; omega

private lemma wAt_doNegRevW {n : Nat} (S : TurynType n) {j : Nat}
    (hj1 : 1 ≤ j) (hj2 : j ≤ n - 1) :
    wAt (TurynType.doNegW S.doRevW) j = -(wAt S (n - j)) := by
  simp only [wAt, TurynType.doNegW, TurynType.doRevW, PmSeq.neg_data, PmSeq.reverse_data,
             lookupNat_negSeqFn]
  rw [lookupNat_reverseFn S.W.data (j - 1) (by omega)]
  show -lookupNat S.W.data (n - 1 - 1 - (j - 1)) = -lookupNat S.W.data (n - j - 1)
  congr 2; omega

private lemma wAt_doNegRevW_mirror {n : Nat} (S : TurynType n) {j : Nat}
    (hj1 : 1 ≤ j) (hj2 : j ≤ n - 1) :
    wAt (TurynType.doNegW S.doRevW) (n - j) = -(wAt S j) := by
  rw [wAt_doNegRevW S (by omega : 1 ≤ n - j) (by omega : n - j ≤ n - 1)]
  show -(wAt S (n - (n - j))) = -(wAt S j)
  congr 1; unfold wAt; congr 1; omega

private lemma wAt_pm' {n : Nat} (S : TurynType n) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ n - 1) :
    wAt S i = 1 ∨ wAt S i = -1 :=
  pm_lookupNat S.W.pm (by omega)

private lemma wAt_doRevW_n1 {n : Nat} (S : TurynType n) (hn : 2 ≤ n) :
    wAt S.doRevW (n - 1) = wAt S 1 := by
  rw [wAt_doRevW S (by omega) le_rfl]
  congr 1; omega

private lemma wAt_doNegRevW_n1 {n : Nat} (S : TurynType n) (hn : 2 ≤ n) :
    wAt (TurynType.doNegW S.doRevW) (n - 1) = -(wAt S 1) := by
  rw [wAt_doNegRevW S (by omega : 1 ≤ n - 1) le_rfl]
  show -(wAt S (n - (n - 1))) = -(wAt S 1)
  congr 1; unfold wAt; congr 1; omega

private lemma doRevW_product_eq {n : Nat} (S : TurynType n) {k : Nat}
    (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1) :
    wAt S.doRevW k * wAt S.doRevW (n - k) = wAt S k * wAt S (n - k) := by
  rw [wAt_doRevW S hk1 hk2, wAt_doRevW_mirror S hk1 hk2]; ring

private lemma doNegRevW_product_eq {n : Nat} (S : TurynType n) {k : Nat}
    (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1) :
    wAt (TurynType.doNegW S.doRevW) k *
      wAt (TurynType.doNegW S.doRevW) (n - k) =
    wAt S k * wAt S (n - k) := by
  rw [wAt_doNegRevW S hk1 hk2, wAt_doNegRevW_mirror S hk1 hk2]; ring

/-- Step 5: enforce condition (5) by optional `D*` or `−D*`. -/
theorem step5_condition5
    (n : Nat) (hn : 2 ≤ n) (S : TurynType n)
    (h1234 : Canonical1 n S ∧ Canonical2 n S ∧ Canonical3 n S ∧ Canonical4 n S) :
    ∃ S5 : TurynType n,
      Equivalent n S S5 ∧
      Canonical1 n S5 ∧ Canonical2 n S5 ∧ Canonical3 n S5 ∧
      Canonical4 n S5 ∧ Canonical5 n S5 := by
  by_cases h5 : Canonical5 n S
  · exact ⟨S, Relation.ReflTransGen.refl, h1234.1, h1234.2.1, h1234.2.2.1, h1234.2.2.2, h5⟩
  · unfold Canonical5 at h5
    push_neg at h5
    obtain ⟨i, hi1, hi2, hi3, hi4, hi5⟩ := h5
    have hdS1 : wAt S 1 = 1 := h1234.1.2.2.2.2.2
    by_cases h_case : wAt S (n - 1) = 1
    · refine ⟨S.doRevW, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact Relation.ReflTransGen.single (Elementary.revW S)
      · exact ⟨h1234.1.1, h1234.1.2.1, h1234.1.2.2.1, h1234.1.2.2.2.1, h1234.1.2.2.2.2.1,
               by rw [wAt_doRevW S (by omega) (by omega)]; exact h_case⟩
      · exact h1234.2.1
      · exact h1234.2.2.1
      · exact h1234.2.2.2
      · intro j hj1 hj2 hj3 hj4
        rw [doRevW_product_eq S hj1 hj2, wAt_doRevW_n1 S hn, hdS1] at hj4
        rw [wAt_doRevW S hj1 hj2]
        by_cases hji_lt : j < i
        · have := hi3 j hj1 hji_lt
          rw [h_case] at this
          exact absurd this hj4
        · by_cases hji_eq : j = i
          · subst hji_eq
            have hdi_neg : wAt S j = -1 := by
              rcases wAt_pm' S hj1 hj2 with h | h
              · exact absurd h hi5
              · exact h
            rcases wAt_pm' S (by omega : 1 ≤ n - j) (by omega : n - j ≤ n - 1) with h | h
            · exact h
            · exfalso; apply hj4; rw [hdi_neg, h]; norm_num
          · have hji_gt : i < j := by omega
            have hk_eq := hj3 i hi1 hji_gt
            rw [doRevW_product_eq S hi1 hi2, wAt_doRevW_n1 S hn, hdS1] at hk_eq
            rw [h_case] at hi4
            exact absurd hk_eq hi4
    · have h_neg : wAt S (n - 1) = -1 := by
        rcases wAt_pm' S (by omega) le_rfl with h | h
        · exact absurd h h_case
        · exact h
      refine ⟨TurynType.doNegW S.doRevW, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single (Elementary.revW S))
          (Relation.ReflTransGen.single (Elementary.negW _))
      · refine ⟨h1234.1.1, h1234.1.2.1, h1234.1.2.2.1, h1234.1.2.2.2.1, h1234.1.2.2.2.2.1, ?_⟩
        rw [wAt_doNegRevW S (by omega) (by omega)]
        rw [show n - 1 = n - 1 from rfl]
        rw [h_neg]; norm_num
      · exact h1234.2.1
      · exact h1234.2.2.1
      · exact h1234.2.2.2
      · intro j hj1 hj2 hj3 hj4
        rw [doNegRevW_product_eq S hj1 hj2, wAt_doNegRevW_n1 S hn, hdS1] at hj4
        have hj4' : wAt S j * wAt S (n - j) ≠ -1 := by norm_num at hj4 ⊢; exact hj4
        rw [wAt_doNegRevW S hj1 hj2]
        by_cases hji_lt : j < i
        · have := hi3 j hj1 hji_lt
          rw [h_neg] at this
          exact absurd this hj4'
        · by_cases hji_eq : j = i
          · subst hji_eq
            have hdi_neg : wAt S j = -1 := by
              rcases wAt_pm' S hj1 hj2 with h | h
              · exact absurd h hi5
              · exact h
            rcases wAt_pm' S (by omega : 1 ≤ n - j) (by omega : n - j ≤ n - 1) with h | h
            · exfalso; apply hj4'; rw [hdi_neg, h]; norm_num
            · rw [h]; norm_num
          · have hji_gt : i < j := by omega
            have hk_eq := hj3 i hi1 hji_gt
            rw [doNegRevW_product_eq S hi1 hi2, wAt_doNegRevW_n1 S hn, hdS1] at hk_eq
            rw [h_neg] at hi4
            have hk_eq' : wAt S i * wAt S (n - i) = -1 := by linarith
            exact absurd hk_eq' hi4

/-! ### Helper lemmas for step 6 -/

private lemma doSwap_xAt {n : Nat} (S : TurynType n) (i : Nat) :
    xAt S.doSwap i = yAt S i := rfl

private lemma doSwap_yAt {n : Nat} (S : TurynType n) (i : Nat) :
    yAt S.doSwap i = xAt S i := rfl

private lemma doSwap_zAt {n : Nat} (S : TurynType n) (i : Nat) :
    zAt S.doSwap i = zAt S i := rfl

private lemma doSwap_wAt {n : Nat} (S : TurynType n) (i : Nat) :
    wAt S.doSwap i = wAt S i := rfl

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
  exact h3 i hi₁ hi₂ hi₃ hi₄

private lemma canonical3_doSwap_of_canonical2 {n : Nat} {S : TurynType n}
    (h2 : Canonical2 n S) : Canonical3 n S.doSwap := by
  intro i hi₁ hi₂ hi₃ hi₄
  exact h2 i hi₁ hi₂ hi₃ hi₄

private lemma canonical4_doSwap {n : Nat} {S : TurynType n}
    (h4 : Canonical4 n S) : Canonical4 n S.doSwap := by
  intro i hi₁ hi₂ hi₃ hi₄
  have hi₃' : ∀ j, 1 ≤ j → j < i → zAt S j ≠ zAt S (n + 1 - j) := fun j hj₁ hj₂ => hi₃ j hj₁ hj₂
  have hi₄' : zAt S i = zAt S (n + 1 - i) := hi₄
  exact h4 i hi₁ hi₂ hi₃' hi₄'

private lemma canonical5_doSwap {n : Nat} {S : TurynType n}
    (h5 : Canonical5 n S) : Canonical5 n S.doSwap := by
  intro i hi₁ hi₂ hi₃ hi₄
  have hi₃' : ∀ j, 1 ≤ j → j < i → wAt S j * wAt S (n - j) = wAt S (n - 1) :=
    fun j hj₁ hj₂ => hi₃ j hj₁ hj₂
  have hi₄' : wAt S i * wAt S (n - i) ≠ wAt S (n - 1) := hi₄
  exact h5 i hi₁ hi₂ hi₃' hi₄'

private lemma step6_xAt_pm {n : Nat} (S : TurynType n) (i : Nat) (hi : i - 1 < n) :
    xAt S i = 1 ∨ xAt S i = -1 :=
  pm_lookupNat S.X.pm hi

private lemma step6_yAt_pm {n : Nat} (S : TurynType n) (i : Nat) (hi : i - 1 < n) :
    yAt S i = 1 ∨ yAt S i = -1 :=
  pm_lookupNat S.Y.pm hi

private lemma step6_zAt_pm {n : Nat} (S : TurynType n) (i : Nat) (hi : i - 1 < n) :
    zAt S i = 1 ∨ zAt S i = -1 :=
  pm_lookupNat S.Z.pm hi

private lemma step6_wAt_pm {n : Nat} (S : TurynType n) (i : Nat) (hi : i - 1 < n - 1) :
    wAt S i = 1 ∨ wAt S i = -1 :=
  pm_lookupNat S.W.pm hi

/-! ### Autocorrelation expansion helpers -/

private lemma autocorr_two_terms {n : Nat} (a : Fin n → Int) (m : Nat) (hlen : n = m + 2) :
    aperiodicAutocorr a m = lookupNat a 0 * lookupNat a m +
      lookupNat a 1 * lookupNat a (m + 1) := by
  unfold aperiodicAutocorr
  rw [if_neg (by omega), show n - m = 2 from by omega]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  ring_nf

private lemma autocorr_one_term {n : Nat} (a : Fin n → Int) (m : Nat) (hlen : n = m + 1) :
    aperiodicAutocorr a m = lookupNat a 0 * lookupNat a m := by
  unfold aperiodicAutocorr
  rw [if_neg (by omega), show n - m = 1 from by omega]
  rw [Finset.sum_range_succ, Finset.sum_range_zero]
  ring_nf

private lemma step6_autocorr_lag_n_sub_2
    (n : Nat) (hn3 : 3 ≤ n) (S : TurynType n)
    (h1 : Canonical1 n S) :
    xAt S (n - 1) + xAt S 2 + (yAt S (n - 1) + yAt S 2) +
    2 * (zAt S (n - 1) + zAt S 2 * zAt S n) +
    2 * wAt S (n - 1) = 0 := by
  have hv := S.vanishing (n - 2) (by omega) (by omega)
  unfold combinedAutocorr at hv
  rw [autocorr_two_terms S.X.data (n - 2) (by omega),
      autocorr_two_terms S.Y.data (n - 2) (by omega),
      autocorr_two_terms S.Z.data (n - 2) (by omega),
      autocorr_one_term S.W.data (n - 2) (by omega)] at hv
  have h_a0 : lookupNat S.X.data 0 = 1 := by
    have := h1.1; unfold xAt at this; simpa using this
  have h_an1 : lookupNat S.X.data (n - 1) = 1 := by
    have := h1.2.1; unfold xAt at this; simpa using this
  have h_b0 : lookupNat S.Y.data 0 = 1 := by
    have := h1.2.2.1; unfold yAt at this; simpa using this
  have h_bn1 : lookupNat S.Y.data (n - 1) = 1 := by
    have := h1.2.2.2.1; unfold yAt at this; simpa using this
  have h_c0 : lookupNat S.Z.data 0 = 1 := by
    have := h1.2.2.2.2.1; unfold zAt at this; simpa using this
  have h_d0 : lookupNat S.W.data 0 = 1 := by
    have := h1.2.2.2.2.2; unfold wAt at this; simpa using this
  have hn21 : n - 2 + 1 = n - 1 := by omega
  rw [hn21] at hv
  rw [h_a0, h_an1, h_b0, h_bn1, h_c0, h_d0] at hv
  unfold xAt yAt zAt wAt
  simp only [show 2 - 1 = 1 from rfl, show (n - 1) - 1 = n - 2 from by omega]
  linarith

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
  by_cases hn3 : 3 ≤ n
  · have h_sum : xAt S (n - 1) + yAt S (n - 1) + 2 * xAt S 2 + 2 * zAt S (n - 1) +
        2 * (zAt S 2 * zAt S n) + 2 * wAt S (n - 1) = 0 := by
      convert step6_autocorr_lag_n_sub_2 n hn3 S h1 using 1; rw [h_eq]; ring
    have hab0 := step6_sum_forces_zero
      (xAt S (n - 1)) (yAt S (n - 1)) (xAt S 2) (zAt S (n - 1))
      (wAt S (n - 1)) (zAt S 2 * zAt S n)
      (step6_xAt_pm S (n - 1) (by omega))
      (step6_yAt_pm S (n - 1) (by omega))
      (step6_xAt_pm S 2 (by omega))
      (step6_zAt_pm S (n - 1) (by omega))
      (by rcases step6_zAt_pm S 2 (by omega) with h | h <;>
          rcases step6_zAt_pm S n (by omega) with j | j <;> simp [h, j])
      (step6_wAt_pm S (n - 1) (by omega))
      h_sum
    rcases step6_xAt_pm S (n - 1) (by omega) with ha1 | ha_neg1
    · exact Or.inr (Or.inl ⟨ha1, by linarith⟩)
    · exact Or.inr (Or.inr ⟨ha_neg1, by linarith⟩)
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
  by_cases h_neq : xAt S 2 ≠ yAt S 2
  · rcases step6_xAt_pm S 2 (by omega) with h_a2_1 | h_a2_neg1
    · exact ⟨S, Relation.ReflTransGen.refl, h1, h2, h3, h4, h5,
             Or.inr (Or.inl ⟨h_neq, h_a2_1⟩)⟩
    · have h_b2 : yAt S 2 = 1 := by
        rcases step6_yAt_pm S 2 (by omega) with h | h
        · exact h
        · exfalso; exact h_neq (by rw [h_a2_neg1, h])
      refine ⟨S.doSwap, Relation.ReflTransGen.single (Elementary.swap S),
              canonical1_doSwap h1,
              canonical2_doSwap_of_canonical3 h3,
              canonical3_doSwap_of_canonical2 h2,
              canonical4_doSwap h4,
              canonical5_doSwap h5,
              ?_⟩
      unfold Canonical6
      right; left
      exact ⟨by rw [doSwap_xAt, doSwap_yAt]; exact fun h => h_neq h.symm,
             by rw [doSwap_xAt]; exact h_b2⟩
  · push_neg at h_neq
    rcases step6_opposite_signs n hn_even hn S h1 h_neq with h_le2 | ⟨ha_pos, hb_neg⟩ | ⟨ha_neg, hb_pos⟩
    · exact ⟨S, Relation.ReflTransGen.refl, h1, h2, h3, h4, h5, Or.inl h_le2⟩
    · exact ⟨S, Relation.ReflTransGen.refl, h1, h2, h3, h4, h5,
             Or.inr (Or.inr ⟨h_neq, ha_pos, hb_neg⟩)⟩
    · refine ⟨S.doSwap, Relation.ReflTransGen.single (Elementary.swap S),
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
