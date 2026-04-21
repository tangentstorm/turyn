import Turyn.Equivalence
import Turyn.PmSum

namespace Turyn

/-- Product of A and B entries at 1-indexed position `i`. -/
def uAt {n : Nat} (S : TurynTypeSeq n) (i : Nat) : Int := aAt S i * bAt S i

/-- `uAt S i` is ±1 for valid indices. -/
lemma uAt_pm {n : Nat} (S : TurynTypeSeq n) (i : Nat) (hi1 : 1 ≤ i) (hi2 : i ≤ n) :
    uAt S i = 1 ∨ uAt S i = -1 := by
  unfold uAt aAt bAt
  have hAlen := S.isTuryn.x_len
  have hBlen := S.isTuryn.y_len
  have hiA : i - 1 < S.A.length := by omega
  have hiB : i - 1 < S.B.length := by omega
  have ha := pm_entry_of_getD S.isTuryn.x_pm hiA
  have hb := pm_entry_of_getD S.isTuryn.y_pm hiB
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    · rw [ha, hb]; decide

/-- Under `Canonical1`, the first entry of `u` is 1. -/
lemma uAt_one_of_canonical1_head {n : Nat} {S : TurynTypeSeq n}
    (hc : Canonical1 n S) : uAt S 1 = 1 := by
  unfold uAt
  have ha1 := hc.1
  have hb1 := hc.2.2.1
  rw [ha1, hb1]; ring

/-- Under `Canonical1`, the last entry of `u` is 1. -/
lemma uAt_one_of_canonical1_tail {n : Nat} {S : TurynTypeSeq n}
    (_hn : 1 ≤ n) (hc : Canonical1 n S) : uAt S n = 1 := by
  unfold uAt
  have han := hc.2.1
  have hbn := hc.2.2.2.1
  rw [han, hbn]; ring

/-- `uAt S i` squares to 1 for valid indices. -/
lemma uAt_sq {n : Nat} (S : TurynTypeSeq n) (i : Nat) (hi1 : 1 ≤ i) (hi2 : i ≤ n) :
    uAt S i * uAt S i = 1 := by
  have h := uAt_pm S i hi1 hi2
  rcases h with h | h <;> rw [h] <;> ring

theorem aperiodicAutocorr_A_via_aAt {n : Nat} (S : TurynTypeSeq n) (s : Nat) (hs : s < n) :
    aperiodicAutocorr S.A s = ∑ i ∈ Finset.range (n - s), aAt S (i + 1) * aAt S (i + 1 + s) := by
  unfold aperiodicAutocorr
  rw [if_neg (by rw [S.isTuryn.x_len]; omega)]
  rw [show S.A.length - s = n - s from by rw [S.isTuryn.x_len]]
  apply Finset.sum_congr rfl
  intro i _
  unfold aAt
  simp

theorem aperiodicAutocorr_B_via_aAt {n : Nat} (S : TurynTypeSeq n) (s : Nat) (hs : s < n) :
    aperiodicAutocorr S.B s = ∑ i ∈ Finset.range (n - s), bAt S (i + 1) * bAt S (i + 1 + s) := by
  unfold aperiodicAutocorr
  rw [if_neg (by rw [S.isTuryn.y_len]; omega)]
  rw [show S.B.length - s = n - s from by rw [S.isTuryn.y_len]]
  apply Finset.sum_congr rfl
  intro i _
  unfold bAt
  simp

lemma aAt_sq {n : Nat} (S : TurynTypeSeq n) (i : Nat) (hi1 : 1 ≤ i) (hi2 : i ≤ n) :
    aAt S i * aAt S i = 1 := by
      -- Apply the lemma that states the product of a number with itself is 1 if the number is either 1 or -1.
      have h_sq : aAt S i = 1 ∨ aAt S i = -1 := by
        apply pm_entry_of_getD; exact S.isTuryn.x_pm; exact (by
        rw [ S.isTuryn.x_len ] ; omega)
      exact h_sq.elim (fun h => by rw [h]; norm_num) (fun h => by rw [h]; norm_num)

lemma bAt_eq_aAt_mul_uAt {n : Nat} (S : TurynTypeSeq n) (i : Nat)
    (hi1 : 1 ≤ i) (hi2 : i ≤ n) :
    bAt S i = aAt S i * uAt S i := by
      unfold uAt;
      rw [ ← mul_assoc, aAt_sq S i hi1 hi2, one_mul ]

private lemma summand_identity {n : Nat} (S : TurynTypeSeq n) (i : Nat)
    (hi1 : 1 ≤ i) (hi2 : i ≤ n) (j : Nat) (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    aAt S i * aAt S j + bAt S i * bAt S j =
    aAt S i * aAt S j * (1 + uAt S i * uAt S j) := by
      -- Apply the lemma to rewrite the bAt terms in the LHS.
      have h_lhs_rewrite : aAt S i * aAt S j + bAt S i * bAt S j = aAt S i * aAt S j + (aAt S i * aAt S j) * (aAt S i * aAt S i) * (uAt S i * uAt S j) := by
        rw [ bAt_eq_aAt_mul_uAt, bAt_eq_aAt_mul_uAt ];
        · rw [ show aAt S i * aAt S i = 1 by exact aAt_sq S i hi1 hi2 ] ; ring;
        · linarith;
        · lia;
        · linarith;
        · linarith;
      rw [ h_lhs_rewrite, aAt_sq S i hi1 hi2 ] ; ring

theorem T_k_as_U_sum {n : Nat} (S : TurynTypeSeq n) (k : Nat) (hk : 2 ≤ k) (hkn : k ≤ n - 1) :
    aperiodicAutocorr S.A (n - k) + aperiodicAutocorr S.B (n - k) =
    ∑ i ∈ Finset.range k,
      aAt S (i + 1) * aAt S (i + 1 + (n - k)) * (1 + uAt S (i + 1) * uAt S (i + 1 + (n - k))) := by
        have h1 : aperiodicAutocorr S.A (n - k) = ∑ i ∈ Finset.range k, aAt S (i + 1) * aAt S (i + 1 + (n - k)) := by
          convert aperiodicAutocorr_A_via_aAt S ( n - k ) _ using 1;
          · rw [ Nat.sub_sub_self ( by omega ) ];
          · omega
        have h2 : aperiodicAutocorr S.B (n - k) = ∑ i ∈ Finset.range k, bAt S (i + 1) * bAt S (i + 1 + (n - k)) := by
          convert aperiodicAutocorr_B_via_aAt S ( n - k ) _ using 1;
          · rw [ Nat.sub_sub_self ( by omega ) ];
          · omega;
        rw [ h1, h2, ← Finset.sum_add_distrib ];
        -- Apply the summand_identity to each term in the sum.
        apply Finset.sum_congr rfl
        intro i hi
        apply summand_identity;
        · linarith;
        · linarith [ Finset.mem_range.mp hi, Nat.sub_add_cancel ( show 1 ≤ n from by omega ) ];
        · omega;
        · linarith [ Finset.mem_range.mp hi, Nat.sub_add_cancel ( show k ≤ n from hkn.trans ( Nat.pred_le _ ) ) ]

/-! ### Parity-hammer helpers -/

/-
Each term of an autocorrelation of a ±1 sequence is itself ±1.
-/
lemma autocorr_term_pm {X : PmSeq} (hpm : AllPmOne X) {s : Nat} (hs : s < X.length)
    {i : Nat} (hi : i < X.length - s) :
    X.getD i 0 * X.getD (i + s) 0 = 1 ∨ X.getD i 0 * X.getD (i + s) 0 = -1 := by
  -- Since $X$ is a list of pm-ones, each element in $X$ is either 1 or -1.
  have h_getD : ∀ i, i < X.length → X.getD i 0 = 1 ∨ X.getD i 0 = -1 := by
    exact fun i a => pm_entry_of_getD hpm a
  grind

/-
Autocorrelation of a ±1 sequence mod 2 equals the number of summation terms mod 2.
-/
lemma autocorr_mod_two {X : PmSeq} (hpm : AllPmOne X) {s : Nat} (hs : s < X.length) :
    aperiodicAutocorr X s % 2 = ((X.length - s : Nat) : Int) % 2 := by
  convert sum_of_pm_ones_mod_two ( List.length X - s ) ( fun i => X.getD i 0 * X.getD ( i + s ) 0 ) _;
  · unfold aperiodicAutocorr; aesop;
  · exact fun i hi => autocorr_term_pm hpm hs ( Finset.mem_range.mp hi )

/-
From the vanishing condition: N_A(s) + N_B(s) = −2·(N_C(s) + N_D(s)).
-/
lemma AB_eq_neg2_CD {n : Nat} (S : TurynTypeSeq n) {s : Nat}
    (hs1 : 1 ≤ s) (hsn : s < n) :
    aperiodicAutocorr S.A s + aperiodicAutocorr S.B s =
    -2 * (aperiodicAutocorr S.C s + aperiodicAutocorr S.D s) := by
  have := S.isTuryn.vanishing s hs1 hsn;
  unfold combinedAutocorr at this; linarith;

/-
The sum N_C(s) + N_D(s) is odd for 1 ≤ s ≤ n − 2.
-/
lemma autocorr_CD_sum_odd {n : Nat} (S : TurynTypeSeq n) {s : Nat}
    (hs1 : 1 ≤ s) (hsn : s ≤ n - 2) :
    (aperiodicAutocorr S.C s + aperiodicAutocorr S.D s) % 2 = 1 := by
  -- Since $s \leq n - 2$, we have $s < n$.
  have hs_lt_n : s < n := by
    omega;
  -- Apply the autocorr_mod_two lemma to C and D.
  have hC : aperiodicAutocorr S.C s % 2 = ((S.C.length - s : Nat) : Int) % 2 := by
    apply autocorr_mod_two;
    · exact S.isTuryn.z_pm;
    · exact hs_lt_n.trans_le ( by linarith [ S.isTuryn.z_len ] )
  have hD : aperiodicAutocorr S.D s % 2 = ((S.D.length - s : Nat) : Int) % 2 := by
    apply autocorr_mod_two;
    · exact S.isTuryn.w_pm;
    · have := S.isTuryn.w_len; omega;
  norm_num [ Int.add_emod, hC, hD ];
  rw [ S.isTuryn.z_len, S.isTuryn.w_len ] ; omega;

/-
−2 times an odd integer is congruent to 2 modulo 4.
-/
lemma neg2_mul_odd_mod4 (m : Int) (hm : m % 2 = 1) : (-2 * m) % 4 = 2 := by
  omega

/-
**Parity hammer**: the sum N_A(n−k) + N_B(n−k) is congruent to 2 modulo 4
    for 2 ≤ k ≤ n − 1.  (Best–Đoković–Kharaghani–Ramp, arXiv:1206.4107)
-/
theorem parity_hammer {n : Nat} (S : TurynTypeSeq n) (k : Nat) (hk : 2 ≤ k) (hkn : k ≤ n - 1) :
    (aperiodicAutocorr S.A (n - k) + aperiodicAutocorr S.B (n - k)) % 4 = 2 := by
  -- Use AB_eq_neg2_CD S hs1 hsn to rewrite LHS as (-2 * (autocorr C s + autocorr D s)) % 4.
  have h_sum : (aperiodicAutocorr S.A (n - k) + aperiodicAutocorr S.B (n - k)) = -2 * (aperiodicAutocorr S.C (n - k) + aperiodicAutocorr S.D (n - k)) := by
    exact AB_eq_neg2_CD S ( Nat.sub_pos_of_lt ( by omega ) ) ( Nat.sub_lt ( by omega ) ( by omega ) );
  -- Use autocorr_CD_sum_odd S hs1 hsn2 to get (autocorr C s + autocorr D s) % 2 = 1.
  have h_odd : (aperiodicAutocorr S.C (n - k) + aperiodicAutocorr S.D (n - k)) % 2 = 1 := by
    apply autocorr_CD_sum_odd;
    · omega;
    · omega;
  omega

/-- aAt S i is ±1 for valid indices. -/
lemma aAt_pm {n : Nat} (S : TurynTypeSeq n) (i : Nat) (hi1 : 1 ≤ i) (hi2 : i ≤ n) :
    aAt S i = 1 ∨ aAt S i = -1 := by
  exact pm_entry_of_getD S.isTuryn.x_pm (by rw [S.isTuryn.x_len]; omega)

/-
Pure integer case analysis: if a₁, a₂, u₁, u₂ are all ±1 and
    a₁*(1+u₁) + a₂*(1+u₂) ≡ 2 (mod 4), then u₁ = -u₂.
-/
private lemma xy_base_common (a₁ a₂ u₁ u₂ : Int)
    (ha1 : a₁ = 1 ∨ a₁ = -1) (ha2 : a₂ = 1 ∨ a₂ = -1)
    (hu1 : u₁ = 1 ∨ u₁ = -1) (hu2 : u₂ = 1 ∨ u₂ = -1)
    (hmod : (a₁ * (1 + u₁) + a₂ * (1 + u₂)) % 4 = 2) :
    u₁ = -u₂ := by
  rcases ha1 with rfl | rfl <;> rcases ha2 with rfl | rfl <;>
    rcases hu1 with rfl | rfl <;> rcases hu2 with rfl | rfl <;> omega

theorem xy_base_k2 {n : Nat} (S : TurynTypeSeq n) (hn : 3 ≤ n)
    (hc : Canonical1 n S) : uAt S (n - 1) = -(uAt S 2) := by
      -- Apply the parity hammer lemma to get the congruence.
      have h_parity : (aAt S (n - 1) * (1 + uAt S (n - 1)) + aAt S 2 * (1 + uAt S 2)) % 4 = 2 := by
        have := parity_hammer S 2 ( by decide ) ( by omega ) ; ( rw [ T_k_as_U_sum S 2 ( by decide ) ( by omega ) ] at this; );
        rcases n with ( _ | _ | n ) <;> simp_all +decide [ Finset.sum_range_succ ];
        simp_all +decide [ add_comm 1, add_comm 2, uAt ];
        have := hc.1; have := hc.2.1; have := hc.2.2.1; have := hc.2.2.2.1; have := hc.2.2.2.2.1; have := hc.2.2.2.2.2; simp_all +decide [ aAt, bAt ] ;
      grind +suggestions

theorem xy_base_k3 {n : Nat} (S : TurynTypeSeq n) (hn : 4 ≤ n)
    (hc : Canonical1 n S) : uAt S (n - 2) = -(uAt S 3) := by
      -- Apply xy_base_common with the given conditions.
      apply xy_base_common (aAt S (n - 2)) (aAt S 3) (uAt S (n - 2)) (uAt S 3) (aAt_pm S (n - 2) (by omega) (by omega)) (aAt_pm S 3 (by omega) (by omega)) (uAt_pm S (n - 2) (by omega) (by omega)) (uAt_pm S 3 (by omega) (by omega));
      have hT3_mod4 : (aperiodicAutocorr S.A (n - 3) + aperiodicAutocorr S.B (n - 3)) % 4 = 2 := by
        apply parity_hammer S 3 (by omega) (by omega);
      convert hT3_mod4 using 1;
      rw [ Turyn.T_k_as_U_sum S 3 ( by omega ) ( by omega ) ] ; norm_num [ Finset.sum_range_succ ] ; ring;
      rw [ show 3 + ( n - 3 ) = n by omega, show 1 + ( n - 3 ) = n - 2 by omega, show 2 + ( n - 3 ) = n - 1 by omega ] ; ring;
      rw [ show aAt S 1 = 1 by exact hc.1, show aAt S n = 1 by exact hc.2.1, show uAt S 1 = 1 by exact uAt_one_of_canonical1_head hc, show uAt S n = 1 by exact uAt_one_of_canonical1_tail ( by linarith ) hc ] ; ring;
      rw [ show uAt S ( n - 1 ) = -uAt S 2 by exact xy_base_k2 S ( by omega ) hc ] ; ring;
      rw [ show uAt S 2 ^ 2 = 1 by rw [ sq, uAt_sq S 2 ( by linarith ) ( by omega ) ] ] ; ring

/-
Endpoint-pair mod-4 lemma: the expression
`aAt S (n+1-k) * (1 + uAt S (n+1-k)) + aAt S k * (1 + uAt S k)`
is congruent to 2 mod 4 if and only if the `u`-values at the two
endpoints are negatives of each other. This generalises the k = 2
base-case analysis to arbitrary k and is used by the main XY
induction step.
-/
lemma endpoint_pair_mod4 {n : Nat} (S : TurynTypeSeq n) (k : Nat)
    (hk : 2 ≤ k) (hkn : k ≤ n - 1) (_hc : Canonical1 n S) :
    (aAt S (n + 1 - k) * (1 + uAt S (n + 1 - k)) + aAt S k * (1 + uAt S k)) % 4 = 2 ↔
      uAt S (n + 1 - k) = -(uAt S k) := by
  -- Let's simplify the expression using the fact that `aAt` and `uAt` are ±1.
  have h_simp : ∀ i, 1 ≤ i → i ≤ n → aAt S i = 1 ∨ aAt S i = -1 := by
    exact fun i a a_1 => aAt_pm S i a a_1
  have h_simp_u : ∀ i, 1 ≤ i → i ≤ n → uAt S i = 1 ∨ uAt S i = -1 := by
    exact fun i a a_1 => uAt_pm S i a a_1
  grind

/--
Pure integer algebra: for ±1 values a₁, a₂, a₃, a₄, u₁, u₃,
the paired sum `a₁·a₂·(1 + u₁·(−u₃)) + a₃·a₄·(1 + u₃·(−u₁))` is divisible by 4.

This factors as `(1 − u₁·u₃)·(a₁·a₂ + a₃·a₄)`.
- `1 − u₁·u₃ ∈ {0, 2}` (product of two ±1's is ±1).
- `a₁·a₂ + a₃·a₄ ∈ {−2, 0, 2}` (sum of two ±1's).
So the product is always in `{0, ±4}`, hence divisible by 4.
-/
private lemma pm_pair_sum_mod4 (a1 a2 a3 a4 u1 u3 : Int)
    (ha1 : a1 = 1 ∨ a1 = -1) (ha2 : a2 = 1 ∨ a2 = -1)
    (ha3 : a3 = 1 ∨ a3 = -1) (ha4 : a4 = 1 ∨ a4 = -1)
    (hu1 : u1 = 1 ∨ u1 = -1) (hu3 : u3 = 1 ∨ u3 = -1) :
    (a1 * a2 * (1 + u1 * (-u3)) + a3 * a4 * (1 + u3 * (-u1))) % 4 = 0 := by
  rcases ha1 with rfl | rfl <;> rcases ha2 with rfl | rfl <;>
  rcases ha3 with rfl | rfl <;> rcases ha4 with rfl | rfl <;>
  rcases hu1 with rfl | rfl <;> rcases hu3 with rfl | rfl <;> decide

/--
**Interior-pair mod-4 lemma.**  The central induction-step ingredient for the
XY product-law proof.

Given the induction hypothesis `IH` (all mirrors up to index `k` are negated),
the paired contribution of prose positions `m` and `k+1−m` in `T_k`'s sum is
divisible by 4.

The proof rewrites the two "far" `uAt` values via `IH`, then closes by an
explicit 64-case split on the ±1 values.
-/
lemma interior_pair_mod4 {n : Nat} (S : TurynTypeSeq n) (k : Nat)
    (hk : 4 ≤ k) (hkn : k ≤ n - 1)
    (IH : ∀ j, 2 ≤ j → j < k → uAt S (n + 1 - j) = -(uAt S j))
    {m : Nat} (hm1 : 2 ≤ m) (hm2 : 2 * m ≤ k) (hm3 : m < k + 1 - m) :
    (aAt S m * aAt S (m + (n - k)) * (1 + uAt S m * uAt S (m + (n - k))) +
     aAt S (k + 1 - m) * aAt S ((k + 1 - m) + (n - k)) *
        (1 + uAt S (k + 1 - m) * uAt S ((k + 1 - m) + (n - k)))) % 4 = 0 := by
  -- Step 1: Establish the key index identities (Nat arithmetic).
  have hidx1 : m + (n - k) = n + 1 - (k + 1 - m) := by omega
  have hidx2 : (k + 1 - m) + (n - k) = n + 1 - m := by omega
  -- Step 2: Apply IH to rewrite the "far" uAt values.
  -- IH at j = k+1−m: uAt S (n+1−(k+1−m)) = −(uAt S (k+1−m)),
  --   i.e. uAt S (m+(n−k)) = −(uAt S (k+1−m)).
  have hih1 : uAt S (m + (n - k)) = -(uAt S (k + 1 - m)) := by
    rw [hidx1]
    exact IH (k + 1 - m) (by omega) (by omega)
  -- IH at j = m: uAt S (n+1−m) = −(uAt S m),
  --   i.e. uAt S ((k+1−m)+(n−k)) = −(uAt S m).
  have hih2 : uAt S ((k + 1 - m) + (n - k)) = -(uAt S m) := by
    rw [hidx2]
    exact IH m hm1 (by omega)
  -- Step 3: Substitute into the goal.
  rw [hih1, hih2]
  -- Step 4: Apply the pure-integer 64-case lemma.
  exact pm_pair_sum_mod4
    (aAt S m) (aAt S (m + (n - k)))
    (aAt S (k + 1 - m)) (aAt S ((k + 1 - m) + (n - k)))
    (uAt S m) (uAt S (k + 1 - m))
    (aAt_pm S m (by omega) (by omega))
    (aAt_pm S (m + (n - k)) (by omega) (by omega))
    (aAt_pm S (k + 1 - m) (by omega) (by omega))
    (aAt_pm S ((k + 1 - m) + (n - k)) (by omega) (by omega))
    (uAt_pm S m (by omega) (by omega))
    (uAt_pm S (k + 1 - m) (by omega) (by omega))

end Turyn
