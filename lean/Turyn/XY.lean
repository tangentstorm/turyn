import Turyn.Equivalence
import Turyn.PmSum

open Finset BigOperators

namespace Turyn

/-- `uAt S i` is ±1 for valid indices. -/
lemma uAt_pm {n : Nat} (S : TurynType n) (i : Nat) (hi1 : 1 ≤ i) (hi2 : i ≤ n) :
    uAt S i = 1 ∨ uAt S i = -1 := by
  unfold uAt xAt yAt
  have hiA : i - 1 < n := by omega
  have ha := pm_lookupNat S.X.pm hiA
  have hb := pm_lookupNat S.Y.pm hiA
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    · rw [ha, hb]; decide

/-- Under `Canonical1`, the first entry of `u` is 1. -/
lemma uAt_one_of_canonical1_head {n : Nat} {S : TurynType n}
    (hc : Canonical1 n S) : uAt S 1 = 1 := by
  unfold uAt
  have ha1 := hc.1
  have hb1 := hc.2.2.1
  rw [ha1, hb1]; ring

/-- Under `Canonical1`, the last entry of `u` is 1. -/
lemma uAt_one_of_canonical1_tail {n : Nat} {S : TurynType n}
    (_hn : 1 ≤ n) (hc : Canonical1 n S) : uAt S n = 1 := by
  unfold uAt
  have han := hc.2.1
  have hbn := hc.2.2.2.1
  rw [han, hbn]; ring

/-- `uAt S i` squares to 1 for valid indices. -/
lemma uAt_sq {n : Nat} (S : TurynType n) (i : Nat) (hi1 : 1 ≤ i) (hi2 : i ≤ n) :
    uAt S i * uAt S i = 1 := by
  have h := uAt_pm S i hi1 hi2
  rcases h with h | h <;> rw [h] <;> ring

theorem aperiodicAutocorr_A_via_xAt {n : Nat} (S : TurynType n) (s : Nat) (hs : s < n) :
    aperiodicAutocorr S.X.data s =
      ∑ i ∈ Finset.range (n - s), xAt S (i + 1) * xAt S (i + 1 + s) := by
  unfold aperiodicAutocorr
  rw [if_neg (by omega)]
  apply Finset.sum_congr rfl
  intro i hi
  unfold xAt
  have him : i < n := by have := Finset.mem_range.mp hi; omega
  have his : i + s < n := by have := Finset.mem_range.mp hi; omega
  simp [show i + 1 - 1 = i from by omega, show i + 1 + s - 1 = i + s from by omega]

theorem aperiodicAutocorr_B_via_yAt {n : Nat} (S : TurynType n) (s : Nat) (hs : s < n) :
    aperiodicAutocorr S.Y.data s =
      ∑ i ∈ Finset.range (n - s), yAt S (i + 1) * yAt S (i + 1 + s) := by
  unfold aperiodicAutocorr
  rw [if_neg (by omega)]
  apply Finset.sum_congr rfl
  intro i hi
  unfold yAt
  have him : i < n := by have := Finset.mem_range.mp hi; omega
  have his : i + s < n := by have := Finset.mem_range.mp hi; omega
  simp [show i + 1 - 1 = i from by omega, show i + 1 + s - 1 = i + s from by omega]

lemma xAt_sq {n : Nat} (S : TurynType n) (i : Nat) (hi1 : 1 ≤ i) (hi2 : i ≤ n) :
    xAt S i * xAt S i = 1 := by
  have h_sq : xAt S i = 1 ∨ xAt S i = -1 := by
    unfold xAt; exact pm_lookupNat S.X.pm (by omega)
  rcases h_sq with h | h <;> rw [h] <;> norm_num

lemma yAt_eq_xAt_mul_uAt {n : Nat} (S : TurynType n) (i : Nat)
    (hi1 : 1 ≤ i) (hi2 : i ≤ n) :
    yAt S i = xAt S i * uAt S i := by
  unfold uAt
  rw [← mul_assoc, xAt_sq S i hi1 hi2, one_mul]

private lemma summand_identity {n : Nat} (S : TurynType n) (i : Nat)
    (hi1 : 1 ≤ i) (hi2 : i ≤ n) (j : Nat) (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    xAt S i * xAt S j + yAt S i * yAt S j =
    xAt S i * xAt S j * (1 + uAt S i * uAt S j) := by
  rw [yAt_eq_xAt_mul_uAt S i hi1 hi2, yAt_eq_xAt_mul_uAt S j hj1 hj2]
  have : xAt S i * xAt S i = 1 := xAt_sq S i hi1 hi2
  nlinarith [this]

theorem T_k_as_U_sum {n : Nat} (S : TurynType n) (k : Nat) (hk : 2 ≤ k) (hkn : k ≤ n - 1) :
    aperiodicAutocorr S.X.data (n - k) + aperiodicAutocorr S.Y.data (n - k) =
    ∑ i ∈ Finset.range k,
      xAt S (i + 1) * xAt S (i + 1 + (n - k)) *
        (1 + uAt S (i + 1) * uAt S (i + 1 + (n - k))) := by
  have h1 : aperiodicAutocorr S.X.data (n - k) =
      ∑ i ∈ Finset.range k, xAt S (i + 1) * xAt S (i + 1 + (n - k)) := by
    convert aperiodicAutocorr_A_via_xAt S (n - k) _ using 1
    · rw [Nat.sub_sub_self (by omega)]
    · omega
  have h2 : aperiodicAutocorr S.Y.data (n - k) =
      ∑ i ∈ Finset.range k, yAt S (i + 1) * yAt S (i + 1 + (n - k)) := by
    convert aperiodicAutocorr_B_via_yAt S (n - k) _ using 1
    · rw [Nat.sub_sub_self (by omega)]
    · omega
  rw [h1, h2, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply summand_identity
  · omega
  · have := Finset.mem_range.mp hi; omega
  · omega
  · have := Finset.mem_range.mp hi
    have : k ≤ n - 1 := hkn
    omega

/-! ### Parity-hammer helpers -/

/-- Each term of an autocorrelation of a ±1 sequence is itself ±1. -/
lemma autocorr_term_pm {n : Nat} {a : Fin n → Int} (hpm : AllPmOne a) {s : Nat} (hs : s < n)
    {i : Nat} (hi : i < n - s) :
    lookupNat a i * lookupNat a (i + s) = 1 ∨
    lookupNat a i * lookupNat a (i + s) = -1 := by
  have hi_lt : i < n := by omega
  have his_lt : i + s < n := by omega
  rcases pm_lookupNat hpm hi_lt with h1 | h1 <;>
    rcases pm_lookupNat hpm his_lt with h2 | h2 <;>
    (rw [h1, h2]; decide)

/-- Autocorrelation of a ±1 sequence mod 2 equals the number of summation terms mod 2. -/
lemma autocorr_mod_two {n : Nat} {a : Fin n → Int} (hpm : AllPmOne a) {s : Nat} (hs : s < n) :
    aperiodicAutocorr a s % 2 = ((n - s : Nat) : Int) % 2 := by
  convert sum_of_pm_ones_mod_two (n - s)
    (fun i => lookupNat a i * lookupNat a (i + s)) _
  · unfold aperiodicAutocorr
    rw [if_neg (by omega)]
  · exact fun i hi => autocorr_term_pm hpm hs (Finset.mem_range.mp hi)

/-- From the vanishing condition: N_A(s) + N_B(s) = −2·(N_C(s) + N_D(s)). -/
lemma AB_eq_neg2_CD {n : Nat} (S : TurynType n) {s : Nat}
    (hs1 : 1 ≤ s) (hsn : s < n) :
    aperiodicAutocorr S.X.data s + aperiodicAutocorr S.Y.data s =
    -2 * (aperiodicAutocorr S.Z.data s + aperiodicAutocorr S.W.data s) := by
  have := S.vanishing s hs1 hsn
  unfold combinedAutocorr at this; linarith

/-- The sum N_C(s) + N_D(s) is odd for 1 ≤ s ≤ n − 2. -/
lemma autocorr_CD_sum_odd {n : Nat} (S : TurynType n) {s : Nat}
    (hs1 : 1 ≤ s) (hsn : s ≤ n - 2) :
    (aperiodicAutocorr S.Z.data s + aperiodicAutocorr S.W.data s) % 2 = 1 := by
  have hs_lt_n : s < n := by omega
  have hC : aperiodicAutocorr S.Z.data s % 2 = ((n - s : Nat) : Int) % 2 := by
    exact autocorr_mod_two S.Z.pm (by omega)
  have hD : aperiodicAutocorr S.W.data s % 2 = ((n - 1 - s : Nat) : Int) % 2 := by
    exact autocorr_mod_two S.W.pm (by omega)
  omega

/-- −2 times an odd integer is congruent to 2 modulo 4. -/
lemma neg2_mul_odd_mod4 (m : Int) (hm : m % 2 = 1) : (-2 * m) % 4 = 2 := by
  omega

/-- **Parity hammer**: the sum N_A(n−k) + N_B(n−k) is congruent to 2 modulo 4
    for 2 ≤ k ≤ n − 1.  (Best–Đoković–Kharaghani–Ramp, arXiv:1206.4107) -/
theorem parity_hammer {n : Nat} (S : TurynType n) (k : Nat)
    (hk : 2 ≤ k) (hkn : k ≤ n - 1) :
    (aperiodicAutocorr S.X.data (n - k) +
      aperiodicAutocorr S.Y.data (n - k)) % 4 = 2 := by
  have h_sum : aperiodicAutocorr S.X.data (n - k) +
      aperiodicAutocorr S.Y.data (n - k) =
    -2 * (aperiodicAutocorr S.Z.data (n - k) +
      aperiodicAutocorr S.W.data (n - k)) := by
    exact AB_eq_neg2_CD S (Nat.sub_pos_of_lt (by omega))
      (Nat.sub_lt (by omega) (by omega))
  have h_odd : (aperiodicAutocorr S.Z.data (n - k) +
      aperiodicAutocorr S.W.data (n - k)) % 2 = 1 := by
    apply autocorr_CD_sum_odd <;> omega
  omega

/-- xAt S i is ±1 for valid indices. -/
lemma xAt_pm {n : Nat} (S : TurynType n) (i : Nat) (hi1 : 1 ≤ i) (hi2 : i ≤ n) :
    xAt S i = 1 ∨ xAt S i = -1 := by
  unfold xAt; exact pm_lookupNat S.X.pm (by omega)

/-- Pure integer case analysis: if a₁, a₂, u₁, u₂ are all ±1 and
    a₁*(1+u₁) + a₂*(1+u₂) ≡ 2 (mod 4), then u₁ = -u₂. -/
private lemma xy_base_common (a₁ a₂ u₁ u₂ : Int)
    (ha1 : a₁ = 1 ∨ a₁ = -1) (ha2 : a₂ = 1 ∨ a₂ = -1)
    (hu1 : u₁ = 1 ∨ u₁ = -1) (hu2 : u₂ = 1 ∨ u₂ = -1)
    (hmod : (a₁ * (1 + u₁) + a₂ * (1 + u₂)) % 4 = 2) :
    u₁ = -u₂ := by
  rcases ha1 with rfl | rfl <;> rcases ha2 with rfl | rfl <;>
    rcases hu1 with rfl | rfl <;> rcases hu2 with rfl | rfl <;> omega

theorem xy_base_k2 {n : Nat} (S : TurynType n) (hn : 3 ≤ n)
    (hc : Canonical1 n S) : uAt S (n - 1) = -(uAt S 2) := by
  apply xy_base_common (xAt S (n - 1)) (xAt S 2) (uAt S (n - 1)) (uAt S 2)
    (xAt_pm S (n - 1) (by omega) (by omega))
    (xAt_pm S 2 (by omega) (by omega))
    (uAt_pm S (n - 1) (by omega) (by omega))
    (uAt_pm S 2 (by omega) (by omega))
  have hph := parity_hammer S 2 (by decide) (by omega)
  rw [T_k_as_U_sum S 2 (by decide) (by omega)] at hph
  rw [show (2 : ℕ) = 0 + 1 + 1 from by norm_num] at hph
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at hph
  simp only [zero_add] at hph
  have h1n : 1 + (n - 2) = n - 1 := by omega
  have h2n : 2 + (n - 2) = n := by omega
  rw [h1n, h2n] at hph
  rw [hc.1, hc.2.1, uAt_one_of_canonical1_head hc,
      uAt_one_of_canonical1_tail (by omega) hc] at hph
  convert hph using 2; ring

theorem xy_base_k3 {n : Nat} (S : TurynType n) (hn : 4 ≤ n)
    (hc : Canonical1 n S) : uAt S (n - 2) = -(uAt S 3) := by
  apply xy_base_common (xAt S (n - 2)) (xAt S 3) (uAt S (n - 2)) (uAt S 3)
    (xAt_pm S (n - 2) (by omega) (by omega))
    (xAt_pm S 3 (by omega) (by omega))
    (uAt_pm S (n - 2) (by omega) (by omega))
    (uAt_pm S 3 (by omega) (by omega))
  have hT3_mod4 : (aperiodicAutocorr S.X.data (n - 3) +
      aperiodicAutocorr S.Y.data (n - 3)) % 4 = 2 := by
    apply parity_hammer S 3 (by omega) (by omega)
  convert hT3_mod4 using 1
  rw [T_k_as_U_sum S 3 (by omega) (by omega)]
  norm_num [Finset.sum_range_succ]
  ring_nf
  rw [show 3 + (n - 3) = n by omega,
      show 1 + (n - 3) = n - 2 by omega,
      show 2 + (n - 3) = n - 1 by omega]
  ring_nf
  rw [show xAt S 1 = 1 by exact hc.1,
      show xAt S n = 1 by exact hc.2.1,
      show uAt S 1 = 1 by exact uAt_one_of_canonical1_head hc,
      show uAt S n = 1 by exact uAt_one_of_canonical1_tail (by linarith) hc]
  ring_nf
  rw [show uAt S (n - 1) = -uAt S 2 by exact xy_base_k2 S (by omega) hc]
  ring_nf
  rw [show uAt S 2 ^ 2 = 1 by rw [sq, uAt_sq S 2 (by linarith) (by omega)]]
  ring_nf

/-- Endpoint-pair mod-4 lemma (pure integer). -/
private lemma endpoint_pair_mod4_pure (a_p a_q u_p u_q : Int)
    (ha_p : a_p = 1 ∨ a_p = -1) (ha_q : a_q = 1 ∨ a_q = -1)
    (hu_p : u_p = 1 ∨ u_p = -1) (hu_q : u_q = 1 ∨ u_q = -1) :
    (a_p * (1 + u_p) + a_q * (1 + u_q)) % 4 = 2 ↔ u_p = -u_q := by
  rcases ha_p with rfl | rfl <;> rcases ha_q with rfl | rfl <;>
    rcases hu_p with rfl | rfl <;> rcases hu_q with rfl | rfl <;> decide

lemma endpoint_pair_mod4 {n : Nat} (S : TurynType n) (k : Nat)
    (hk : 2 ≤ k) (hkn : k ≤ n - 1) (_hc : Canonical1 n S) :
    (xAt S (n + 1 - k) * (1 + uAt S (n + 1 - k)) +
      xAt S k * (1 + uAt S k)) % 4 = 2 ↔
      uAt S (n + 1 - k) = -(uAt S k) := by
  exact endpoint_pair_mod4_pure
    (xAt S (n + 1 - k)) (xAt S k) (uAt S (n + 1 - k)) (uAt S k)
    (xAt_pm S (n + 1 - k) (by omega) (by omega))
    (xAt_pm S k (by omega) (by omega))
    (uAt_pm S (n + 1 - k) (by omega) (by omega))
    (uAt_pm S k (by omega) (by omega))

/-- Pure integer algebra: paired sum divisible by 4. -/
private lemma pm_pair_sum_mod4 (a1 a2 a3 a4 u1 u3 : Int)
    (ha1 : a1 = 1 ∨ a1 = -1) (ha2 : a2 = 1 ∨ a2 = -1)
    (ha3 : a3 = 1 ∨ a3 = -1) (ha4 : a4 = 1 ∨ a4 = -1)
    (hu1 : u1 = 1 ∨ u1 = -1) (hu3 : u3 = 1 ∨ u3 = -1) :
    (a1 * a2 * (1 + u1 * (-u3)) + a3 * a4 * (1 + u3 * (-u1))) % 4 = 0 := by
  rcases ha1 with rfl | rfl <;> rcases ha2 with rfl | rfl <;>
  rcases ha3 with rfl | rfl <;> rcases ha4 with rfl | rfl <;>
  rcases hu1 with rfl | rfl <;> rcases hu3 with rfl | rfl <;> decide

/-- Interior-pair mod-4 lemma. -/
lemma interior_pair_mod4 {n : Nat} (S : TurynType n) (k : Nat)
    (hk : 4 ≤ k) (hkn : k ≤ n - 1)
    (IH : ∀ j, 2 ≤ j → j < k → uAt S (n + 1 - j) = -(uAt S j))
    {m : Nat} (hm1 : 2 ≤ m) (hm2 : 2 * m ≤ k) (hm3 : m < k + 1 - m) :
    (xAt S m * xAt S (m + (n - k)) * (1 + uAt S m * uAt S (m + (n - k))) +
     xAt S (k + 1 - m) * xAt S ((k + 1 - m) + (n - k)) *
        (1 + uAt S (k + 1 - m) * uAt S ((k + 1 - m) + (n - k)))) % 4 = 0 := by
  have hidx1 : m + (n - k) = n + 1 - (k + 1 - m) := by omega
  have hidx2 : (k + 1 - m) + (n - k) = n + 1 - m := by omega
  have hih1 : uAt S (m + (n - k)) = -(uAt S (k + 1 - m)) := by
    rw [hidx1]; exact IH (k + 1 - m) (by omega) (by omega)
  have hih2 : uAt S ((k + 1 - m) + (n - k)) = -(uAt S m) := by
    rw [hidx2]; exact IH m hm1 (by omega)
  rw [hih1, hih2]
  exact pm_pair_sum_mod4
    (xAt S m) (xAt S (m + (n - k)))
    (xAt S (k + 1 - m)) (xAt S ((k + 1 - m) + (n - k)))
    (uAt S m) (uAt S (k + 1 - m))
    (xAt_pm S m (by omega) (by omega))
    (xAt_pm S (m + (n - k)) (by omega) (by omega))
    (xAt_pm S (k + 1 - m) (by omega) (by omega))
    (xAt_pm S ((k + 1 - m) + (n - k)) (by omega) (by omega))
    (uAt_pm S m (by omega) (by omega))
    (uAt_pm S (k + 1 - m) (by omega) (by omega))

lemma middle_term_zero {n : Nat} (S : TurynType n) (k : Nat)
    (hk : 4 ≤ k) (hkn : k ≤ n - 1) (hk_odd : k % 2 = 1)
    (IH : ∀ j, 2 ≤ j → j < k → uAt S (n + 1 - j) = -(uAt S j)) :
    xAt S ((k + 1) / 2) * xAt S ((k + 1) / 2 + (n - k)) *
      (1 + uAt S ((k + 1) / 2) * uAt S ((k + 1) / 2 + (n - k))) = 0 := by
  rw [show (k + 1) / 2 + (n - k) = n + 1 - ((k + 1) / 2) from by omega]
  rw [IH ((k + 1) / 2) (by omega) (by omega)]
  have h_sq := uAt_sq S ((k + 1) / 2) (by omega) (by omega)
  have h_neg : uAt S ((k + 1) / 2) * -uAt S ((k + 1) / 2) = -1 := by linarith [h_sq]
  rw [h_neg]; ring

/-! ### Paired-sum mod 4 helpers -/

private lemma sum_paired_mod4 : ∀ (m : Nat) (f : Nat → Int),
    (∀ i, i < m → (f i + f (2 * m - 1 - i)) % 4 = 0) →
    (∑ i ∈ Finset.range (2 * m), f i) % 4 = 0 := by
  have h_pair : ∀ m : ℕ, ∀ f : ℕ → ℤ,
      (∑ i ∈ Finset.range (2 * m), f i) =
      ∑ i ∈ Finset.range m, (f i + f (2 * m - 1 - i)) := by
    intro m f
    rw [show 2 * m = m + m from by omega, Finset.sum_range_add]
    have h_reflect : ∑ i ∈ Finset.range m, f (m + i) =
        ∑ i ∈ Finset.range m, f (m + m - 1 - i) := by
      rw [← Finset.sum_range_reflect]
      exact Finset.sum_congr rfl fun x hx =>
        congr_arg f (by have := Finset.mem_range.mp hx; omega)
    rw [h_reflect, ← Finset.sum_add_distrib]
  exact fun m f hf =>
    h_pair m f ▸ Int.emod_eq_zero_of_dvd
      (Finset.dvd_sum fun i hi =>
        Int.dvd_of_emod_eq_zero (hf i (Finset.mem_range.mp hi)))

private lemma sum_paired_with_middle_mod4 : ∀ (m : Nat) (f : Nat → Int),
    (∀ i, i < m → (f i + f (2 * m - i)) % 4 = 0) →
    f m = 0 →
    (∑ i ∈ Finset.range (2 * m + 1), f i) % 4 = 0 := by
  intro m f hf hmid
  have h_split : ∑ i ∈ Finset.range (2 * m + 1), f i =
      f m + ∑ i ∈ Finset.range m, (f i + f (2 * m - i)) := by
    rw [show 2 * m + 1 = m + 1 + m from by omega, Finset.sum_range_add,
        Finset.sum_range_succ]
    have h_reflect : ∑ i ∈ Finset.range m, f (m + 1 + i) =
        ∑ i ∈ Finset.range m, f (2 * m - i) := by
      rw [← Finset.sum_range_reflect]
      exact Finset.sum_congr rfl fun x hx =>
        congr_arg f (by have := Finset.mem_range.mp hx; omega)
    rw [h_reflect]
    have h_distrib : ∑ i ∈ Finset.range m, (f i + f (2 * m - i)) =
        ∑ i ∈ Finset.range m, f i + ∑ i ∈ Finset.range m, f (2 * m - i) :=
      Finset.sum_add_distrib
    linarith [h_distrib]
  rw [h_split, hmid, zero_add]
  exact Int.emod_eq_zero_of_dvd
    (Finset.dvd_sum fun i hi =>
      Int.dvd_of_emod_eq_zero (hf i (Finset.mem_range.mp hi)))

/-! ### Interior-sum vanishing mod 4 -/

private lemma interior_sum_mod4_zero {n : Nat} (S : TurynType n) (k : Nat)
    (hk : 4 ≤ k) (hkn : k ≤ n - 1) (_hc : Canonical1 n S)
    (IH : ∀ j, 2 ≤ j → j < k → uAt S (n + 1 - j) = -(uAt S j)) :
    (∑ i ∈ Finset.Ico 1 (k - 1),
      xAt S (i + 1) * xAt S (i + 1 + (n - k)) *
        (1 + uAt S (i + 1) * uAt S (i + 1 + (n - k)))) % 4 = 0 := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hkk : k - 1 - 1 = k - 2 := by omega
  rw [hkk]
  have h_norm : ∀ j, xAt S (1 + j + 1) * xAt S (1 + j + 1 + (n - k)) *
      (1 + uAt S (1 + j + 1) * uAt S (1 + j + 1 + (n - k))) =
      xAt S (j + 2) * xAt S (j + 2 + (n - k)) *
      (1 + uAt S (j + 2) * uAt S (j + 2 + (n - k))) := by
    intro j; rw [show 1 + j + 1 = j + 2 from by omega]
  simp only [h_norm]
  by_cases hk_even : k % 2 = 0
  · have hlen : k - 2 = 2 * ((k - 2) / 2) := by omega
    rw [hlen]
    apply sum_paired_mod4
    intro j hj
    rw [show 2 * ((k - 2) / 2) - 1 - j + 2 = k + 1 - (j + 2) from by omega]
    exact interior_pair_mod4 S k hk hkn IH
      (show 2 ≤ j + 2 from by omega)
      (show 2 * (j + 2) ≤ k from by omega)
      (show j + 2 < k + 1 - (j + 2) from by omega)
  · have hlen : k - 2 = 2 * ((k - 3) / 2) + 1 := by omega
    rw [hlen]
    apply sum_paired_with_middle_mod4
    · intro j hj
      rw [show 2 * ((k - 3) / 2) - j + 2 = k + 1 - (j + 2) from by omega]
      exact interior_pair_mod4 S k hk hkn IH
        (show 2 ≤ j + 2 from by omega)
        (show 2 * (j + 2) ≤ k from by omega)
        (show j + 2 < k + 1 - (j + 2) from by omega)
    · have hk_odd : k % 2 = 1 := by omega
      rw [show (k - 3) / 2 + 2 = (k + 1) / 2 from by omega]
      exact middle_term_zero S k hk hkn hk_odd IH

/-! ### First and last summand simplification -/

private lemma first_summand_eq {n : Nat} (S : TurynType n) (k : Nat)
    (hk : 2 ≤ k) (hkn : k ≤ n - 1) (hc : Canonical1 n S) :
    xAt S (0 + 1) * xAt S (0 + 1 + (n - k)) *
      (1 + uAt S (0 + 1) * uAt S (0 + 1 + (n - k))) =
    xAt S (n + 1 - k) * (1 + uAt S (n + 1 - k)) := by
  rw [show n + 1 - k = 1 + (n - k) by omega]
  rw [show xAt S 1 = 1 by exact hc.1,
      show uAt S 1 = 1 by exact uAt_one_of_canonical1_head hc]
  ring

private lemma last_summand_eq {n : Nat} (S : TurynType n) (k : Nat)
    (hk : 2 ≤ k) (hkn : k ≤ n - 1) (hc : Canonical1 n S) :
    xAt S (k - 1 + 1) * xAt S (k - 1 + 1 + (n - k)) *
      (1 + uAt S (k - 1 + 1) * uAt S (k - 1 + 1 + (n - k))) =
    xAt S k * (1 + uAt S k) := by
  rw [Nat.sub_add_cancel (by linarith)]
  rw [Nat.add_sub_of_le (by omega)]
  have h_an : xAt S n = 1 := hc.2.1
  have h_un : uAt S n = 1 := by
    have h_bn : yAt S n = 1 := hc.2.2.2.1
    unfold uAt; rw [h_an, h_bn]; ring
  rw [h_an, h_un]; ring

/-! ### Main XY product-law theorem -/

/-- **XY product law**.
For a canonical Turyn sequence of length `n ≥ 4`,
`uAt S (n+1−k) = −uAt S k` for all `2 ≤ k ≤ n−1`. -/
theorem xy_product_law {n : Nat} (S : TurynType n) (hn : 4 ≤ n)
    (hc : Canonical1 n S) :
    ∀ k, 2 ≤ k → k ≤ n - 1 → uAt S (n + 1 - k) = -(uAt S k) := by
  intros k hk2 hkn
  induction' k using Nat.strongRecOn with k ih
  by_cases hk : k < 4
  · have hk23 : k = 2 ∨ k = 3 := by omega
    rcases hk23 with rfl | rfl
    · rw [show n + 1 - 2 = n - 1 from by omega]
      exact xy_base_k2 S (by linarith) hc
    · rw [show n + 1 - 3 = n - 2 from by omega]
      exact xy_base_k3 S hn hc
  · let f := fun i => xAt S (i + 1) * xAt S (i + 1 + (n - k)) *
        (1 + uAt S (i + 1) * uAt S (i + 1 + (n - k)))
    have h_range_split : ∑ i ∈ Finset.range k, f i =
        f 0 + ∑ i ∈ Finset.Ico 1 (k - 1), f i + f (k - 1) := by
      have h1 : Finset.range k = {0} ∪ Finset.Ico 1 (k - 1) ∪ {k - 1} := by
        ext x; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico,
          Finset.mem_singleton]; omega
      have h2 : Disjoint ({0} ∪ Finset.Ico 1 (k - 1)) {k - 1} := by
        simp only [Finset.disjoint_singleton_right, Finset.mem_union, Finset.mem_singleton,
          Finset.mem_Ico]; omega
      have h3 : Disjoint ({0} : Finset Nat) (Finset.Ico 1 (k - 1)) := by
        simp only [Finset.disjoint_singleton_left, Finset.mem_Ico]; omega
      rw [h1, Finset.sum_union h2, Finset.sum_union h3,
          Finset.sum_singleton, Finset.sum_singleton]
    have hf0 : f 0 = xAt S (n + 1 - k) * (1 + uAt S (n + 1 - k)) :=
      first_summand_eq S k hk2 hkn hc
    have hfk : f (k - 1) = xAt S k * (1 + uAt S k) :=
      last_summand_eq S k hk2 hkn hc
    have hTsum : aperiodicAutocorr S.X.data (n - k) +
        aperiodicAutocorr S.Y.data (n - k) =
      (xAt S (n + 1 - k) * (1 + uAt S (n + 1 - k)) +
        xAt S k * (1 + uAt S k)) +
      (∑ i ∈ Finset.Ico 1 (k - 1),
        xAt S (i + 1) * xAt S (i + 1 + (n - k)) *
          (1 + uAt S (i + 1) * uAt S (i + 1 + (n - k)))) := by
      rw [T_k_as_U_sum S k hk2 hkn, h_range_split, hf0, hfk]; ring
    have h_interior : (∑ i ∈ Finset.Ico 1 (k - 1),
        xAt S (i + 1) * xAt S (i + 1 + (n - k)) *
          (1 + uAt S (i + 1) * uAt S (i + 1 + (n - k)))) % 4 = 0 := by
      apply interior_sum_mod4_zero S k (by linarith) (by linarith) hc
        (fun j hj1 hj2 => ih j (by linarith) hj1 (by omega))
    have h_total : (aperiodicAutocorr S.X.data (n - k) +
        aperiodicAutocorr S.Y.data (n - k)) % 4 = 2 := by
      apply parity_hammer S k hk2 hkn
    apply (endpoint_pair_mod4 S k hk2 hkn hc).mp
    omega

/-- **Corollary**: The product of `xAt S k * yAt S k` and
`xAt S (n+1−k) * yAt S (n+1−k)` equals `−1` for `2 ≤ k ≤ n−1`. -/
theorem xy_product_eq_neg_one {n : Nat} (S : TurynType n) (hn : 4 ≤ n)
    (hc : Canonical1 n S) :
    ∀ k, 2 ≤ k → k ≤ n - 1 →
      xAt S k * yAt S k * xAt S (n + 1 - k) * yAt S (n + 1 - k) = -1 := by
  intro k hk2 hkn
  have h := xy_product_law S hn hc k hk2 hkn
  have hprod : xAt S k * yAt S k * xAt S (n + 1 - k) * yAt S (n + 1 - k) =
      uAt S k * uAt S (n + 1 - k) := by
    unfold uAt; ring
  rw [hprod, h]
  have hsq := uAt_sq S k (by omega) (by omega)
  linarith

end Turyn
