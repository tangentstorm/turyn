import Turyn.BaseSequence
import Mathlib

open Finset
open BigOperators

/-!
# T-Sequences

Typed T-sequences and the standard construction from base sequences. The main
results show that the constructed sequences have disjoint `{0, ±1}` support and
vanishing combined periodic autocorrelation, making them ready for the final
Goethals-Seidel step.
-/

/-- Element-wise sum divided by `2`. -/
def seqSumHalf (a b : List Int) : List Int :=
  List.zipWith (fun x y => (x + y) / 2) a b

/-- Element-wise difference divided by `2`. -/
def seqDiffHalf (a b : List Int) : List Int :=
  List.zipWith (fun x y => (x - y) / 2) a b

/-- Zero sequence of length `k`. -/
def zeroSeq (k : Nat) : List Int := List.replicate k 0

/-- Periodic autocorrelation of a sequence of length `m` at lag `s`. -/
def periodicAutocorr (a : List Int) (s : Nat) : Int :=
  let m := a.length
  if m == 0 then 0
  else ∑ i ∈ range m, a.getD i 0 * a.getD ((i + s) % m) 0

/-- Combined periodic autocorrelation of four sequences. -/
def combinedPeriodicAutocorr (a b c d : List Int) (s : Nat) : Int :=
  periodicAutocorr a s + periodicAutocorr b s +
  periodicAutocorr c s + periodicAutocorr d s

/-- Construct the four T-sequences from TT(n) = (X, Y, Z, W). -/
def tSequences (x y z w : PmSeq) :
    List Int × List Int × List Int × List Int :=
  let (bsA, bsB, bsC, bsD) := baseSequences x y z w
  let n := x.length
  (seqSumHalf bsA bsB ++ zeroSeq n,
   seqDiffHalf bsA bsB ++ zeroSeq n,
   zeroSeq (2 * n - 1) ++ seqSumHalf bsC bsD,
   zeroSeq (2 * n - 1) ++ seqDiffHalf bsC bsD)

/-- The Hadamard order produced by the Turyn pipeline. -/
def hadamardOrder (n : Nat) : Nat := 4 * (3 * n - 1)

/-- Honest Step 2 output: a typed T-sequence object of length `m`. -/
structure TSequence (m : Nat) where
  a : List Int
  b : List Int
  c : List Int
  d : List Int
  a_len : a.length = m
  b_len : b.length = m
  c_len : c.length = m
  d_len : d.length = m
  support : ∀ i, i < m →
    Int.natAbs (a.getD i 0) + Int.natAbs (b.getD i 0) +
      Int.natAbs (c.getD i 0) + Int.natAbs (d.getD i 0) = 1
  periodic_vanishing :
    ∀ s, 1 ≤ s → s < m → combinedPeriodicAutocorr a b c d s = 0

/-- The four raw list components used by Step 2. -/
def step2a {n : Nat} (T : TurynType n) : List Int :=
  T.z.data ++ zeroSeq (2 * n - 1)

/-- Second raw list component for Step 2: zero-padded W. -/
def step2b {n : Nat} (T : TurynType n) : List Int :=
  zeroSeq n ++ (T.w.data ++ zeroSeq n)

/-- Third raw list component for Step 2: zero-padded half-sum of X and Y. -/
def step2c {n : Nat} (T : TurynType n) : List Int :=
  zeroSeq (2 * n - 1) ++ seqSumHalf T.x.data T.y.data

/-- Fourth raw list component for Step 2: zero-padded half-difference of X and Y. -/
def step2d {n : Nat} (T : TurynType n) : List Int :=
  zeroSeq (2 * n - 1) ++ seqDiffHalf T.x.data T.y.data

/-- Length of `zeroSeq`. -/
@[simp] lemma zeroSeq_length (k : Nat) : (zeroSeq k).length = k := by
  simp [zeroSeq]

/-- Indexing into `zeroSeq` always yields `0`. -/
@[simp] lemma zeroSeq_getD (k i : Nat) : (zeroSeq k).getD i 0 = 0 := by
  unfold zeroSeq
  simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> simp

/-- Valid entries of a signed sequence are `±1`. -/
lemma signedSeq_getD_pmOne {n : Nat} (s : SignedSeq n) {i : Nat} (hi : i < n) :
    s.data.getD i 0 = 1 ∨ s.data.getD i 0 = -1 := by
  rw [List.getD_eq_getElem _ _ (by simpa [s.len] using hi)]
  exact s.pm _ (List.getElem_mem (by simpa [s.len] using hi))

/-- Valid entries of a signed sequence have absolute value `1`. -/
lemma signedSeq_natAbs_getD {n : Nat} (s : SignedSeq n) {i : Nat} (hi : i < n) :
    Int.natAbs (s.data.getD i 0) = 1 := by
  rcases signedSeq_getD_pmOne s hi with h | h <;> rw [h] <;> decide

/-- Equal-length half-sum accessor. -/
lemma seqSumHalf_getD {a b : List Int} {i : Nat}
    (hab : a.length = b.length) (hi : i < a.length) :
    (seqSumHalf a b).getD i 0 = (a.getD i 0 + b.getD i 0) / 2 := by
  have hib : i < b.length := by omega
  have hiz : i < (seqSumHalf a b).length := by
    simp [seqSumHalf, List.length_zipWith, hab, hib]
  rw [List.getD_eq_getElem _ _ hiz]
  simp [seqSumHalf, List.getElem_zipWith, hi, hib]

/-- Equal-length half-difference accessor. -/
lemma seqDiffHalf_getD {a b : List Int} {i : Nat}
    (hab : a.length = b.length) (hi : i < a.length) :
    (seqDiffHalf a b).getD i 0 = (a.getD i 0 - b.getD i 0) / 2 := by
  have hib : i < b.length := by omega
  have hiz : i < (seqDiffHalf a b).length := by
    simp [seqDiffHalf, List.length_zipWith, hab, hib]
  rw [List.getD_eq_getElem _ _ hiz]
  simp [seqDiffHalf, List.getElem_zipWith, hi, hib]

/-- For two `±1` values, exactly one of the half-sum and half-difference has absolute value `1`. -/
lemma natAbs_halfSum_add_natAbs_halfDiff_eq_one (u v : Int)
    (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) :
    Int.natAbs ((u + v) / 2) + Int.natAbs ((u - v) / 2) = 1 := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> decide

/-- Step 2 support/certification interface. -/
theorem step2_support {n : Nat} (T : TurynType n) :
  ∀ i, i < 3 * n - 1 →
    Int.natAbs ((step2a T).getD i 0) + Int.natAbs ((step2b T).getD i 0) +
      Int.natAbs ((step2c T).getD i 0) + Int.natAbs ((step2d T).getD i 0) = 1
  := by
  intro i hi
  by_cases h1 : i < n
  · have ht1 : (step2a T).getD i 0 = T.z.data.getD i 0 := by
      unfold step2a
      rw [List.getD_append _ _ _ _ (by simpa [T.z.len] using h1)]
    have ht2 : (step2b T).getD i 0 = 0 := by
      unfold step2b
      rw [List.getD_append _ _ _ _ (by simpa [zeroSeq_length] using h1)]
      exact zeroSeq_getD n i
    have hpre : i < 2 * n - 1 := by omega
    have ht3 : (step2c T).getD i 0 = 0 := by
      unfold step2c
      rw [List.getD_append _ _ _ _ (by simpa [zeroSeq_length] using hpre)]
      exact zeroSeq_getD (2 * n - 1) i
    have ht4 : (step2d T).getD i 0 = 0 := by
      unfold step2d
      rw [List.getD_append _ _ _ _ (by simpa [zeroSeq_length] using hpre)]
      exact zeroSeq_getD (2 * n - 1) i
    rw [ht1, ht2, ht3, ht4]
    simp
    exact signedSeq_natAbs_getD T.z h1
  · by_cases h2 : i < 2 * n - 1
    · have hn : n ≤ i := by omega
      have ht1 : (step2a T).getD i 0 = 0 := by
        unfold step2a
        rw [List.getD_append_right _ _ _ _ (by simpa [T.z.len] using hn)]
        simpa [T.z.len] using zeroSeq_getD (2 * n - 1) (i - T.z.data.length)
      have hw : i - n < T.w.data.length := by
        simpa [T.w.len] using (show i - n < n - 1 by omega)
      have hw' : i - (zeroSeq n).length < T.w.data.length := by
        simpa [zeroSeq_length] using hw
      have ht2 : (step2b T).getD i 0 = T.w.data.getD (i - n) 0 := by
        unfold step2b
        rw [List.getD_append_right _ _ _ _ (by simpa [zeroSeq_length] using hn)]
        simpa [zeroSeq_length] using (List.getD_append T.w.data (zeroSeq n) 0 (i - (zeroSeq n).length) hw')
      have ht3 : (step2c T).getD i 0 = 0 := by
        unfold step2c
        rw [List.getD_append _ _ _ _ (by simpa [zeroSeq_length] using h2)]
        exact zeroSeq_getD (2 * n - 1) i
      have ht4 : (step2d T).getD i 0 = 0 := by
        unfold step2d
        rw [List.getD_append _ _ _ _ (by simpa [zeroSeq_length] using h2)]
        exact zeroSeq_getD (2 * n - 1) i
      rw [ht1, ht2, ht3, ht4]
      simp
      have hwn : i - n < n - 1 := by omega
      simpa [T.w.len] using signedSeq_natAbs_getD T.w hwn
    · have h3 : 2 * n - 1 ≤ i := by omega
      have hx : i - (2 * n - 1) < T.x.data.length := by
        simpa [T.x.len] using (show i - (2 * n - 1) < n by omega)
      have hy : i - (2 * n - 1) < T.y.data.length := by
        simpa [T.y.len] using (show i - (2 * n - 1) < n by omega)
      have hxy : T.x.data.length = T.y.data.length := by rw [T.x.len, T.y.len]
      have ht1 : (step2a T).getD i 0 = 0 := by
        unfold step2a
        rw [List.getD_append_right _ _ _ _ (by
          have : T.z.data.length ≤ i := by rw [T.z.len]; omega
          exact this)]
        simpa [T.z.len] using zeroSeq_getD (2 * n - 1) (i - T.z.data.length)
      have ht2 : (step2b T).getD i 0 = 0 := by
        unfold step2b
        rw [List.getD_append_right _ _ _ _ (by
          have : n ≤ i := by omega
          simpa [zeroSeq_length] using this)]
        rw [List.getD_append_right _ _ _ _ (by
          have : T.w.data.length ≤ i - (zeroSeq n).length := by
            simpa [zeroSeq_length, T.w.len] using (show T.w.data.length ≤ i - n by rw [T.w.len]; omega)
          exact this)]
        simpa [zeroSeq_length, T.w.len] using
          zeroSeq_getD n (i - n - T.w.data.length)
      have ht3 : (step2c T).getD i 0 =
          (T.x.data.getD (i - (2 * n - 1)) 0 + T.y.data.getD (i - (2 * n - 1)) 0) / 2 := by
        unfold step2c
        rw [List.getD_append_right _ _ _ _ (by simpa [zeroSeq_length] using h3)]
        simpa [zeroSeq_length] using seqSumHalf_getD hxy hx
      have ht4 : (step2d T).getD i 0 =
          (T.x.data.getD (i - (2 * n - 1)) 0 - T.y.data.getD (i - (2 * n - 1)) 0) / 2 := by
        unfold step2d
        rw [List.getD_append_right _ _ _ _ (by simpa [zeroSeq_length] using h3)]
        simpa [zeroSeq_length] using seqDiffHalf_getD hxy hx
      rw [ht1, ht2, ht3, ht4]
      simp
      exact natAbs_halfSum_add_natAbs_halfDiff_eq_one
        (T.x.data.getD (i - (2 * n - 1)) 0)
        (T.y.data.getD (i - (2 * n - 1)) 0)
        (signedSeq_getD_pmOne T.x (by simpa [T.x.len] using hx))
        (signedSeq_getD_pmOne T.y (by simpa [T.y.len] using hy))

/-! ### Helper lemmas for periodic autocorrelation -/

/-- Aperiodic autocorrelation vanishes when the lag meets or exceeds the length. -/
private lemma aperiodicAutocorr_zero_of_ge (a : List Int) (s : Nat) (h : s ≥ a.length) :
    aperiodicAutocorr a s = 0 := by
  unfold aperiodicAutocorr; exact if_pos h

/-- Periodic autocorrelation decomposes into aperiodic at lag s plus aperiodic at lag m-s. -/
lemma periodic_eq_aperiodic_sum (a : List Int) (s : Nat) (hs : 0 < s) (hsm : s < a.length) :
    periodicAutocorr a s =
      aperiodicAutocorr a s + aperiodicAutocorr a (a.length - s) := by
  set m := a.length with hm_def
  have hper : periodicAutocorr a s = ∑ i ∈ range m, a.getD i 0 * a.getD ((i + s) % m) 0 := by
    simp only [periodicAutocorr]
    split
    next h =>
      exfalso
      rw [beq_iff_eq] at h
      omega
    next => rfl
  have hap1 : aperiodicAutocorr a s = ∑ i ∈ range (m - s), a.getD i 0 * a.getD (i + s) 0 := by
    unfold aperiodicAutocorr; exact if_neg (by omega)
  have hap2 : aperiodicAutocorr a (m - s) = ∑ i ∈ range s, a.getD i 0 * a.getD (i + (m - s)) 0 := by
    unfold aperiodicAutocorr
    rw [if_neg (by omega), show m - (m - s) = s from by omega]
  rw [hper, hap1, hap2, ← Finset.sum_range_add_sum_Ico _ (Nat.sub_le m s)]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_range] at hi
    rw [show (i + s) % m = i + s from Nat.mod_eq_of_lt (by omega)]
  · rw [Finset.sum_Ico_eq_sum_range, show m - (m - s) = s from by omega]
    apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_range] at hi
    rw [show (m - s + i + s) % m = i from by
      rw [show m - s + i + s = i + m from by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)]
    ring_nf

/-- Accessing `a ++ zeroSeq k` via `getD` always agrees with accessing `a`. -/
private lemma getD_append_zeroSeq (a : List Int) (k i : Nat) :
    (a ++ zeroSeq k).getD i 0 = a.getD i 0 := by
  by_cases hi : i < a.length
  · rw [List.getD_append _ _ _ _ hi]
  · push_neg at hi
    rw [List.getD_eq_default a 0 hi]
    rw [List.getD_append_right _ _ _ _ hi]
    rw [zeroSeq_getD]

/-- Appending zeros does not change the aperiodic autocorrelation. -/
lemma aperiodicAutocorr_append_zeros (a : List Int) (k s : Nat) :
    aperiodicAutocorr (a ++ zeroSeq k) s = aperiodicAutocorr a s := by
  unfold aperiodicAutocorr
  simp only [List.length_append, zeroSeq_length]
  by_cases hs : s ≥ a.length
  · -- RHS: if_pos
    rw [if_pos hs]
    by_cases hsk : s ≥ a.length + k
    · -- LHS: if_pos
      rw [if_pos hsk]
    · -- LHS: if_neg, but every term is 0 since i + s ≥ a.length
      push_neg at hsk
      rw [if_neg (by omega)]
      apply Finset.sum_eq_zero
      intro i hi
      rw [getD_append_zeroSeq, getD_append_zeroSeq]
      have : a.getD (i + s) 0 = 0 :=
        List.getD_eq_default a 0 (by rw [Finset.mem_range] at hi; omega)
      rw [this, mul_zero]
  · -- Both sides compute sums
    push_neg at hs
    rw [if_neg (by omega), if_neg (by omega)]
    -- Split LHS sum: range (a.length + k - s) = range (a.length - s) ∪ Ico ...
    rw [← Finset.sum_range_add_sum_Ico _ (show a.length - s ≤ a.length + k - s by omega)]
    -- First part: terms agree with RHS
    have h_agree : ∀ i ∈ Finset.range (a.length - s),
        (a ++ zeroSeq k).getD i 0 * (a ++ zeroSeq k).getD (i + s) 0 =
        a.getD i 0 * a.getD (i + s) 0 := by
      intro i _
      rw [getD_append_zeroSeq, getD_append_zeroSeq]
    -- Second part: each term is 0 since i + s ≥ a.length
    have h_zero : ∀ i ∈ Finset.Ico (a.length - s) (a.length + k - s),
        (a ++ zeroSeq k).getD i 0 * (a ++ zeroSeq k).getD (i + s) 0 = 0 := by
      intro i hi
      rw [getD_append_zeroSeq, getD_append_zeroSeq]
      rw [Finset.mem_Ico] at hi
      have : a.getD (i + s) 0 = 0 :=
        List.getD_eq_default a 0 (by omega)
      rw [this, mul_zero]
    rw [Finset.sum_congr rfl h_agree, Finset.sum_eq_zero h_zero, add_zero]

/-- Prepending zeros does not change the aperiodic autocorrelation. -/
lemma aperiodicAutocorr_prepend_zeros (a : List Int) (k s : Nat) :
    aperiodicAutocorr (zeroSeq k ++ a) s = aperiodicAutocorr a s := by
  unfold aperiodicAutocorr
  have hlen : (zeroSeq k ++ a).length = k + a.length := by
    rw [List.length_append, zeroSeq_length]
  rw [hlen]
  by_cases h1 : s ≥ k + a.length
  · -- s ≥ k + a.length implies s ≥ a.length
    have h2 : s ≥ a.length := by omega
    rw [if_pos h1, if_pos h2]
  · push_neg at h1
    rw [if_neg (by omega)]
    by_cases h2 : s ≥ a.length
    · -- s ≥ a.length: RHS = 0, sum over indices < k so all hit zero region
      rw [if_pos h2]
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      have hik : i < k := by omega
      rw [List.getD_append _ _ _ _ (by rw [zeroSeq_length]; exact hik),
          zeroSeq_getD, zero_mul]
    · -- s < a.length: main case
      push_neg at h2
      rw [if_neg (by omega)]
      have hsplit : k + a.length - s = k + (a.length - s) := by omega
      rw [hsplit, Finset.sum_range_add]
      -- First k terms: index hits zeroSeq, so each is 0
      have hfirst : ∑ x ∈ range k,
          (zeroSeq k ++ a).getD x 0 * (zeroSeq k ++ a).getD (x + s) 0 = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_range] at hi
        rw [List.getD_append _ _ _ _ (by rw [zeroSeq_length]; exact hi),
            zeroSeq_getD, zero_mul]
      rw [hfirst, zero_add]
      -- Remaining terms: shift by k reduces to original sum
      apply Finset.sum_congr rfl
      intro i hi
      rw [List.getD_append_right _ _ _ _ (by rw [zeroSeq_length]; omega),
          zeroSeq_length, show k + i - k = i from Nat.add_sub_cancel_left k i,
          List.getD_append_right _ _ _ _ (by rw [zeroSeq_length]; omega),
          zeroSeq_length, show k + i + s - k = i + s from by omega]

/-- Pointwise identity: for ±1 values u, v, u', v',
    2 * ((u+v)/2 * ((u'+v')/2) + (u-v)/2 * ((u'-v')/2)) = u*u' + v*v'. -/
private lemma pointwise_half_sq (u v u' v' : Int)
    (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1)
    (hu' : u' = 1 ∨ u' = -1) (hv' : v' = 1 ∨ v' = -1) :
    2 * ((u + v) / 2 * ((u' + v') / 2) + (u - v) / 2 * ((u' - v') / 2)) =
    u * u' + v * v' := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl <;> norm_num

/-- For a ±1 list, `getD i 0` is ±1 when `i < length`. -/
private lemma allPmOne_getD (a : List Int) (ha : AllPmOne a) (i : Nat) (hi : i < a.length) :
    a.getD i 0 = 1 ∨ a.getD i 0 = -1 := by
  rw [List.getD_eq_getElem _ _ hi]
  exact ha _ (List.getElem_mem hi)

/-- Half-sum/half-difference autocorrelation identity for ±1 sequences. -/
lemma sumHalf_diffHalf_autocorr (a b : List Int) (s : Nat)
    (hab : a.length = b.length) (ha : AllPmOne a) (hb : AllPmOne b) :
    2 * (aperiodicAutocorr (seqSumHalf a b) s +
         aperiodicAutocorr (seqDiffHalf a b) s) =
    aperiodicAutocorr a s + aperiodicAutocorr b s := by
  have hSlen : (seqSumHalf a b).length = a.length := by
    simp only [seqSumHalf, List.length_zipWith, hab, Nat.min_self]
  have hDlen : (seqDiffHalf a b).length = a.length := by
    simp only [seqDiffHalf, List.length_zipWith, hab, Nat.min_self]
  unfold aperiodicAutocorr
  by_cases hs : s ≥ a.length
  · rw [if_pos (by omega), if_pos (by omega), if_pos hs, if_pos (by omega)]
    norm_num
  · push_neg at hs
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        hSlen, hDlen, ← hab, ← Finset.sum_add_distrib, Finset.mul_sum,
        ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hi_lt : i < a.length := by omega
    have his_lt : i + s < a.length := by omega
    rw [seqSumHalf_getD hab hi_lt, seqSumHalf_getD hab his_lt,
        seqDiffHalf_getD hab hi_lt, seqDiffHalf_getD hab his_lt]
    exact pointwise_half_sq _ _ _ _
      (allPmOne_getD a ha i hi_lt)
      (allPmOne_getD b hb i (by omega))
      (allPmOne_getD a ha (i + s) his_lt)
      (allPmOne_getD b hb (i + s) (by omega))

/-- Length of seqSumHalf. -/
@[simp] lemma seqSumHalf_length (a b : List Int) :
    (seqSumHalf a b).length = min a.length b.length := by
  simp [seqSumHalf, List.length_zipWith]

/-- Length of seqDiffHalf. -/
@[simp] lemma seqDiffHalf_length (a b : List Int) :
    (seqDiffHalf a b).length = min a.length b.length := by
  simp [seqDiffHalf, List.length_zipWith]

/-- Combined aperiodic autocorrelation of the step2 sequences vanishes. -/
lemma step2_aperiodic_vanishing {n : Nat} (T : TurynType n) (s : Nat) (hs : 1 ≤ s) :
    aperiodicAutocorr (step2a T) s + aperiodicAutocorr (step2b T) s +
    aperiodicAutocorr (step2c T) s + aperiodicAutocorr (step2d T) s = 0 := by
  simp only [step2a, step2b, step2c, step2d]
  rw [aperiodicAutocorr_append_zeros,
      aperiodicAutocorr_prepend_zeros,
      aperiodicAutocorr_append_zeros,
      aperiodicAutocorr_prepend_zeros,
      aperiodicAutocorr_prepend_zeros]
  have hxy : T.x.data.length = T.y.data.length := by rw [T.x.len, T.y.len]
  have hXY := sumHalf_diffHalf_autocorr T.x.data T.y.data s hxy T.x.pm T.y.pm
  have hbase := concat_neg_autocorr_sum T.z.data T.w.data s
  by_cases hsn : s < n
  · have := T.vanishing s hs hsn
    unfold combinedAutocorr at this
    linarith
  · simp only [not_lt] at hsn
    rw [aperiodicAutocorr_zero_of_ge T.z.data s (by rw [T.z.len]; omega),
        aperiodicAutocorr_zero_of_ge T.w.data s (by rw [T.w.len]; omega)]
    have : aperiodicAutocorr (seqSumHalf T.x.data T.y.data) s = 0 := by
      apply aperiodicAutocorr_zero_of_ge
      rw [seqSumHalf_length]
      simp only [hxy, Nat.min_self]
      rw [T.y.len]
      omega
    have : aperiodicAutocorr (seqDiffHalf T.x.data T.y.data) s = 0 := by
      apply aperiodicAutocorr_zero_of_ge
      rw [seqDiffHalf_length]
      simp only [hxy, Nat.min_self]
      rw [T.y.len]
      omega
    linarith

/-- Step 2 periodic vanishing: combined periodic autocorrelation of T-sequences vanishes. -/
theorem step2_periodic {n : Nat} (T : TurynType n) :
    ∀ s, 1 ≤ s → s < 3 * n - 1 →
      combinedPeriodicAutocorr (step2a T) (step2b T) (step2c T) (step2d T) s = 0 := by
  intro s hs1 hs2
  unfold combinedPeriodicAutocorr
  -- Use the decomposition: periodicAutocorr a s = aperiodicAutocorr a s + aperiodicAutocorr a (m-s)
  set m := 3 * n - 1
  -- We need all four sequences to have length m
  have ha_len : (step2a T).length = m := by
    simp [step2a, zeroSeq, T.z.len]; omega
  have hb_len : (step2b T).length = m := by
    simp [step2b, zeroSeq, T.w.len]; omega
  have hc_len : (step2c T).length = m := by
    simp [step2c, zeroSeq, seqSumHalf, List.length_zipWith, T.x.len, T.y.len]; omega
  have hd_len : (step2d T).length = m := by
    simp [step2d, zeroSeq, seqDiffHalf, List.length_zipWith, T.x.len, T.y.len]; omega
  have hm : m > 0 := by omega
  rw [periodic_eq_aperiodic_sum _ s (by omega) (by rw [ha_len]; omega),
      periodic_eq_aperiodic_sum _ s (by omega) (by rw [hb_len]; omega),
      periodic_eq_aperiodic_sum _ s (by omega) (by rw [hc_len]; omega),
      periodic_eq_aperiodic_sum _ s (by omega) (by rw [hd_len]; omega)]
  rw [ha_len, hb_len, hc_len, hd_len]
  have h1 := step2_aperiodic_vanishing T s hs1
  have h2 := step2_aperiodic_vanishing T (m - s) (by omega)
  linarith

/-- Step 2 as a typed function from Turyn data to a certified T-sequence. -/
def step2 {n : Nat} (T : TurynType n) : TSequence (3 * n - 1) :=
  { a := step2a T
    b := step2b T
    c := step2c T
    d := step2d T
    a_len := by
      simp [step2a, zeroSeq, T.z.len]
      omega
    b_len := by
      simp [step2b, zeroSeq, T.w.len]
      omega
    c_len := by
      simp [step2c, zeroSeq, seqSumHalf, List.length_zipWith, T.x.len, T.y.len]
      omega
    d_len := by
      simp [step2d, zeroSeq, seqDiffHalf, List.length_zipWith, T.x.len, T.y.len]
      omega
    support := by
      intro i hi
      exact step2_support T i hi
    periodic_vanishing := by
      intro s hs1 hs2
      exact step2_periodic T s hs1 hs2 }
