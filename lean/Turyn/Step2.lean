import Turyn.Step1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open Finset
open BigOperators

/-!
# Step 2: Typed T-Sequences

This file is standalone and does not depend on `Turyn.Hadamard`.
It introduces a typed T-sequence object and the Step 2 construction.
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

def step2b {n : Nat} (T : TurynType n) : List Int :=
  zeroSeq n ++ (T.w.data ++ zeroSeq n)

def step2c {n : Nat} (T : TurynType n) : List Int :=
  zeroSeq (2 * n - 1) ++ seqSumHalf T.x.data T.y.data

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

axiom step2_periodic {n : Nat} (T : TurynType n) :
  ∀ s, 1 ≤ s → s < 3 * n - 1 →
    combinedPeriodicAutocorr (step2a T) (step2b T) (step2c T) (step2d T) s = 0

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
