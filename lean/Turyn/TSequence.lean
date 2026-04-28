import Turyn.BaseSequence
import Turyn.MatUtils
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option linter.unusedSimpArgs false

open Finset BigOperators

/-!
# T-Sequences (Function-typed)

Typed T-sequences with `Fin m → Int` carriers and the standard construction
from Turyn-type input. The main results show that the constructed sequences
have disjoint `{0, ±1}` support and vanishing combined periodic
autocorrelation.
-/

/-- The Hadamard order produced by the Turyn pipeline. -/
def hadamardOrder (n : Nat) : Nat := 4 * (3 * n - 1)

/-- Typed T-sequence of length `m`.  Each component is a `SignSeq m`
    (entries in `{0, ±1}`, carried as `Fin m → Int`). -/
structure TSequence (m : Nat) where
  a : SignSeq m
  b : SignSeq m
  c : SignSeq m
  d : SignSeq m
  support : ∀ i : Fin m,
    Int.natAbs (a.data i) + Int.natAbs (b.data i) +
      Int.natAbs (c.data i) + Int.natAbs (d.data i) = 1
  periodic_vanishing :
    ∀ s : Fin m, s.1 ≠ 0 →
      Turyn.periodicAutocorr a.data s + Turyn.periodicAutocorr b.data s +
        Turyn.periodicAutocorr c.data s + Turyn.periodicAutocorr d.data s = 0

/-! ### Step 2 component functions -/

/-- Step 2a: Z in positions `[0, n)`, zero elsewhere. -/
def step2a {n : Nat} (T : TurynType n) : Fin (3 * n - 1) → Int :=
  fun i => if h : i.1 < n then T.Z.data ⟨i.1, h⟩ else 0

/-- Step 2b: W in positions `[n, 2n−1)`, zero elsewhere. -/
def step2b {n : Nat} (T : TurynType n) : Fin (3 * n - 1) → Int :=
  fun i =>
    if h1 : i.1 < n then 0
    else if h2 : i.1 < 2 * n - 1 then T.W.data ⟨i.1 - n, by omega⟩
    else 0

/-- Step 2c: `(X + Y) / 2` in positions `[2n−1, 3n−1)`, zero elsewhere. -/
def step2c {n : Nat} (T : TurynType n) : Fin (3 * n - 1) → Int :=
  fun i =>
    if h : i.1 < 2 * n - 1 then 0
    else (T.X.data ⟨i.1 - (2 * n - 1), by have := i.2; omega⟩ +
          T.Y.data ⟨i.1 - (2 * n - 1), by have := i.2; omega⟩) / 2

/-- Step 2d: `(X − Y) / 2` in positions `[2n−1, 3n−1)`, zero elsewhere. -/
def step2d {n : Nat} (T : TurynType n) : Fin (3 * n - 1) → Int :=
  fun i =>
    if h : i.1 < 2 * n - 1 then 0
    else (T.X.data ⟨i.1 - (2 * n - 1), by have := i.2; omega⟩ -
          T.Y.data ⟨i.1 - (2 * n - 1), by have := i.2; omega⟩) / 2

/-- Element-wise half-sum. -/
def halfSumFn {n : Nat} (x y : Fin n → Int) : Fin n → Int :=
  fun i => (x i + y i) / 2

/-- Element-wise half-difference. -/
def halfDiffFn {n : Nat} (x y : Fin n → Int) : Fin n → Int :=
  fun i => (x i - y i) / 2

/-! ### Small helper lemmas -/

/-- `natAbs` of a ±1 entry is 1. -/
lemma PmSeq_natAbs_eq_one {n : Nat} (s : PmSeq n) (i : Fin n) :
    Int.natAbs (s.data i) = 1 := by
  rcases s.pm i with h | h <;> rw [h] <;> decide

/-- For two ±1 values, exactly one of the half-sum and half-difference
    has absolute value 1. -/
private lemma natAbs_halfSum_add_natAbs_halfDiff_eq_one (u v : Int)
    (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) :
    Int.natAbs ((u + v) / 2) + Int.natAbs ((u - v) / 2) = 1 := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> decide

/-! ### Support theorem -/

theorem step2_support {n : Nat} (T : TurynType n) (i : Fin (3 * n - 1)) :
    Int.natAbs (step2a T i) + Int.natAbs (step2b T i) +
      Int.natAbs (step2c T i) + Int.natAbs (step2d T i) = 1 := by
  unfold step2a step2b step2c step2d;
  split_ifs <;> simp_all +decide [ PmSeq_natAbs_eq_one ];
  · omega;
  · convert natAbs_halfSum_add_natAbs_halfDiff_eq_one _ _ _ _ using 1;
    · exact T.X.pm _;
    · exact T.Y.pm _

/-! ### AllSignOne for step2 components -/

lemma step2a_sign {n : Nat} (T : TurynType n) : AllSignOne (step2a T) := by
  unfold step2a;
  intro i; by_cases hi : ( i : ℕ ) < n <;> simp +decide [ hi ] ;
  exact Or.inr <| T.Z.pm _

lemma step2b_sign {n : Nat} (T : TurynType n) : AllSignOne (step2b T) := by
  intro i;
  unfold step2b;
  split_ifs <;> norm_num;
  exact Or.inr <| T.W.pm _

lemma step2c_sign {n : Nat} (T : TurynType n) : AllSignOne (step2c T) := by
  intro i
  unfold step2c
  simp [AllSignOne];
  split_ifs <;> norm_num;
  · omega;
  · cases T.X.pm ⟨ i - ( 2 * n - 1 ), by omega ⟩ <;> cases T.Y.pm ⟨ i - ( 2 * n - 1 ), by omega ⟩ <;> simp +decide [ * ]

lemma step2d_sign {n : Nat} (T : TurynType n) : AllSignOne (step2d T) := by
  intro i;
  unfold step2d;
  split_ifs <;> norm_num;
  rcases T.X.pm ⟨ i - ( 2 * n - 1 ), by omega ⟩ with ha | ha <;> rcases T.Y.pm ⟨ i - ( 2 * n - 1 ), by omega ⟩ with hb | hb <;> norm_num [ ha, hb ]

/-! ### Aperiodic autocorrelation of shifted-support functions -/

/-
If `f : Fin M → Int` has support in `[off, off + N)` and agrees with
    `g : Fin N → Int` on that interval, their aperiodic autocorrelations agree.
-/
lemma aperiodicAutocorr_of_support {M N off : Nat}
    (f : Fin M → Int) (g : Fin N → Int) (s : Nat)
    (hle : off + N ≤ M)
    (hlo : ∀ i, i < off → lookupNat f i = 0)
    (hhi : ∀ i, off + N ≤ i → lookupNat f i = 0)
    (heq : ∀ j, j < N → lookupNat f (off + j) = lookupNat g j) :
    aperiodicAutocorr f s = aperiodicAutocorr g s := by
  unfold aperiodicAutocorr;
  split_ifs <;> try omega;
  · refine Finset.sum_eq_zero fun i hi => ?_;
    grind;
  · -- For the sum over the range (M - s), split it into two parts: one where $i < off$ and one where $i \geq off$.
    have h_split_sum : ∑ i ∈ Finset.range (M - s), lookupNat f i * lookupNat f (i + s) = ∑ i ∈ Finset.Ico off (off + (N - s)), lookupNat f i * lookupNat f (i + s) := by
      rw [ ← Finset.sum_subset ];
      · exact fun x hx => Finset.mem_range.mpr ( by linarith [ Finset.mem_Ico.mp hx, Nat.sub_add_cancel ( by linarith : s ≤ N ), Nat.sub_add_cancel ( by linarith : s ≤ M ) ] );
      · grind;
    rw [ h_split_sum, Finset.sum_Ico_eq_sum_range ];
    simp +zetaDelta at *;
    grind +suggestions

/-! ### Application to each step2 component -/

lemma aperiodicAutocorr_step2a {n : Nat} (T : TurynType n) (s : Nat) :
    aperiodicAutocorr (step2a T) s = aperiodicAutocorr T.Z.data s := by
  convert aperiodicAutocorr_of_support _ _ _ _ _ _ _ using 3;
  exact 0;
  · omega;
  · tauto;
  · unfold lookupNat;
    unfold step2a; aesop;
  · unfold step2a lookupNat;
    grind

lemma aperiodicAutocorr_step2b {n : Nat} (T : TurynType n) (s : Nat) :
    aperiodicAutocorr (step2b T) s = aperiodicAutocorr T.W.data s := by
  convert aperiodicAutocorr_of_support _ _ _ _ _ _ _ using 3;
  exact n;
  · omega;
  · unfold step2b lookupNat; aesop;
  · unfold lookupNat;
    unfold step2b;
    grind;
  · unfold step2b lookupNat;
    grind

lemma aperiodicAutocorr_step2c {n : Nat} (T : TurynType n) (s : Nat) :
    aperiodicAutocorr (step2c T) s =
      aperiodicAutocorr (halfSumFn T.X.data T.Y.data) s := by
  apply aperiodicAutocorr_of_support;
  case off => exact 2 * n - 1;
  · omega;
  · unfold lookupNat step2c;
    grind;
  · grind +suggestions;
  · intro j hj; simp +decide [ lookupNat, step2c, halfSumFn ] ;
    grind +splitImp

lemma aperiodicAutocorr_step2d {n : Nat} (T : TurynType n) (s : Nat) :
    aperiodicAutocorr (step2d T) s =
      aperiodicAutocorr (halfDiffFn T.X.data T.Y.data) s := by
  apply aperiodicAutocorr_of_support;
  case off => exact 2 * n - 1;
  · omega;
  · unfold lookupNat;
    unfold step2d; aesop;
  · unfold lookupNat;
    grind;
  · unfold lookupNat;
    unfold step2d halfDiffFn;
    grind

/-! ### Half-sum / half-difference identity -/

/-- Pointwise algebraic identity for ±1 values. -/
private lemma pointwise_half_sq (u v u' v' : Int)
    (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1)
    (hu' : u' = 1 ∨ u' = -1) (hv' : v' = 1 ∨ v' = -1) :
    2 * ((u + v) / 2 * ((u' + v') / 2) + (u - v) / 2 * ((u' - v') / 2)) =
    u * u' + v * v' := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl <;> norm_num

lemma halfSum_halfDiff_autocorr {n : Nat} (x y : Fin n → Int)
    (hx : AllPmOne x) (hy : AllPmOne y) (s : Nat) :
    2 * (aperiodicAutocorr (halfSumFn x y) s +
         aperiodicAutocorr (halfDiffFn x y) s) =
    aperiodicAutocorr x s + aperiodicAutocorr y s := by
  unfold aperiodicAutocorr;
  split_ifs <;> simp_all +decide [ lookupNat, Finset.sum_add_distrib, mul_add ];
  rw [ ← mul_add, ← Finset.sum_add_distrib ];
  rw [ ← Finset.sum_add_distrib, Finset.mul_sum ];
  refine' Finset.sum_congr rfl fun i hi => _;
  split_ifs <;> simp_all +decide [ Nat.lt_succ_iff ];
  convert pointwise_half_sq ( x ⟨ i, by linarith ⟩ ) ( y ⟨ i, by linarith ⟩ ) ( x ⟨ i + s, by linarith ⟩ ) ( y ⟨ i + s, by linarith ⟩ ) ( hx _ ) ( hy _ ) ( hx _ ) ( hy _ ) using 1

/-! ### Periodic–aperiodic decomposition -/

/-
Periodic autocorrelation decomposes into two aperiodic terms.
-/
lemma periodicAutocorr_eq_aperiodic {m : Nat} (x : Fin m → Int) (s : Fin m)
    (hs : s.1 ≠ 0) :
    Turyn.periodicAutocorr x s =
      aperiodicAutocorr x s.1 + aperiodicAutocorr x (m - s.1) := by
  unfold Turyn.periodicAutocorr aperiodicAutocorr lookupNat;
  rw [ Finset.sum_fin_eq_sum_range ];
  split_ifs <;> simp_all +decide [ Nat.sub_sub_self ( show ↑s ≤ m from s.2.le ) ];
  · exact absurd ‹_› ( not_le_of_gt s.2 );
  · exact absurd ‹_› ( not_le_of_gt ( Nat.sub_lt ( Fin.pos s ) ( Nat.pos_of_ne_zero hs ) ) );
  · rw [ ← Finset.sum_range_add_sum_Ico _ ( show m - s ≤ m from Nat.sub_le _ _ ) ];
    refine' congrArg₂ ( · + · ) _ _;
    · refine' Finset.sum_congr rfl fun i hi => _;
      split_ifs <;> simp_all +decide [ Fin.add_def, Nat.mod_eq_of_lt ];
      omega;
    · refine' Finset.sum_bij ( fun k hk => k - ( m - s ) ) _ _ _ _ <;> simp_all +decide [ Fin.add_def, Nat.mod_eq_of_lt ];
      · intros; omega;
      · intros; omega;
      · exact fun b hb => ⟨ b + ( m - s ), ⟨ by omega, by omega ⟩, by omega ⟩;
      · intro a hp hq; split_ifs <;> simp_all +decide [ Nat.mod_eq_sub_mod, Nat.sub_sub ] ;
        · simp +decide [ Nat.mod_eq_of_lt ( show a + s - m < m from by omega ), mul_comm ];
          grind;
        · omega

/-! ### Combined vanishing -/

lemma step2_aperiodic_vanishing {n : Nat} (T : TurynType n) (s : Nat) (hs : 1 ≤ s) :
    aperiodicAutocorr (step2a T) s + aperiodicAutocorr (step2b T) s +
      aperiodicAutocorr (step2c T) s + aperiodicAutocorr (step2d T) s = 0 := by
  rw [aperiodicAutocorr_step2a, aperiodicAutocorr_step2b,
      aperiodicAutocorr_step2c, aperiodicAutocorr_step2d]
  have hXY := halfSum_halfDiff_autocorr T.X.data T.Y.data T.X.pm T.Y.pm s
  by_cases hsn : s < n
  · have hvan := T.vanishing s hs hsn
    unfold combinedAutocorr at hvan
    linarith
  · rw [aperiodicAutocorr_zero_of_ge T.Z.data s (by omega),
        aperiodicAutocorr_zero_of_ge T.W.data s (by omega),
        aperiodicAutocorr_zero_of_ge (halfSumFn T.X.data T.Y.data) s (by omega),
        aperiodicAutocorr_zero_of_ge (halfDiffFn T.X.data T.Y.data) s (by omega)]
    ring

theorem step2_periodic {n : Nat} (T : TurynType n) (s : Fin (3 * n - 1))
    (hs : s.1 ≠ 0) :
    Turyn.periodicAutocorr (step2a T) s + Turyn.periodicAutocorr (step2b T) s +
      Turyn.periodicAutocorr (step2c T) s + Turyn.periodicAutocorr (step2d T) s = 0 := by
  rw [periodicAutocorr_eq_aperiodic (step2a T) s hs,
      periodicAutocorr_eq_aperiodic (step2b T) s hs,
      periodicAutocorr_eq_aperiodic (step2c T) s hs,
      periodicAutocorr_eq_aperiodic (step2d T) s hs]
  have h1 := step2_aperiodic_vanishing T s.1 (by omega)
  have h2 := step2_aperiodic_vanishing T (3 * n - 1 - s.1) (by have := s.2; omega)
  linarith

/-- Step 2: Turyn-type to T-sequence. -/
def step2 {n : Nat} (T : TurynType n) : TSequence (3 * n - 1) :=
  { a := ⟨step2a T, step2a_sign T⟩
    b := ⟨step2b T, step2b_sign T⟩
    c := ⟨step2c T, step2c_sign T⟩
    d := ⟨step2d T, step2d_sign T⟩
    support := step2_support T
    periodic_vanishing := step2_periodic T }