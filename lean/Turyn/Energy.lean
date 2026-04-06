/-!
# Energy Identity for Turyn-Type Sequences

For any TT(n) with sequences X, Y, Z (length n) and W (length n−1),
the sums x = Σ Xᵢ, y = Σ Yᵢ, z = Σ Zᵢ, w = Σ Wᵢ satisfy:

    x² + y² + 2z² + 2w² = 6n − 2

## Why this works

The proof follows from two facts:

**Fact 1 (Sum-autocorrelation identity):**
For any ±1 sequence `a` of length `k`:

    (Σᵢ aᵢ)² = k + 2 · Σ_{s=1}^{k-1} N_a(s)

*Proof:*  Expand (Σᵢ aᵢ)² = Σᵢ aᵢ² + 2·Σ_{i<j} aᵢaⱼ.
Since aᵢ ∈ {±1}, we have aᵢ² = 1, so Σᵢ aᵢ² = k.
The cross terms group by lag: Σ_{i<j} aᵢaⱼ = Σ_{s=1}^{k-1} N_a(s).

**Fact 2 (Turyn vanishing):**
N_X(s) + N_Y(s) + 2·N_Z(s) + 2·N_W(s) = 0 for all s ≥ 1.

**Combining:**
    x² + y² + 2z² + 2w²
  = (n + 2·Σ N_X(s)) + (n + 2·Σ N_Y(s))
    + 2·(n + 2·Σ N_Z(s)) + 2·((n-1) + 2·Σ N_W(s))
  = (n + n + 2n + 2(n-1))
    + 2·Σ_{s≥1} (N_X(s) + N_Y(s) + 2·N_Z(s) + 2·N_W(s))
  = (6n − 2) + 2 · 0
  = 6n − 2                                                   □

This is essentially Parseval's theorem applied to the combined power spectral
density: the vanishing autocorrelation forces the spectrum to be flat, so
evaluating at frequency zero gives the energy identity.
-/

import Turyn.Basic

/-! ### Sum-autocorrelation identity -/

/-- Total autocorrelation: sum of N_a(s) for s = 1, …, k−1. -/
def totalAutocorr (a : Seq) : Int :=
  (List.range (a.length - 1)).foldl (fun acc i =>
    acc + aperiodicAutocorr a (i + 1)) 0

/-- The sum-autocorrelation identity for ±1 sequences:

    (Σ aᵢ)² = |a| + 2 · Σ_{s≥1} N_a(s)

This is the key lemma connecting sequence sums to autocorrelations.
It follows from expanding the square and grouping cross-terms by lag. -/
theorem sum_sq_eq_len_add_two_totalAutocorr (a : Seq) (h : AllPmOne a) :
    (seqSum a) ^ 2 = a.length + 2 * totalAutocorr a := by
  sorry -- See module docstring for the mathematical proof.
         -- Full formalization requires a nontrivial induction on
         -- the double sum Σᵢ Σⱼ aᵢaⱼ with regrouping by lag s = j - i.

/-! ### Weighted total autocorrelation -/

/-- Weighted total autocorrelation: Σ_{s≥1} (N_X(s) + N_Y(s) + 2·N_Z(s) + 2·N_W(s)). -/
def weightedTotalAutocorr (x y z w : Seq) (n : Nat) : Int :=
  (List.range (n - 1)).foldl (fun acc i =>
    acc + combinedAutocorr x y z w (i + 1)) 0

/-- If (x, y, z, w) is TT(n), the weighted total autocorrelation is zero. -/
theorem turyn_vanishing_total (n : Nat) (x y z w : Seq)
    (h : IsTurynType n x y z w) :
    weightedTotalAutocorr x y z w n = 0 := by
  sorry -- Follows directly from unfolding the definition and using
         -- the fact that each shift's combined autocorrelation is zero.

/-! ### The Energy Identity -/

/-- **Energy identity:** For any TT(n), the sums satisfy
    x² + y² + 2z² + 2w² = 6n − 2.

This is a necessary condition for the existence of TT(n) and is used
in Phase A of the search to enumerate candidate sum-tuples. -/
theorem energy_identity (n : Nat) (x y z w : Seq)
    (htt : IsTurynType n x y z w)
    (hx : AllPmOne x) (hy : AllPmOne y) (hz : AllPmOne z) (hw : AllPmOne w)
    (hxl : x.length = n) (hyl : y.length = n)
    (hzl : z.length = n) (hwl : w.length = n - 1) :
    (seqSum x) ^ 2 + (seqSum y) ^ 2 +
    2 * (seqSum z) ^ 2 + 2 * (seqSum w) ^ 2 =
    6 * n - 2 := by
  sorry -- Proof sketch:
         -- By sum_sq_eq_len_add_two_totalAutocorr applied to each sequence:
         --   (seqSum x)² = n + 2 * totalAutocorr x
         --   (seqSum y)² = n + 2 * totalAutocorr y
         --   (seqSum z)² = n + 2 * totalAutocorr z
         --   (seqSum w)² = (n-1) + 2 * totalAutocorr w
         -- Substituting and collecting the autocorrelation terms:
         --   LHS = n + n + 2n + 2(n-1)
         --       + 2*(totalAutocorr x + totalAutocorr y
         --           + 2*totalAutocorr z + 2*totalAutocorr w)
         --       = (6n - 2) + 2 * weightedTotalAutocorr x y z w n
         --       = (6n - 2) + 0    [by turyn_vanishing_total]
         --       = 6n - 2

/-! ### Computational verification of the energy identity -/

/-- Compute x² + y² + 2z² + 2w² for a quadruple. -/
def energyLHS (x y z w : Seq) : Int :=
  (seqSum x) ^ 2 + (seqSum y) ^ 2 +
  2 * (seqSum z) ^ 2 + 2 * (seqSum w) ^ 2

/-- Compute 6n − 2. -/
def energyRHS (n : Nat) : Int := 6 * n - 2

/-- Boolean check that the energy identity holds for a given quadruple. -/
def checkEnergy (n : Nat) (x y z w : Seq) : Bool :=
  energyLHS x y z w == energyRHS n
