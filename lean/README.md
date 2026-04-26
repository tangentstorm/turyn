# Lean Formal Verification for Turyn-Type Sequences

Machine-checked proofs that a given set of ±1 sequences form a valid Turyn-type
quadruple TT(n), suitable for constructing Hadamard matrices.

## Quick start

```bash
# Install Lean 4 (if not already installed)
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Build and verify all proofs
cd lean
lake build
```

The build compiles all definitions and checks all proofs, including the
`native_decide` verification of the Kharaghani TT(36) sequences.

## Proof status

| Theorem | Status | Method |
|---------|--------|--------|
| `tt6_valid` | **Proved** | `native_decide` |
| `kharaghani_2005_tt36` | **Proved** | `native_decide` |
| `kh05_energy` | **Proved** | `native_decide` |
| `turyn_vanishing_total` | **Proved** | `rangeSum_eq_zero` + vanishing condition |
| `energy_identity` | **Proved** | Combines sum-sq identity + vanishing total |
| `IsTurynType.toProp` | **Proved** | Bool → Prop extraction |
| `sum_sq_eq_len_add_two_totalAutocorr` | Axiom | Requires Mathlib's `Finset.sum` + `ring` |
| `weightedTotalAutocorr_decompose` | Axiom | Requires Mathlib's `Finset.sum` linearity |
| `tseq_vanishing` | Axiom | Periodic/aperiodic autocorrelation relation |
| `goethals_seidel_is_hadamard` | Axiom | Circulant matrix algebra |

The two sum-decomposition axioms are straightforward with Mathlib: the first is
the algebraic identity (Σ aᵢ)² = Σ aᵢ² + 2·Σ_{i<j} aᵢaⱼ combined with ±1
simplification and lag regrouping; the second is linearity of `Finset.sum`.

## Architecture

```
Turyn/
├── TurynType.lean      Core definitions: aperiodic autocorrelation, IsTurynType
│                   (Bool + Prop), rangeSum helper, AllPmOne, decidability.
│                   Fully proved: IsTurynType.toProp, rangeSum lemmas.
├── Energy.lean     Energy identity x² + y² + 2z² + 2w² = 6n − 2.
│                   Proved: turyn_vanishing_total, energy_identity.
│                   Axioms: sum_sq identity, weighted decomposition.
├── Hadamard.lean   Hadamard matrix defs, T-sequence and Goethals-Seidel
│                   construction (computable). Axioms for correctness.
└── Examples.lean   Verified TT(6) and TT(36) (Kharaghani 2005 → Hadamard 428).
```

## How to verify your own solution

After the turyn solver finds a TT(n), add a new file:

```lean
import Turyn.TurynType
import Turyn.Energy
import Turyn.Hadamard

def myX : PmSeq := [1, -1, ...]
def myY : PmSeq := [1, 1, ...]
def myZ : PmSeq := [-1, 1, ...]
def myW : PmSeq := [1, -1, ...]

-- Lean verifies at compile time (takes seconds)
theorem my_tt_valid : IsTurynType N myX myY myZ myW := by native_decide
theorem my_energy : checkEnergy N myX myY myZ myW = true := by native_decide

theorem my_hadamard_exists :
    ∃ (x y z w : PmSeq),
      IsTurynType N x y z w ∧ hadamardOrder N = ORDER :=
  ⟨myX, myY, myZ, myW, my_tt_valid, by native_decide⟩
```

Then `lake build` checks everything. If the sequences are wrong, Lean rejects
the proof and the build fails.

## Mathematical background

### Turyn-type sequences

A TT(n) is a quadruple (X, Y, Z, W) of ±1 sequences with lengths (n, n, n, n−1)
satisfying:

    N_X(s) + N_Y(s) + 2·N_Z(s) + 2·N_W(s) = 0    for all s = 1, …, n−1

### Energy identity (proved)

The sequence sums satisfy x² + y² + 2z² + 2w² = 6n − 2.

**Why:** Expanding (Σ aᵢ)² = |a| + 2·Σₛ≥₁ Nₐ(s) for each sequence and
combining with the vanishing condition:

    LHS = (n + n + 2n + 2(n−1)) + 2·Σₛ≥₁(N_X + N_Y + 2N_Z + 2N_W)(s)
        = (6n − 2) + 2·0 = 6n − 2

### Hadamard construction

From TT(n), the base-sequence → T-sequence → Goethals-Seidel pipeline produces
a Hadamard matrix of order 4(3n − 1). For TT(36), this gives order 428.

## Trust model

- **Fully verified by Lean's kernel:** The `native_decide` proofs (TT verification,
  energy check, sums) are machine-checked. The energy identity theorem is proved
  from its axioms with full Lean kernel verification.

- **Axioms (4 total):** Two algebraic sum identities (provable with Mathlib's
  `Finset.sum` and `ring`), and two construction correctness axioms (T-sequence
  and Goethals-Seidel). These represent standard results from combinatorial
  design theory.

## Comparator-checkable headline results

The three headline theorems are exposed in a layout consumable by
[`leanprover/comparator`](https://github.com/leanprover/comparator):

```
Results.lean              -- challenge module: theorem statements with `sorry`
Proofs.lean               -- solution module: imports the proof files below
Proofs/
  TtToHadamard.lean       -- TT → Hadamard pipeline
  CanonicalForm.lean      -- canonical representative exists
  XyProductLaw.lean       -- XY product law
comparator-config.json    -- comparator configuration
```

The headline names live in the `Turyn.Result` namespace and are:

- `Turyn.Result.tt_implies_hadamard` —
  if a TT(n) exists, a Hadamard matrix of order `4 (3 n − 1)` exists.
- `Turyn.Result.canonical_form_exists` —
  every TT(n) is equivalent to a representative in canonical form
  (existence half of the BDKR result; uniqueness within the orbit is not
  yet formalized).
- `Turyn.Result.xy_interior_antipalindrome` —
  for a canonical TT(n) of length `n ≥ 4`, `uAt S (n + 1 − k) = − uAt S k`
  for every `2 ≤ k ≤ n − 1` (the BDKR XY product law).

Run comparator from the `lean/` directory after installing `landrun` and
`lean4export` (see the comparator README) with:

```bash
lake env <path-to-comparator-binary> comparator-config.json
```

## References

- Kharaghani & Tayfeh-Rezaie (2005). A Hadamard matrix of order 428.
  *J. Combin. Des.* 13(6), 435–440.
- Best, Djokovic, Kharaghani, Ramp (2013). Turyn-Type Sequences.
  arXiv:1206.4107.
- Goethals & Seidel (1967). Orthogonal matrices with zero diagonal.
  *Can. J. Math.* 19, 1001–1010.
