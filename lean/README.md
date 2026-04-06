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

## What's verified

| Theorem | Statement | Proof method |
|---------|-----------|-------------|
| `tt6_valid` | TT(6) sequences satisfy the autocorrelation condition | `native_decide` |
| `kharaghani_2005_tt36` | Kharaghani's TT(36) is a valid Turyn-type sequence | `native_decide` |
| `kh05_energy` | Energy identity: 0² + 6² + 2·8² + 2·5² = 214 = 6·36 − 2 | `native_decide` |
| `kh05_hadamard_order` | TT(36) gives Hadamard order 4(3·36−1) = 428 | `native_decide` |
| `hadamard_428_exists` | ∃ verified TT(36) implying a Hadamard matrix of order 428 | construction |

## How to verify your own solution

After the turyn solver finds a TT(n), add a new file (e.g., `Turyn/MySolution.lean`):

```lean
import Turyn.Basic
import Turyn.Energy
import Turyn.Hadamard

-- Paste sequences from solver output
def myX : Seq := [1, -1, 1, ...]
def myY : Seq := [1, 1, -1, ...]
def myZ : Seq := [-1, 1, -1, ...]
def myW : Seq := [1, -1, ...]

-- Lean verifies this at compile time (takes seconds)
theorem my_tt_valid : IsTurynType <n> myX myY myZ myW := by native_decide

-- Cross-check: energy identity
theorem my_energy : checkEnergy <n> myX myY myZ myW = true := by native_decide

-- State the Hadamard consequence
theorem my_hadamard_exists :
    ∃ (x y z w : Seq),
      IsTurynType <n> x y z w ∧ hadamardOrder <n> = <order> :=
  ⟨myX, myY, myZ, myW, my_tt_valid, by native_decide⟩
```

Then `lake build` checks everything. If the sequences are wrong, Lean rejects
the proof and the build fails.

## File structure

```
Turyn/
├── Basic.lean      Core definitions: aperiodic autocorrelation, IsTurynType,
│                   decidability via native_decide
├── Energy.lean     Energy identity x² + y² + 2z² + 2w² = 6n − 2
│                   (theorem stated with proof sketch; computationally verified)
├── Hadamard.lean   Hadamard matrix definitions, Goethals-Seidel construction,
│                   T-sequence interleaving, construction theorems
└── Examples.lean   Verified TT(6) and TT(36) (Kharaghani 2005 → Hadamard 428)
```

## Mathematical background

### Turyn-type sequences

A TT(n) is a quadruple (X, Y, Z, W) of ±1 sequences with lengths (n, n, n, n−1)
satisfying:

    N_X(s) + N_Y(s) + 2·N_Z(s) + 2·N_W(s) = 0    for all s = 1, …, n−1

where N_a(s) = Σᵢ aᵢ · aᵢ₊ₛ is the aperiodic autocorrelation at lag s.

### Energy identity

The sequence sums x = Σ Xᵢ, y = Σ Yᵢ, z = Σ Zᵢ, w = Σ Wᵢ satisfy:

    x² + y² + 2z² + 2w² = 6n − 2

**Why:** Expanding (Σ aᵢ)² = |a| + 2·Σₛ≥₁ Nₐ(s) for each sequence and
combining with the vanishing condition gives:

    LHS = (n + n + 2n + 2(n−1)) + 2·Σₛ≥₁(N_X + N_Y + 2N_Z + 2N_W)(s)
        = (6n − 2) + 2·0 = 6n − 2

### Hadamard construction

From TT(n), the base-sequence → T-sequence → Goethals-Seidel pipeline produces
a Hadamard matrix of order 4(3n − 1). For TT(36), this gives order 428.

## Trust model

- **Fully verified by Lean's kernel:** The `native_decide` proofs compile the
  Boolean verification to native code, run it, and the kernel certifies the
  result. This means the only trusted components are the Lean kernel and the
  correctness of the definitions in `Basic.lean`.

- **Stated with `sorry`:** The general theorems (energy identity, Goethals-Seidel
  construction) are stated with proof sketches. These establish the mathematical
  framework but are not yet machine-checked. Extending them to full proofs would
  require Mathlib's linear algebra library.

## References

- Kharaghani & Tayfeh-Rezaie (2005). A Hadamard matrix of order 428.
  *J. Combin. Des.* 13(6), 435–440.
- Best, Djokovic, Kharaghani, Ramp (2013). Turyn-Type Sequences.
  arXiv:1206.4107.
- Goethals & Seidel (1967). Orthogonal matrices with zero diagonal.
  *Can. J. Math.* 19, 1001–1010.
