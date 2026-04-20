# Data Corpus Analysis

Data source: [`data/`](../data/) from <https://www.cs.uleth.ca/~hadi/research/TurynType/>.

Tool: [`src/bin/analyze_data.rs`](../src/bin/analyze_data.rs)

Run with:

```bash
cargo run --release --bin analyze_data
```

The tool decodes the published hex format, reconstructs the missing tail bits,
canonicalizes each solution under the full BDKR symmetry group, verifies the
Turyn identity, and prints corpus statistics.

## What seems useful

### 1. Canonical-rule witnesses are usually very early

Across all 28,029 canonical representatives for `n <= 32`:

- rule (ii) witness in `X` is at position `<= 4` for **89.0%**
- rule (iii) witness in `Y` is at position `<= 4` for **89.4%**
- rule (iv) witness in `Z` is at position `<= 4` for **94.0%**
- rule (v) witness in `W` is at position `<= 4` for **93.3%**

Implication:

- if a boundary/MDD layer sees the first four positions on each side, it captures
  most of the symmetry-breaking benefit already
- the outstanding TODO in `docs/CANONICAL.md` about stateful MDD pruning for
  rules (ii)-(v) is likely worth doing, especially when `k >= 4`
- for `k < 4`, a lot of canonical pruning is still deferred to the SAT or
  post-walk filters

### 2. Small boundaries have very high reuse, but `k=5` is almost injective

For the larger instances:

- at `n=32`, `k=3` yields only **218** distinct canonical boundaries for **6292**
  solutions; the largest bucket has **124** completions
- at `n=32`, `k=4` yields **2850** boundaries for **6292** solutions
- at `n=32`, `k=5` yields **5989** boundaries for **6292** solutions
- at `n=32`, `k=6` yields **6278** boundaries for **6292** solutions

The same pattern is stable from `n=22` through `n=32`:

- `k=3`: very coarse, heavy reuse
- `k=4`: still materially reusable
- `k=5`: already near one-solution-per-boundary
- `k>=6`: essentially unique

Implication:

- `k=4` looks like a strong compromise point for reusable boundary tables /
  learned boundary scoring
- `k=5` looks like a strong compromise point for near-terminal lookup because
  it almost identifies a full solution already
- pushing structural MDD work much past `k=5` may have diminishing returns if
  the goal is reuse rather than exact reconstruction

### 3. Some bit positions are strongly biased and could drive branching/phase heuristics

Empirically, in the canonical corpus:

- `X[2] = +1` in **100%** of solutions up to `n=32`
- `Y[n-1] = -1` in **100%** of solutions up to `n=32`
- `Z[2] = +1` is around **78-84%**
- `W[2] = +1` is around **78-83%**
- `X[3]`, `Y[3]`, `W[3]` are usually in the **60-65%** range
- true middle positions are close to unbiased, typically near **50/50**

Implication:

- these should be treated as **heuristics**, not hard constraints
- they are good candidates for SAT phase initialization, DFS branch ordering,
  and stochastic warm starts
- they do **not** suggest strong hard structure in the middle; the edge bias
  drops off quickly after the first few positions

### 4. Signed tuple ordering helps somewhat, but tuple frequency alone is too flat

For larger `n`, the most common tuple is only about **1.6-3.3%** of the corpus.
By `n=32`:

- `P(σ_X >= 0) = 72.7%`
- `P(σ_Y >= 0) = 58.4%`
- `P(σ_Z >= 0) = 63.6%`
- `P(σ_W > 0) = 66.2%`

Implication:

- signed tuples must remain in the search for completeness
- heuristic tuple ordering should prefer positive `σ_X`, then positive `σ_W`,
  then positive `σ_Z`
- but tuple priors alone are unlikely to give order-of-magnitude gains, because
  the distribution is too diffuse

## What does **not** look promising

### Same-position equalities

For `n >= 22` the rates stay near:

- `P(X[i] = Y[i]) ~= 52%`
- `P(Z[i] = W[i]) ~= 51%`
- `P(X[i] = Z[i]) ~= 52%`

Implication:

- there is no strong same-index coupling to exploit directly
- heuristics based on forcing two sequences to agree/disagree at the same
  position are unlikely to pay off

## Practical next steps

1. Implement stateful MDD pruning for canonical rules (ii)-(v) when `k >= 4`.
2. Add SAT phase hints / DFS branch ordering using the empirical edge priors:
   `X[2]=+` strongly first, then `Z[2]=+`, `W[2]=+`, then `X[3]`, `Y[3]`, `W[3]`.
3. Order signed tuples heuristically by positive `σ_X`, positive `σ_W`,
   positive `σ_Z`, but keep the search complete.
4. If we want a learned boundary scorer, train it on `k=4` or `k=5` boundaries,
   not larger ones.

## Caveat

Everything above is empirical from `n <= 32`. The only safe hard constraints are
the proved BDKR canonical rules and the Turyn identities. The new bit-position
patterns should be treated as heuristic guidance unless we can prove them.
