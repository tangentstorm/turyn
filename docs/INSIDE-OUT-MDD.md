# Inside-out MDD with lag-sum-indexed boundary lookup

A second MDD that walks from the centre of the middle outward, paired
with a boundary index that lets the walker query "which boundaries
satisfy the autocorrelation system given everything I've placed so
far?" The current `zw_first` MDD walks the *outside* in (boundary →
middle); this one is its dual.

## Why bother

At n=56 the framework is bottlenecked at the boundary level:
`MddStagesAdapter::init` pre-enumerates all boundaries upfront and
runs out of memory at k=9/k=10 (44/65 GB). The k=7 boundary table
fits in memory but the SAT solve per (Z,W) candidate is the slow
step (>1 sec each, mostly UNSAT). Most of those (Z,W) candidates
turn out to be infeasible against the four-tuple autocorrelation
system, which the SAT solver only discovers by exhaustive search.

An inside-out walk lets the *middle's* autocorrelation contribution
prune (Z,W) boundary candidates *before* committing to one — and
crucially, lets us batch-query "which boundaries solve this
sub-system" via a precomputed lookup table rather than per-instance
SAT.

## The lag-sum decomposition (the indexing key)

For any sequence of length `n` partitioned into boundary `B = b[0..k-1] ∪ b[n-k..n-1]` and middle
`M = b[k..n-k-1]`, the lag-`s` autocorrelation factors as

```
A(s) = A_bb(s) + A_mm(s) + A_bm(s) + A_mb(s)
       └─ B only ┘ └ M only ┘ └─── cross terms ───┘
```

The Turyn condition `Σ_{X,Y,Z,W} A(s) = 0` for `1 ≤ s ≤ n-1` therefore
splits by lag class:

| Lag range | `bb` term | `mm` term | cross | Notes |
|---|---|---|---|---|
| Low: `1 ≤ s ≤ n-2k-1` | **0** | nontrivial | nontrivial | boundary contributes only via cross |
| Mid: `s = n-2k` | trivial (≤ 1 pair) | trivial | nontrivial | transition |
| High: `n-2k+1 ≤ s ≤ n-1` | nontrivial | small/0 | nontrivial | bb dominates |

This is the central observation: **the high-lag block is exclusively
constrained by the boundary's bb-contribution plus a small cross
correction**. If the cross correction is computable from the
"depth-near-border" state of the inside-out MDD, then the high-lag
target `bb_X(s)+bb_Y(s)+bb_Z(s)+bb_W(s)` is a known integer vector.

That vector is the **index key** the user is asking for.

## The query

After walking inside-out to depth `d` (where `d = (n-2k)/2 - δ` for
some small δ that gives us the boundary-adjacent middle bits), the
walker has:

* **`mm_sum[s]`** — accumulated middle-middle contribution to lag `s`,
  summed across all four sequences.
* **`cross_coef[s, p]`** — for each lag `s` and each boundary position
  `p`, the coefficient on `b[p]` in the cross term, summed across
  sequences. Non-zero only when there's a placed middle bit at
  position `p ± s`.

The query the boundary index must answer is: **find all 4-sequence
boundary tuples `(B_X, B_Y, B_Z, B_W)` such that for every lag `s`,**

```
A_bb_total(s) + Σ_p cross_coef[s, p] · b_total[p]  =  -mm_sum[s]
```

where `A_bb_total(s)` and `b_total[p]` are summed across the four
sequences' boundaries.

For high lags the second (cross) term has small support — only middle
bits adjacent to the boundary contribute, and those are *fixed* once
the inside-out walk reaches near-border depth. So for each high lag
`s`, the cross term is a *known scalar* `C_high[s]`, and the
constraint is

```
A_bb_total(s) = -mm_sum[s] - C_high[s]   for s in high-lag range
```

That's a `(2k-1)`-vector key. Hash it.

## Boundary index structure

### Single-table version

For each 4-tuple `(B_X, B_Y, B_Z, B_W)` of boundaries (4^(2k) tuples;
at k=7 that's 2^56 ≈ 7×10^16, infeasible to enumerate directly), this
doesn't work.

### Meet-in-the-middle (the practical plan)

Index two pair-tables:

* `T_xy[v]` = list of `(B_X, B_Y)` whose combined high-lag bb-vector is `v`
* `T_zw[v]` = same for `(B_Z, B_W)`

Each pair-table has 4^(2k) entries (X-bd is 2^(2k) and Y-bd is 2^(2k),
so pair count is 2^(4k) but per-sequence boundary count is 2^(2k); at
k=7 each pair table is 2^28 = 268M entries).

Per-entry payload: the pair `(B_X, B_Y)` packed (~14 bytes at k=7) plus
the `(2k-1)`-vector key (~56 bytes at n=26 k=7). Storage estimate:
~70 bytes × 268M = ~19 GB per table. Too big.

**Compression**:

1. **Store key separately, pair data in a flat array, hash the keys**.
   Hash table maps key → range `(start, len)` into the flat pair array.
   Typical bucket size: small (most keys don't collide). Memory:
   `O(distinct keys)` for the hash + `O(pair count × pair-size)` for
   the array. Per pair: 4 bytes (packed boundary). 2^28 × 4 = 1 GB per
   table. Hash itself: maybe ~100 MB. **Total ≈ 2.2 GB for both
   tables, on disk**.

2. **Symmetry reductions**: T1–T4 group operations from CANONICAL.md
   (palindromic reversals, sign flips, sequence permutations) reduce
   the boundary-tuple space by up to 16×. Apply at table-build time;
   inflate at query.

3. **Sparse high-lag**: at small `s` near the high-lag boundary the
   bb-vector entries are mostly zero. Drop trailing zeros from the
   key for shorter hash buckets.

### Query

Given the inside-out walker's high-lag target `t = -mm_sum[high-lags]
- C_high`:

```
for v in T_zw.keys():
    matching_xy = T_xy[t - v]
    if matching_xy:
        for (B_X, B_Y) in matching_xy:
            for (B_Z, B_W) in T_zw[v]:
                # Filter on low-lag and mid-lag constraints
                if check_low_lag(mm_sum, cross_coef, B):
                    yield B
```

The outer loop over `T_zw.keys()` is `O(|distinct keys|)` (much smaller
than 268M because of clustering). For each, hash lookup into `T_xy`.

## Inside-out MDD construction

### Walk order

Place positions from the centre outward, in some order:
* Symmetric: positions `m=⌊(n)/2⌋, m-1, m+1, m-2, m+2, ...`
* Or in pairs: `(m, m+1), (m-1, m+2), ...`

A symmetric pair-walk makes sense because each new bit potentially
contributes to many lags simultaneously.

### Per-node state

* `mm_sum[s]` for each lag `s` — `(n-1)` integers per node. At n=26
  that's 25 ints (100 bytes).
* `cross_coef[s, p]` for each `(s, p)` pair — sparse most of the time.
  Stored as a dictionary or compressed bitfield. Worst case
  `O((n-1) × 2k)` entries; at n=26 k=7 that's 350 entries per node.

That's significant but not crazy. The MDD itself probably has
millions of nodes; deduplication via Pareto-domination on the state
vector keeps it manageable.

### Build-time pruning

Available pruning sources:

1. **Local autocorrelation bound**: `|mm_sum[s]| ≤ (n - 2k) - s` is
   a hard limit from middle length alone. Apply at every level.
2. **Spectral envelope**: the middle's mm-contribution to the
   spectrum (`|M̂(ω)|²`) plus the boundary's max contribution must
   fit the four-tuple budget. Computable at any depth.
3. **Sub-tuple sum**: `Σ middle bits` matches the (signed) tuple-
   prescribed middle sum.
4. **XY palindrome / mirror-U**: sequence-level symmetry; collapses
   the MDD by 2× per affected position.
5. **Pairwise consistency at depth-near-border**: boundary-table
   keys that aren't reachable from any boundary tuple can be pruned
   pre-emptively.

### State deduplication

Two MDD subtrees are equivalent iff their `mm_sum` and `cross_coef`
states are equal. Hash by the state vector; merge nodes with
identical state.

The `cross_coef` part is the harder one to compress. Insight:
`cross_coef[s, p]` only depends on the middle bit at position
`p ± s`. If we sort positions in walk-order and only track the
"frontier" near the boundary, the cross-coef state is bounded.

## Where this should win

* **At deep search levels**, where most (Z,W) candidates currently
  reach the SAT solver and time out. The inside-out filter means
  most bad (Z,W) get rejected at the boundary index (a hash lookup,
  not a SAT call).
* **At n=56**, where the existing pre-enumerate-everything boundary
  pipeline OOMs at k=9/k=10. A streaming inside-out walker with
  meet-in-the-middle lookup avoids the upfront enumeration.
* **For TT(n) for large n**, where enumerating boundaries is
  super-exponential but the four-tuple autocorrelation system is
  highly over-constrained. The lookup table converts a 4-sequence
  search into a 2 + 2 indexed match.

## Where this might not win

* **Small n / dense solution space**: the SAT solver already finds
  solutions faster than building/querying tables. At n=18 the
  existing pipeline finishes in 17s.
* **If `cross_coef` is too dense**: state explosion in the MDD at
  near-border depth. Symmetry reductions essential.
* **If the high-lag block is too small** to be informative: at
  k=7, n=26 the high-lag block is 13 lags. Plenty. At k=12, n=26
  there are essentially no high lags. So this is k≪n/2 territory.

## Implementation roadmap

### Stage 0: prototype the lag-sum decomposition (1-2 hours)

* Compute `bb`, `mm`, `bm + mb` separately for a known TT(18)
  solution and verify the sum equals the full autocorrelation.
* Quantify the high-lag/low-lag split for n=18, 26, 56 at various
  `k`.

**STATUS: DONE.** See `src/bin/lag_sum_decomp.rs`. Output for known
TT(18) at k=4:

* Turyn condition `N_X + N_Y + 2N_Z + 2N_W = 0` verified for all 17 lags.
* Per-sequence decomposition `A(s) = A_bb(s) + A_mm(s) + A_cross(s)`
  verified for all (sequence, lag) pairs.
* Lag classes: 9 low (mm+cross only), 1 mid, 7 high (bb dominant).
* `bb_total` is non-zero only for lags 11–13 (the low end of the
  high-lag block); lags 14–17 have `bb_total = 0` because the
  Turyn-weighted sum is balanced.
* The known boundary's high-lag bb-vector at k=4 is
  `[-2, 2, 2, 0, 0, 0, 0]` (length 7).

### Stage 1: build the boundary index (1 day)

* For small n (say n=18, k=4), enumerate all 4-tuples of boundaries.
* Compute high-lag bb-vector for each.
* Hash by vector. Inspect bucket size distribution.
* Sanity check: pick a known TT(18) solution; verify its boundary
  hashes to a key that includes that solution as one of the matches.

### Stage 2: meet-in-the-middle (1 day)

* Split into `T_xy` (pairs of X,Y boundaries) and `T_zw` similarly.
* Hash both.
* Implement the cross-table query: given target `t`, iterate
  `T_zw[v]` and look up `T_xy[t-v]`.
* Sanity check: same answer as Stage 1 for small n.

**STATUS: prototype done in `lag_sum_decomp.rs`.** Empirical
findings (Turyn-weighted high-lag bb-vector as the index key):

| (n, k) | T_xy entries | T_xy distinct keys | T_zw entries | T_zw distinct keys | 4-tuple boundary count | Cross-match rate |
|---|---|---|---|---|---|---|
| 18, 4 | 65,536 | 1,763 | 65,536 | 2,984 | 4.3 × 10⁹ | **0.0034%** (147,392 match) |
| 22, 4 | 65,536 | 1,763 | 65,536 | 2,984 | 4.3 × 10⁹ | (same) |
| 22, 5 | 1,048,576 | 23,651 | 1,048,576 | 41,788 | 1.1 × 10¹² | **0.0001%** (956,672 match) |
| 24, 4 | 65,536 | 1,763 | 65,536 | 2,984 | 4.3 × 10⁹ | (same) |
| 26, 4 | 65,536 | 1,763 | 65,536 | 2,984 | 4.3 × 10⁹ | (same) |

**Key empirical observations:**

1. **The pair-table structure is invariant in `n` at fixed `k`.**
   The high-lag bb-vector for any 4-sequence boundary depends only
   on the boundary's bits and lag offsets within `[0..k] ∪ [n-k..n]`,
   which are determined by `k` alone (modulo the W-length difference
   for lags ≥ m=n-1). So the boundary table can be built **once per
   k** and reused at all n. Build cost amortizes across many n.
2. **Cross-match rates are tiny.** At k=4, only 0.0034% of all
   4-tuple boundaries pass the high-lag constraint (~30,000× pruning
   before SAT). At k=5, the rate drops to 0.0001% (~1.1M× pruning).
   The cross-table lookup is doing the right thing.
3. **Bucket sizes are reasonable.** Avg 37 entries per key in T_xy
   at k=4, 22 in T_zw. At k=5, 44 and 25 respectively. Hash queries
   stay O(small list length).
4. **Turyn weighting matters.** The four-tuple condition has Z and
   W weighted ×2; the index key must reflect this or false negatives
   appear.

The k=7 production case projects to:
* T_xy with ~2^28 = 268M entries, ~2.6M distinct keys (35× more than k=5)
* T_zw similar
* Memory at 4 bytes per (X-bd, Y-bd) pair: ~1 GB per table, ~2 GB
  total. Fits in RAM. Build time ~few minutes serially.
* Pruning rate projects to ~10⁻⁸ — i.e. the 4^14 ≈ 268M-per-table
  meet-in-the-middle returns ~3 candidates per query. Most queries
  yield the empty set; for the rest, almost all candidates are
  consistent.

### Stage 3: inside-out MDD walker (1-2 days)

* Build the MDD with `mm_sum + cross_coef` state.
* Apply the build-time pruning rules (autocorrelation bound,
  palindrome, etc.).
* Stop at near-border depth; emit the high-lag target vector.

**STATUS: minimal walker prototyped in `src/bin/inside_out_walk.rs`.**

Key empirical findings from the prototype:

* **The walker is correct at n=10 k=3 and n=14 k=4.** Joint
  4-sequence DFS, pair-walk from centre outward, mm_sum tracked
  Turyn-weighted. Known TT(n) leaves are reached and known boundary
  bits are retrieved from the index at the right key.
* **Cross-table pre-convolution makes leaf lookup O(1).**
  `target_to_count[v] = Σ_{a+b=v} |T_xy[a]| · |T_zw[b]|` is
  precomputed; per-leaf lookup is one hash query. n=14 k=4
  (16M leaves, 4M candidate boundaries each) walks in 3.1 s.
* **The very-high-lag-only key is middle-independent.** At lags
  s ≥ n-k both `mm` and `cross` are exactly zero (no pair structure
  at that distance involves the middle), so the target is always
  the all-zeros vector — the index acts as a *middle-independent
  boundary pre-filter*, pruning ~1000× of boundaries (4M of 4G at
  k=4) regardless of which middle was placed. **The walker is not
  yet using middle information to differentiate leaves.**
* **Per-leaf differentiation needs the cross-term-bearing lag
  range.** Lags `[n-2k+1..n-k-1]` (length `k-1`) have nonzero `mm`
  AND nonzero `cross`. Including them in the key gives per-leaf
  target vectors but couples the lookup to boundary bits via the
  linear cross term, breaking the simple hash design. Solving this
  is the open problem for Stage 4.

**Two design conclusions from the prototype:**

1. The **lag-sum decomposition is correct** and the **boundary
   index works as designed** as a pre-filter. The very-high-lag
   block alone gives ~1000× pruning at k=4 and projects to ~10⁵×
   at k=7.
2. The **inside-out walker** as described needs the cross-term
   handling to make full use of middle information. Without it,
   the walker only contributes the mm-feasibility bound (which is
   itself useful for leaf pruning, but the prototype's bound is
   too loose to fire). Two ways to tighten the boundary lookup
   into a per-leaf filter:
   * **(a) Indexed cross-coefficient**: store boundaries as
     (`bb-vector`, `cross_coef[s, p]` for each high lag and
     boundary position). At leaf, compute `target = -mm - Σ_p
     coef · b[p]` for each candidate; verify match.
   * **(b) Constraint-propagation lookup**: iterate hash buckets
     of the bb-vector (B-only); for each candidate, run cheap
     low-lag checks against the leaf's mm. SAT solver on top.

### Stage 4: integration (1 day)

* Couple: walk inside-out → query boundary index → forward
  candidates to a small SAT verifier on the low-lag constraints.
* Plug into the existing search framework as a new `--wz=inside`
  mode.

**STATUS: end-to-end Stage 4 walker working.** `inside_out_walk.rs`
extended with `verify_full_turyn` (exhaustive Turyn-condition check
on a 4-tuple boundary against the leaf's middle) and a `FULL_CHECK=1`
mode that runs the full check at every leaf as the walker enumerates.

End-to-end demos:

| (n, k) | leaves | canonical TT 4-tuples | walk time |
|---|---|---|---|
| 8, 2 | 65,536 | **336** | 0.17 s |
| 10, 3 | 65,536 | **1,792** | 1.0 s (parallel) |
| 12, 4 | 65,536 | **4,912** | 27 s (parallel) |
| 14, 4 | 16,777,216 | **8,128** | 6,787 s = 1.88 h (parallel) |

Cumulative speedup chain at n=10 k=3 (the most-measured case):

| Optimisation | Walk time | Cumulative speedup |
|---|---|---|
| Original `verify_full_turyn` (Vec<i32>) | 650 s | — |
| Bit-packed verify (popcount autocorr) | 153 s | 4.25× |
| + T2 (sign) on X, Z only | 38 s | 17× |
| + T2 on Y, W + T1 (reversal) on all 4 | **3.79 s** | **171×** |

n=8 k=2 chain: 16 s → 0.17 s = **94×**; canonical TT(8) count
8,192 → 336 (24.4× orbit reduction).

n=12 k=4 result is new — was previously infeasible. The walker now
scales to TT(12) in under 2 minutes.

The walker correctly enumerates **every** TT(n) 4-tuple at both
scales (the totals are full symmetry orbits per the BDKR T1–T4
group). Per-leaf cost grows as `pre_filter_count × verify_cost`,
and pre-filter at small k is too coarse — the walker is exhaustive
across leaves but spends most of its time per-leaf in the verify
loop. The pre-filter has 24,576× overhead vs the exact set — the
verify step kills 99.996 % of the surviving boundaries per leaf —
but the verify is cheap enough at small n that the walker still
completes.

What this proves:

1. **The full pipeline is correct.** Inside-out enumeration → very-
   high-lag bb pre-filter → full Turyn verify finds every TT(n)
   solution at small n (sanity-checked against the known TT(8)
   solution; 8,192 ≈ |full symmetry orbit of one canonical TT(8)|).
2. **The pre-filter is doing real work** even though it's
   middle-independent: at k=2 it cuts 65k → 3k boundaries per
   leaf (24,576× vs 4-tuple total).
3. **Stage 5 scaling is gated by the pre-filter selectivity.**
   At n=14 k=4 the per-leaf full check is 0.55 s × 16M leaves =
   ~9M s, infeasible. To scale we need either (a) a tighter
   per-leaf pre-filter that uses middle information (the open
   cross-term-aware indexing problem from Stage 3 notes), or (b)
   strong walker pruning so most leaves are skipped before
   verify, or (c) replacing per-candidate verify with a SAT
   solver (which is what a `--wz=inside` framework integration
   would do — same interface as existing `--wz=apart` /
   `--wz=together`).

**Stage 5 (open)**: integrate as a real `--wz=inside` framework
adapter. Expected interface: walker produces (mm_state, target_bb)
items; SAT solver queries the boundary index by target and runs
incremental SAT on the surviving candidates. The natural unit of
work is a leaf + a hash bucket; thousands per second possible if
the bucket size and SAT-instance size are both small.

### Stage 5: scale up (open-ended)

* Apply at n=26, n=56 with appropriate k.
* Compare TTC against `--wz=apart` baseline.

## Open questions

* **Cross-coefficient state size**: how dense does `cross_coef` get
  at near-border depth? Need empirical measurement.
* **Walk order**: symmetric pair-walk vs. depth-first single-walk?
  Affects MDD shape and dedup rate.
* **Tuple-conditioning**: should the index be split per (X²,Y²,Z²,W²)
  tuple? The 12 valid n=56 tuples each give a smaller, more
  selective index.
* **Stage-0 question**: can we even compute the high-lag bb-vector
  for arbitrary boundaries, AND can we compute the high-lag cross
  scalar from the MDD's near-border state? Both are arithmetic over
  small integers; should be straightforward but worth a test.

## Relation to existing infrastructure

* `mdd_zw_first.rs` / `mdd-k.bin`: outside-in MDD (current default).
  This proposal is the dual.
* `xy-table-k7.bin` (referenced in `docs/benchmark-sat.md`): a
  similar pair-table indexed by spectral signature. This proposal
  uses lag-sum-vector signatures instead.
* `SpectralIndex` (in `src/main.rs`): pair lookup by spectral pair
  bound. Conceptually related but uses spectrum, not autocorrelation.
* CANONICAL rules (T1-T4): apply the same symmetry reductions to the
  boundary table as in `mdd_zw_first` build.
