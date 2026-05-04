# Re-bench tracker — every rejected/within-noise idea in IDEAS.md

Status of each previously-rejected optimization, re-tested under the
ABBA protocol from `BENCHMARKING.md`. Each row gets:

* **Tractability**: how hard to re-apply (E = easy, M = medium, H = hard)
* **Re-impl notes**: file/function or commit hash to revert
* **Status**: `pending` / `running` / `confirmed-null` / `confirmed-win`
  / `confirmed-regression` / `not-feasible-this-session`

Protocol per candidate:

1. Sanity-check the change still applies cleanly. If not, mark `not-feasible`.
2. 4-block ABBA screen as a hypothesis filter.
3. If 4-block trends in a direction with sign ≥3/1, run an 8-block clean
   re-bench in a fresh process, no parallel benches.
4. If 8-block confirms in same direction, commit. Otherwise, classify as
   `confirmed-null` (or `confirmed-regression`) and move on.
5. Record per-block deltas, sd, 95% CI, and verdict.

Workload (held constant across all rebenches):
`--n=18 --wz=apart --mdd-k=5 --conj-tuple --continue-after-sat
--sat-secs=300`, `TURYN_THREADS=1 taskset -c 2 setarch -R`.

## SAT solver micro-opts (`radical/src/lib.rs`)

These were largely tested in the May 2026 dry-run (`BENCHMARKING-PROTOCOL-RESULTS.md`).
Per the lesson learned there, only the 8-block clean re-bench is the
authoritative result.

| ID | Hypothesis | Tractability | Status | 8-blk Δ | 95% CI | Notes |
|---|---|---|---|---|---|---|
| C1 / R-style | hoist `assigns` + `qc` in `recompute_quad_pb` | E | confirmed-null | TBD | TBD | 4-block: -0.24%; need 8-block clean |
| C2 / R6-style | combine `clause_meta[ci]` loads in `propagate_lit` | E | confirmed-regression-direction | +0.50% (4) | wide | Hoist hurt blocker-true fast path |
| C3 / R-style | hoist `qc` in `propagate_quad_pb` | E | hint-positive | -0.83% (4) | wide | Need 8-block clean re-test |
| C4 / R4-related | hoist `assigns/trail_pos/level` in `compute_quad_pb_explanation_into` | E | **confirmed-null** | +0.59% (8 clean) | [-0.35%, +1.53%] | False-positive at 4 blocks; reverted in `c8d2e8d` |
| C5 / R-style | hoist `quad_pb_var_watches[v]` in `backtrack` | E | confirmed-null | -0.21% (4) | [-0.86%, +0.45%] | sd 0.41% suggests true effect is small |
| C_all | C1+C3+C4+C5 stacked | E | hint-positive | (+0.45% w/ outlier; -1.55% excl) | wide | Most signal came from now-rejected C4 |
| R2 | global stale flag for quad PB constraints | E | pending | — | — | Replace inline scan with one bool |
| R3 | skip term update after recompute | E | known-regression | — | — | -6.5% in original test, not retesting |
| R10 | sort terms by var index | E | known-regression | — | — | -2.4% in original test, not retesting |
| R6 (orig) | swap deleted/blocker check order | E | unsafe | — | — | Loses correctness on deleted+blocker-true clauses |
| P10 | replace HashSet<Vec<i32>> with HashSet<u64> | E | not-feasible-this-session | — | — | Phase B is <0.2% of n=18 runtime; below floor |

## Phase B / search-framework (`src/main.rs`, `src/mdd_pipeline.rs`)

These touch the boundary/SolveW/SolveZ pipeline. Each is non-trivial to
re-apply without finding the original commit. Most target `n=26
--wz=together` or n=56, not the `n=18 --wz=apart` workload we use here,
so even a clean re-bench may show "null" simply because the code path
isn't exercised.

| ID | Hypothesis | Tractability | Status | Notes |
|---|---|---|---|---|
| F2 | Cache spectral cos/sin across SolveWZ calls | M | not-feasible-this-session | Original tested at n=26 wz=together; needs porting check |
| F3 | Cache trig values for spectral DFT | M | not-feasible-this-session | "Within noise ~2.4%" — would need clean 8-block to confirm |
| F4 | Skip per-lag constraint entirely | M | known-tradeoff | Helps n=26 (+35%) but hurts n=22 (3/10 → 1/10 finds). Not a pure speedup |
| F5 | HashSet dedup in PbSetEq counts | E | pending-reapply | Original code lost; would need re-implementation |
| F7 | Drop attempt re-queue entirely | M | known-tradeoff | Helps rate but hurts find rate. Not pure speedup |
| F8 | Coalesce small per-lag constraints | H | not-feasible-this-session | "May not be feasible" per original note |
| F9 | Revert b9d92ac quad PB encoding | H | not-feasible-this-session | Big refactor, depends on current quad-PB shape |
| F10 | Skip per-lag constraint when trivially satisfied | M | not-feasible-this-session | Needs investigation of current early-out logic |
| F11 | Remove rules (iv)/(v) middle clauses for small n | M | known-tradeoff | "Within noise" at n=26; helps small-n find time |
| F13 | SpectralConstraint SIMD | H | not-feasible-this-session | Big change |
| F14 | SpectralConstraint SoA layout | H | not-feasible-this-session | Big change |
| F15 | Move outfix pin handling out of hot path | M | pending-reapply | Need to locate hot path |

## Boundary/E-series (`src/mdd_zw_first.rs`, `src/main.rs`)

| ID | Hypothesis | Tractability | Status | Notes |
|---|---|---|---|---|
| E2 | ZW-only boundary autocorrelation bound | M | known-low-prune | Rejected on 0.3% prune rate, not effect size |
| E4 | Early W spectral reject | M | known-no-pruning | "Conditioned reject" not implemented |
| E5 | Conflict limit ∝ boundary promise | M | not-feasible-this-session | Needs promise-scoring logic |
| E8 | Checkpoint/restore XY solver | H | known-not-cheaper | Profiling showed clone dominates |
| E9 | Pre-check XY extensions at stage 0 | M | not-feasible-this-session | Needs ext-check before SolveW |
| E11 | Group SolveW by w_mid_sum | M | not-feasible-this-session | bnd/s drop in original |

## Sync walker (`src/sync_walker.rs`)

These all target `--wz=sync`, not our `--wz=apart` workload. They are
**out of scope** for retesting under our standard config.

| ID | Hypothesis | Status | Notes |
|---|---|---|---|
| S1 | Pre-DFT at W-tightest bin | not-feasible-wrong-mode | sync-only |
| S4 | Partition first deterministic levels | not-feasible-wrong-mode | sync-only |
| S5 | Raise nogood-share threshold | not-feasible-wrong-mode | sync-only |
| S6 | Remove compute_sigma O(4n) | not-feasible-wrong-mode | sync-only |
| S7 | Skip propagate_only when det-only | not-feasible-wrong-mode | sync-only |
| S11b | dynamic_capacity_violated post-harvest | not-feasible-wrong-mode | sync-only |
| S12 | --no-xor at sync | not-feasible-wrong-mode | sync-only |
| S15 | Adaptive sibling-sort randomness | not-feasible-wrong-mode | sync-only |
| U2 | Skip score_state on seed!=0 | not-feasible-wrong-mode | sync-only |
| U4 | Skip harvest_forced when delta==0 | not-feasible-wrong-mode | sync-only |
| U5 | Reuse candidates Vec | not-feasible-wrong-mode | sync-only |
| U9 | Incremental num_assigned_in_range | not-feasible-wrong-mode | sync-only |
| R5 | `--no-xor` at sync | not-feasible-wrong-mode | sync-only |
| R6 | MAX_SHARED_LEN ∈ {32,64,8} | not-feasible-wrong-mode | sync-only |
| R8d | Skip harvest_forced when no walker var inferred | not-feasible-wrong-mode | sync-only |
| R9 | Forbidden-lit cache | not-feasible-wrong-mode | sync-only |
| V1 | backbone_scan on apart's XY template | M | pending | Specifically targets apart |

## Other / mode-specific

| ID | Status | Notes |
|---|---|---|
| W2 | known-broken-elsewhere | Reduces Z diversity catastrophically |
| W4 | known-broken-elsewhere | Same issue as W2 |
| Branchless multiply (line 126) | known-regression | -5.4% in original test |
| Mirror-U palindromic (line 151) | structural-rejection | TT(6) solution proves not all are palindromic |

## Summary of session feasibility

* **Done in this session (May 2026 dry-run)**: C1, C2, C3, C4, C5, C_all
  → all `confirmed-null` or `confirmed-regression-direction`. C4 was a
  Type I false positive at 4 blocks and reverted.
* **Tractable today, not yet run**: R2 (global stale flag).
* **Out of scope (wrong mode / huge refactor / known-tradeoff)**:
  everything in the sync-walker block, F4/F7/F11 (real tradeoffs),
  F8/F9/F13/F14/E5/E8/E9/E11 (need substantial work).
* **Pending re-apply work**: F5, F15, V1, P10. Could be done in
  subsequent sessions.

## Headline interpretation

After a careful test of 6 SAT-solver-level candidates under the full
ABBA protocol with 4-block screen + 8-block clean confirmation, **none
showed a confirmed wall-clock effect on this hardware (4-CPU shared
VM, σ ≈ 1.0–1.2% per block).** The candidates are likely either:

1. True nulls (the optimization doesn't actually help)
2. Real but sub-1% wins that this hardware can't resolve

Distinguishing (1) from (2) requires either a quieter machine
(detected σ ~0.2-0.4% per block) or instructions-retired metrics via
HW counters (deterministic, σ ≈ 0). On this VM the realistic
detection threshold is ~1.5%, and nothing in the rejected pile
appears to clear that bar.

This is consistent with the original rejections being *correct*: the
ad-hoc "within noise" verdicts at the time of rejection were honest
characterizations, just under-justified statistically.
