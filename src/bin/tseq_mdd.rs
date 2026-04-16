//! 8-way MDD build experiment for T-sequences.
//!
//! Builds an MDD over all 2k positions of a (self-contained) T-sequence of
//! length 2k -- the same problem as `tseq --n=2k` but compiled as a DAG with
//! subtree sharing.  Reports:
//!   * Total MDD node count (distinct states)
//!   * Naive tree node count (every path individually)
//!   * Compression ratio
//!   * Per-level breakdown
//!
//! Purpose: determine whether T-sequence search admits structural subtree
//! sharing the way Turyn MDD does.  If the MDD stays exponentially smaller
//! than the naive tree, the MDD-boundary + middle-SAT approach is viable
//! for n=167.  If the MDD is essentially the full tree (no dedup), then
//! direct T-sequence search has no MDD advantage over DFS.
//!
//! Usage:
//!   target/release/tseq_mdd --k=4                     # full pair set
//!   target/release/tseq_mdd --k=5 --profile
//!   target/release/tseq_mdd --k=5 --cross-only        # only cross-half pairs
//!                                                       (mimics Turyn boundary)

use std::time::Instant;

use rustc_hash::FxHashMap;

/// Bouncing order for 2k positions: 0, 2k-1, 1, 2k-2, 2, 2k-3, ...
fn bouncing_order(m: usize) -> Vec<usize> {
    let mut o = Vec::with_capacity(m);
    for t in 0..m {
        if t % 2 == 0 {
            o.push(t / 2);
        } else {
            o.push(m - 1 - t / 2);
        }
    }
    o
}

/// State at a given DFS/MDD level.
///
/// Crucially, `active_assign` retains only the encoded (c, s) of positions
/// that still have a *pending pair event* in the tracked set -- positions
/// whose last_use < current level have been dropped.  This is the key
/// mechanism that lets the Turyn MDD dedup different histories that end
/// up at the same (sums, still-relevant-values) point.
///
///   sums[s]           = partial N(s) so far, s in 1..m
///   active_assign     = sorted list of (position, encoded_val) for
///                       positions still active at this level
///   channel_counts[c] = number of placed positions with channel c (gauge)
///   max_ch            = max channel introduced so far (gauge)
#[derive(Clone, Eq, PartialEq, Hash)]
struct State {
    sums: Vec<i32>,
    active_assign: Vec<(u8, u8)>, // (position, encoded_val); sorted by position
    channel_counts: [u32; 4],
    max_ch: i8,
}

struct Builder {
    m: usize,
    order: Vec<usize>,
    /// pair_tracked[a][b] == true iff pair (a, b) contributes to a tracked
    /// sum.  For --cross-only mode, only pairs with one endpoint in the
    /// "left half" [0, k) and one in the "right half" [k, 2k) are tracked.
    pair_tracked: Vec<Vec<bool>>,
    /// last_use[p] = max level at which any tracked pair event involving p
    /// completes.  Position p is dropped from the active state at levels > last_use[p].
    last_use: Vec<usize>,
    remaining_cap: Vec<i32>, // per lag; index 0 unused
    /// cache : (level, state) -> node_id.  Node id 0 is DEAD (pruned subtree),
    /// node id 1 is LEAF (feasible completion).  Real nodes start at 2.
    cache: FxHashMap<(usize, State), u32>,
    /// node_count[level] = number of distinct non-dead nodes built at that level.
    node_count: Vec<u64>,
    /// tree_count[level] = number of DFS calls at that level (naive tree).
    tree_count: Vec<u64>,
    /// cache_hits[level] = number of times build() returned via cache hit.
    cache_hits: Vec<u64>,
    /// dead_returns[level] = number of times build() returned DEAD (all children pruned).
    dead_returns: Vec<u64>,
    /// leaf_count = number of feasible complete assignments.
    leaf_count: u64,
    next_id: u32,
}

impl Builder {
    fn new(m: usize, cross_only: bool) -> Self {
        let k = m / 2;
        let order = bouncing_order(m);
        let mut pos_to_level = vec![0usize; m];
        for (lev, &p) in order.iter().enumerate() {
            pos_to_level[p] = lev;
        }
        // Which pairs count as "events" that update sums?  Full mode tracks
        // every pair in [0, m); cross-only tracks only left-right pairs.
        let mut pair_tracked = vec![vec![false; m]; m];
        for a in 0..m {
            for b in (a + 1)..m {
                // In cross-only mode we require distance >= k, which matches
                // the Turyn boundary MDD: the 2k positions model the true
                // boundary [0, k-1] ∪ [n-k, n-1] of a length-n sequence and
                // the only tracked pairs are those at cross-boundary lags
                // n-k..n-1, i.e., MDD-distance >= k.
                let is_cross_far = a < k && b >= k && (b - a) >= k;
                if cross_only {
                    if is_cross_far {
                        pair_tracked[a][b] = true;
                        pair_tracked[b][a] = true;
                    }
                } else {
                    pair_tracked[a][b] = true;
                    pair_tracked[b][a] = true;
                }
            }
        }
        // remaining_cap[s] = number of tracked pairs at lag s
        let mut remaining_cap = vec![0i32; m];
        for a in 0..m {
            for b in (a + 1)..m {
                if pair_tracked[a][b] {
                    remaining_cap[b - a] += 1;
                }
            }
        }
        // last_use[p] = max level where any tracked pair event involving p completes
        let mut last_use = vec![0usize; m];
        for a in 0..m {
            for b in (a + 1)..m {
                if pair_tracked[a][b] {
                    let completion = pos_to_level[a].max(pos_to_level[b]);
                    last_use[a] = last_use[a].max(completion);
                    last_use[b] = last_use[b].max(completion);
                }
            }
        }
        Builder {
            m,
            order,
            pair_tracked,
            last_use,
            remaining_cap,
            cache: FxHashMap::default(),
            node_count: vec![0; m + 1],
            tree_count: vec![0; m + 1],
            cache_hits: vec![0; m + 1],
            dead_returns: vec![0; m + 1],
            leaf_count: 0,
            next_id: 2,
        }
    }

    /// Build MDD node at given level with given state.  Returns node id
    /// (0=DEAD, 1=LEAF, else allocated).  The naive tree count increments
    /// on every call; the MDD node count only when the cache missed.
    fn build(&mut self, level: usize, state: State) -> u32 {
        self.tree_count[level] += 1;

        if let Some(&id) = self.cache.get(&(level, state.clone())) {
            self.cache_hits[level] += 1;
            return id;
        }

        if level == self.m {
            // All positions placed.  Final feasibility: the *tracked* lags
            // must be zero.  (In --cross-only mode, untracked within-half
            // lags are expected to be resolved elsewhere.)
            let feasible = state.sums[1..].iter().all(|&v| v == 0);
            if feasible {
                self.leaf_count += 1;
                self.cache.insert((level, state), 1);
                return 1;
            } else {
                self.cache.insert((level, state), 0);
                return 0;
            }
        }

        let p = self.order[level];
        let max_ch_allowed = ((state.max_ch + 1).min(3)) as u8;

        let mut children: Vec<u32> = Vec::with_capacity(8);
        let mut saw_live = false;

        for c in 0..4u8 {
            for &sign in &[1i8, -1i8] {
                if c > max_ch_allowed {
                    children.push(0); // DEAD
                    continue;
                }
                let is_new_channel = state.channel_counts[c as usize] == 0;
                if is_new_channel && sign != 1 {
                    children.push(0); // gauge blocks
                    continue;
                }

                // Simulate placing (p, c, sign).  Update sums + check pruning.
                // Look up each prior placed position's value from
                // active_assign; positions that dropped off carry their
                // values elsewhere and no longer contribute tracked events.
                let mut new_sums = state.sums.clone();
                let mut pruned = false;
                for &(qpos, qval) in &state.active_assign {
                    let q = qpos as usize;
                    if !self.pair_tracked[p][q] {
                        continue;
                    }
                    let lag = ((p as i32) - (q as i32)).unsigned_abs() as usize;
                    let qc = qval >> 1;
                    if qc == c {
                        let sq = if qval & 1 == 0 { 1i32 } else { -1 };
                        new_sums[lag] += sq * (sign as i32);
                    }
                }
                if !pruned {
                    let mut placed_set = vec![false; self.m];
                    for step in 0..level {
                        placed_set[self.order[step]] = true;
                    }
                    placed_set[p] = true;
                    let mut remaining_cap = self.remaining_cap.clone();
                    for s in 1..self.m {
                        let mut committed = 0i32;
                        for a in 0..self.m - s {
                            if placed_set[a] && placed_set[a + s] && self.pair_tracked[a][a + s] {
                                committed += 1;
                            }
                        }
                        remaining_cap[s] -= committed;
                        if new_sums[s].abs() > remaining_cap[s] {
                            pruned = true;
                            break;
                        }
                    }
                }

                if pruned {
                    children.push(0);
                    continue;
                }

                // Build next-level active set: previous active positions
                // whose last_use is still >= level+1, plus the just-placed
                // position p (iff its own last_use >= level+1; otherwise it
                // drops immediately).
                let mut next_active: Vec<(u8, u8)> = state
                    .active_assign
                    .iter()
                    .filter(|&&(qpos, _)| self.last_use[qpos as usize] >= level + 1)
                    .copied()
                    .collect();
                if self.last_use[p] >= level + 1 {
                    let enc = (c << 1) | (if sign == 1 { 0 } else { 1 });
                    next_active.push((p as u8, enc));
                }
                next_active.sort_by_key(|&(qpos, _)| qpos);

                let mut new_state = State {
                    sums: new_sums,
                    active_assign: next_active,
                    channel_counts: state.channel_counts,
                    max_ch: state.max_ch,
                };
                new_state.channel_counts[c as usize] += 1;
                if (c as i8) > new_state.max_ch {
                    new_state.max_ch = c as i8;
                }

                let child = self.build(level + 1, new_state);
                children.push(child);
                if child != 0 {
                    saw_live = true;
                }
            }
        }

        let id = if !saw_live {
            self.dead_returns[level] += 1;
            0 // all children dead
        } else {
            self.node_count[level] += 1;
            let n = self.next_id;
            self.next_id += 1;
            n
        };
        self.cache.insert((level, state), id);
        id
    }
}

fn parse_flag<T: std::str::FromStr>(args: &[String], prefix: &str) -> Option<T> {
    args.iter()
        .find_map(|s| s.strip_prefix(prefix).and_then(|x| x.parse().ok()))
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let k: usize = parse_flag(&args, "--k=").unwrap_or(4);
    let m = 2 * k;
    let profile = args.iter().any(|s| s == "--profile");
    let cross_only = args.iter().any(|s| s == "--cross-only");

    eprintln!(
        "Building 8-way T-sequence MDD for m={} (k={}), mode={}, naive tree size bound 8^{}={}",
        m,
        k,
        if cross_only { "cross-only" } else { "all-pairs" },
        m,
        8u128.pow(m as u32)
    );

    let start = Instant::now();
    let mut b = Builder::new(m, cross_only);
    let root_state = State {
        sums: vec![0; m],
        active_assign: Vec::new(),
        channel_counts: [0; 4],
        max_ch: -1,
    };
    let root = b.build(0, root_state);
    let elapsed = start.elapsed().as_secs_f64();

    let total_nodes: u64 = b.node_count.iter().sum();
    let total_tree: u64 = b.tree_count.iter().sum();

    eprintln!(
        "\nRoot = {}. Built in {:.2}s. MDD nodes: {}. Naive-tree calls: {}.",
        root, elapsed, total_nodes, total_tree
    );
    eprintln!("Leaves (feasible T({})): {}", m, b.leaf_count);
    if total_tree > 0 {
        eprintln!(
            "Compression: {:.1}x  ({} naive DFS nodes / {} MDD nodes)",
            total_tree as f64 / total_nodes.max(1) as f64,
            total_tree,
            total_nodes
        );
    }

    let total_hits: u64 = b.cache_hits.iter().sum();
    let total_dead: u64 = b.dead_returns.iter().sum();
    eprintln!(
        "Cache hits (genuine subtree sharing): {}   DEAD returns (pruned): {}",
        total_hits, total_dead
    );

    if profile {
        eprintln!("\nPer-level breakdown:");
        eprintln!(
            "  {:>5} {:>12} {:>10} {:>10} {:>10} {:>8}",
            "level", "tree-calls", "live-nodes", "dead", "hits", "share"
        );
        for l in 0..=m {
            let t = b.tree_count[l];
            let n = b.node_count[l];
            let h = b.cache_hits[l];
            let d = b.dead_returns[l];
            if t > 0 {
                let pct = if t > 0 { 100.0 * h as f64 / t as f64 } else { 0.0 };
                eprintln!(
                    "  {:>5} {:>12} {:>10} {:>10} {:>10} {:>7.2}%",
                    l, t, n, d, h, pct
                );
            }
        }
    }
}
