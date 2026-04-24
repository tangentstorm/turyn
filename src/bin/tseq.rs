//! Direct T-sequence finder.
//!
//! A T-sequence of length n is a set of four {+1, -1, 0} sequences X, Y, Z, W
//! of length n such that at each position i exactly one sequence is non-zero
//! (and equal to +1 or -1), and the combined aperiodic autocorrelations vanish:
//!   N_X(s) + N_Y(s) + N_Z(s) + N_W(s) = 0   for s = 1, ..., n-1.
//!
//! Encoding: at each position i, pick channel c[i] in {0,1,2,3} and sign s[i]
//! in {-1, +1}. Only same-channel pairs contribute to the combined
//! autocorrelation:
//!   N(s) = sum_{i: c[i] = c[i+s]} s[i] * s[i+s].
//!
//! This is strictly smaller branching (8-way) than the Turyn 16-way per
//! position, at the cost of working on a larger span (the full length n
//! at once, not just the 2k boundary).
//!
//! Approach:
//!   * Bouncing placement order 0, n-1, 1, n-2, 2, n-3, ...  so long (tight)
//!     lags are completed first.
//!   * 8-way branching (channel x sign) with aggressive pruning: each lag
//!     tracks partial N(s) and remaining_cap(s) (= unplaced pairs at lag s).
//!     Prune when |partial_N(s)| > remaining_cap(s).
//!   * Symmetry breaking: channel relabelling (introduce channels in
//!     ascending order) + sign gauge (first occurrence of each channel has
//!     sign +1). 4! * 2^4 = 384x reduction.
//!
//! Usage:
//!   target/release/tseq --n=167 --secs=600
//!   target/release/tseq --n=8              # quick correctness smoke
//!   target/release/tseq --n=50 --secs=30 --memo
//!                                          # enable failure-state memo experiment

use std::hash::{Hash, Hasher};
use std::time::{Duration, Instant};

use rustc_hash::{FxHashSet, FxHasher};

fn bouncing_order(n: usize) -> Vec<usize> {
    let mut order = Vec::with_capacity(n);
    for t in 0..n {
        if t % 2 == 0 {
            order.push(t / 2);
        } else {
            order.push(n - 1 - t / 2);
        }
    }
    order
}

struct Search {
    n: usize,
    order: Vec<usize>,
    channels: Vec<u8>,
    signs: Vec<i8>,
    n_lag: Vec<i32>,
    remaining_cap: Vec<i32>,
    channel_count: [u32; 4],
    max_ch: i8,
    nodes: u64,
    deadline: Instant,
    start: Instant,
    last_progress: Instant,
    max_depth_seen: usize,
    found: bool,
    stop: bool,
    solution: Option<(Vec<u8>, Vec<i8>)>,
    // Per-depth node counters (for progress diagnostics)
    depth_nodes: Vec<u64>,
    // Optional exact-key failure memo (--memo).
    memo_enabled: bool,
    memo_cap: usize,
    fail_memo: FxHashSet<u64>,
    memo_hits: u64,
    memo_inserts: u64,
    memo_evictions: u64,
}

impl Search {
    fn new(n: usize, deadline: Instant, memo_enabled: bool, memo_cap: usize) -> Self {
        let order = bouncing_order(n);
        // remaining_cap[s] = number of (i, i+s) pairs with both endpoints in [0, n).
        // For s in [1, n-1]: n - s pairs.  Index 0 unused.
        let remaining_cap: Vec<i32> = (0..n)
            .map(|s| if s == 0 { 0 } else { (n - s) as i32 })
            .collect();
        let now = Instant::now();
        Search {
            n,
            order,
            channels: vec![u8::MAX; n],
            signs: vec![0; n],
            n_lag: vec![0; n],
            remaining_cap,
            channel_count: [0; 4],
            max_ch: -1,
            nodes: 0,
            deadline,
            start: now,
            last_progress: now,
            max_depth_seen: 0,
            found: false,
            stop: false,
            solution: None,
            depth_nodes: vec![0; n + 1],
            memo_enabled,
            memo_cap,
            fail_memo: FxHashSet::default(),
            memo_hits: 0,
            memo_inserts: 0,
            memo_evictions: 0,
        }
    }

    /// Exact-key state fingerprint at depth `t`.  Captures full partial
    /// autocorrelation vector plus (channel, sign) of every placed position.
    /// In bouncing-order DFS this is a complete characterization of the node.
    #[inline]
    fn state_hash(&self, t: usize) -> u64 {
        let mut h = FxHasher::default();
        // N(s) for s in 1..n
        for &v in &self.n_lag[1..] {
            v.hash(&mut h);
        }
        // placed (channel, sign) in step order (bouncing)
        for step in 0..t {
            let p = self.order[step];
            self.channels[p].hash(&mut h);
            self.signs[p].hash(&mut h);
        }
        h.finish()
    }

    #[inline]
    fn check_clock(&mut self) {
        let now = Instant::now();
        if now > self.deadline {
            self.stop = true;
            return;
        }
        if now.duration_since(self.last_progress).as_secs() >= 5 {
            self.last_progress = now;
            let el = now.duration_since(self.start).as_secs_f64();
            let rate = self.nodes as f64 / el / 1e6;
            eprintln!(
                "  [{:7.1}s] nodes={:>14} max_depth={:>4}/{} ({:6.2} Mnodes/s)",
                el, self.nodes, self.max_depth_seen, self.n, rate
            );
        }
    }

    fn dfs(&mut self, t: usize) {
        self.nodes += 1;
        self.depth_nodes[t] += 1;
        if self.nodes & ((1u64 << 20) - 1) == 0 {
            self.check_clock();
        }
        if self.stop || self.found {
            return;
        }
        if t > self.max_depth_seen {
            self.max_depth_seen = t;
        }

        if t == self.n {
            // All lag constraints should be satisfied exactly if we reach here,
            // because pruning guarantees |N(s)| <= remaining_cap(s) = 0 at the end.
            debug_assert!(self.n_lag[1..].iter().all(|&v| v == 0));
            self.solution = Some((self.channels.clone(), self.signs.clone()));
            self.found = true;
            return;
        }

        // Failure-memo check.  Only useful if *different* DFS paths can reach
        // the same (N, assignments) state; in pure bouncing-order DFS this is
        // exactly the experiment we want to quantify.  Hit rate is logged at
        // the end.
        let hash_opt = if self.memo_enabled && t >= 1 && t + 1 < self.n {
            let h = self.state_hash(t);
            if self.fail_memo.contains(&h) {
                self.memo_hits += 1;
                return;
            }
            Some(h)
        } else {
            None
        };

        let nodes_before = self.nodes;

        let p = self.order[t];

        // Channel symmetry: can only introduce channel c if all channels 0..c
        // have appeared or c == max_ch+1.  Cheapest: allow c in 0..=min(max_ch+1, 3).
        let max_ch_allowed = ((self.max_ch + 1).min(3)) as u8;

        for c in 0..=max_ch_allowed {
            let is_new_channel = self.channel_count[c as usize] == 0;
            // Sign gauge: first occurrence of a channel has sign +1.
            let sign_range: &[i8] = if is_new_channel { &[1] } else { &[1, -1] };

            for &sign in sign_range {
                // Place position p.
                self.channels[p] = c;
                self.signs[p] = sign;

                // Incrementally update N(s) and remaining_cap(s) for all
                // pairs (q, p) where q is already placed.  Stop early on
                // pruning failure.
                let mut pruned = false;
                let mut applied = 0usize;
                for prev_t in 0..t {
                    let q = self.order[prev_t];
                    let lag = ((p as i32) - (q as i32)).unsigned_abs() as usize;
                    self.remaining_cap[lag] -= 1;
                    if self.channels[q] == c {
                        self.n_lag[lag] += (self.signs[q] as i32) * (sign as i32);
                    }
                    applied = prev_t + 1;
                    if self.n_lag[lag].abs() > self.remaining_cap[lag] {
                        pruned = true;
                        break;
                    }
                }

                if !pruned {
                    let prev_max_ch = self.max_ch;
                    self.channel_count[c as usize] += 1;
                    if (c as i8) > self.max_ch {
                        self.max_ch = c as i8;
                    }

                    self.dfs(t + 1);

                    self.channel_count[c as usize] -= 1;
                    self.max_ch = prev_max_ch;
                }

                // Undo the updates we applied (whether pruned early or not).
                for prev_t in 0..applied {
                    let q = self.order[prev_t];
                    let lag = ((p as i32) - (q as i32)).unsigned_abs() as usize;
                    self.remaining_cap[lag] += 1;
                    if self.channels[q] == c {
                        self.n_lag[lag] -= (self.signs[q] as i32) * (sign as i32);
                    }
                }

                if self.found || self.stop {
                    return;
                }
            }
        }

        // All children explored without finding a solution.  Record this
        // state as a failure for future branches.
        if let Some(h) = hash_opt {
            if self.nodes > nodes_before && self.fail_memo.len() < self.memo_cap {
                self.fail_memo.insert(h);
                self.memo_inserts += 1;
            } else if self.fail_memo.len() >= self.memo_cap {
                self.memo_evictions += 1;
            }
        }
    }
}

fn parse_flag<T: std::str::FromStr>(args: &[String], prefix: &str) -> Option<T> {
    args.iter()
        .find_map(|s| s.strip_prefix(prefix).and_then(|x| x.parse().ok()))
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = parse_flag(&args, "--n=").unwrap_or(167);
    let secs: u64 = parse_flag(&args, "--secs=").unwrap_or(600);
    let memo_enabled = args.iter().any(|s| s == "--memo");
    let memo_cap: usize = parse_flag(&args, "--memo-cap=").unwrap_or(16_000_000);

    if n < 2 {
        eprintln!("Need n >= 2.");
        return;
    }

    eprintln!(
        "T-sequence search: n={}, budget={}s (8-way, bouncing{}){}",
        n,
        secs,
        if memo_enabled {
            format!(", memo on (cap={})", memo_cap)
        } else {
            "".to_string()
        },
        ""
    );
    let deadline = Instant::now() + Duration::from_secs(secs);
    let mut search = Search::new(n, deadline, memo_enabled, memo_cap);
    search.dfs(0);

    let el = search.start.elapsed().as_secs_f64();
    eprintln!(
        "Explored {} nodes in {:.1}s ({:.2} Mnodes/s), max_depth {} / {}",
        search.nodes,
        el,
        search.nodes as f64 / el / 1e6,
        search.max_depth_seen,
        n
    );

    // Per-depth diagnostics (only print non-trivial depths).
    let total_nonzero = search.depth_nodes.iter().filter(|&&c| c > 0).count();
    if total_nonzero > 0 && std::env::var("TSEQ_PROFILE").is_ok() {
        eprintln!("Nodes per depth (non-zero only):");
        for (d, &c) in search.depth_nodes.iter().enumerate() {
            if c > 0 {
                eprintln!("  depth {:>3}: {}", d, c);
            }
        }
    }

    if search.memo_enabled {
        let total_internal = search
            .depth_nodes
            .iter()
            .enumerate()
            .filter(|(d, _)| *d >= 1 && *d + 1 < n)
            .map(|(_, c)| *c)
            .sum::<u64>();
        let hit_pct = if total_internal > 0 {
            100.0 * search.memo_hits as f64 / total_internal as f64
        } else {
            0.0
        };
        eprintln!(
            "Memo: size={} (cap={}), inserts={}, hits={} ({:.4}% of internal nodes), evictions={}",
            search.fail_memo.len(),
            search.memo_cap,
            search.memo_inserts,
            search.memo_hits,
            hit_pct,
            search.memo_evictions
        );
    }

    if let Some((channels, signs)) = search.solution {
        eprintln!("\nFound T({}):", n);
        print_solution(n, &channels, &signs);
    } else if search.stop {
        eprintln!("\nStopped at time budget. No T({}) found yet.", n);
    } else {
        eprintln!(
            "\nSearch exhausted. No T({}) exists under the chosen symmetry gauge.",
            n
        );
    }
}

fn print_solution(n: usize, channels: &[u8], signs: &[i8]) {
    let names = ["X", "Y", "Z", "W"];
    for ch in 0..4u8 {
        let mut s = String::new();
        for i in 0..n {
            if channels[i] == ch {
                s.push(if signs[i] > 0 { '+' } else { '-' });
            } else {
                s.push('0');
            }
        }
        println!("{}: {}", names[ch as usize], s);
    }

    // Verify all autocorrelations vanish.
    let mut ok = true;
    for lag in 1..n {
        let mut sum = 0i32;
        for i in 0..n - lag {
            if channels[i] == channels[i + lag] {
                sum += (signs[i] as i32) * (signs[i + lag] as i32);
            }
        }
        if sum != 0 {
            ok = false;
            eprintln!("  VERIFY FAIL: N({}) = {}", lag, sum);
        }
    }
    if ok {
        eprintln!("  Verified: N(s) = 0 for s = 1..{}", n);
    }

    // Sanity: exactly one channel active per position, value in {-1, +1}.
    let mut counts = [0usize; 4];
    for i in 0..n {
        assert!(channels[i] < 4);
        assert!(signs[i] == 1 || signs[i] == -1);
        counts[channels[i] as usize] += 1;
    }
    eprintln!(
        "  Channel counts: X={} Y={} Z={} W={} (total {})",
        counts[0], counts[1], counts[2], counts[3], n
    );
}
