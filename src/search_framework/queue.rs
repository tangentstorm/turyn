use std::cmp::Ordering;
use std::collections::BinaryHeap;

use crate::search_framework::stage::WorkItem;

pub trait SchedulerPolicy<T>: Send {
    fn push(&mut self, item: WorkItem<T>);
    fn pop(&mut self) -> Option<WorkItem<T>>;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// Two-lane priority scheduler.
///
/// **Within each lane**, items pop highest-`priority` first so the deepest
/// pipeline stage with available work always runs ahead of earlier stages.
/// This gives the pipeline its just-in-time character: every worker is
/// interchangeable, and as soon as a SolveZ item exists it pops ahead of a
/// fresh boundary even if the boundary arrived first. Equal-priority items
/// pop in insertion order (FIFO) via a monotone `seq` tie-break.
///
/// **Gold lane** is reserved for items explicitly promoted via
/// `WorkItem.gold = true`. Gold is *experimentation infrastructure*: a hook
/// to flip specific items into a "skip the line" lane so an experimenter
/// can test a "this cube looks promising" hypothesis without restructuring
/// the scheduler. Nothing currently sets `gold = true`, so the gold lane is
/// expected to stay empty in default runs and the pop hot path
/// short-circuits to the work lane without ever sampling the RNG.
///
/// **Coin flip**: when both lanes are nonempty, a `gold_ratio_per_mille`
/// (default 500 = 50/50) chance picks the gold lane.  When one lane is
/// empty, the other drains.
pub struct LaneByPriority<T> {
    /// Probability ×1000 of selecting gold when both lanes have items.
    /// Clamped to `[0, 1000]`.
    gold_ratio_per_mille: u64,
    /// xorshift64 state.  Same family as `src/stochastic.rs:122`.  Fixed
    /// seed so scheduling is reproducible across reruns; pop order does
    /// not affect TTC totals so this costs nothing.
    rng_state: u64,
    /// Strictly-monotone insertion counter for FIFO tie-break inside a
    /// priority bucket.  `u64` wraps at 1.8e19 — never in practice.
    next_seq: u64,
    gold: BinaryHeap<PrioItem<T>>,
    work: BinaryHeap<PrioItem<T>>,
}

/// Heap entry that stores the sort keys (priority, seq) outside the
/// `WorkItem` so we can derive `Ord` cleanly without requiring the
/// caller's payload type to be `Ord`.
struct PrioItem<T> {
    priority: i32,
    seq: u64,
    item: WorkItem<T>,
}

impl<T> PartialEq for PrioItem<T> {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority && self.seq == other.seq
    }
}
impl<T> Eq for PrioItem<T> {}
impl<T> PartialOrd for PrioItem<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl<T> Ord for PrioItem<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        // BinaryHeap is a max-heap.  Higher priority pops first.  For
        // equal priority, lower `seq` (older insertion) pops first, so
        // we reverse the seq comparison: a smaller seq compares as
        // "greater" inside the max-heap and therefore pops sooner.
        self.priority
            .cmp(&other.priority)
            .then_with(|| other.seq.cmp(&self.seq))
    }
}

impl<T> LaneByPriority<T> {
    /// Default 50/50 lane split with a fixed RNG seed.
    pub fn new() -> Self {
        Self::with_gold_ratio_per_mille(500)
    }

    /// `gold_ratio_per_mille` is the chance (in 1/1000) that a pop pulls
    /// from the gold lane when both lanes are nonempty. 500 = 50/50.
    /// Clamped to `[0, 1000]`.
    pub fn with_gold_ratio_per_mille(ratio: u64) -> Self {
        Self {
            gold_ratio_per_mille: ratio.min(1000),
            rng_state: 0xC0FFEE_5EED_u64,
            next_seq: 0,
            gold: BinaryHeap::new(),
            work: BinaryHeap::new(),
        }
    }

    fn next_seq(&mut self) -> u64 {
        let s = self.next_seq;
        self.next_seq = self.next_seq.wrapping_add(1);
        s
    }

    /// xorshift64 — small, fast, deterministic.
    fn rand_u64(&mut self) -> u64 {
        let mut x = self.rng_state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.rng_state = x;
        x
    }

    fn coin_picks_gold(&mut self) -> bool {
        (self.rand_u64() % 1000) < self.gold_ratio_per_mille
    }
}

impl<T> Default for LaneByPriority<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Send> SchedulerPolicy<T> for LaneByPriority<T> {
    fn push(&mut self, item: WorkItem<T>) {
        let priority = item.priority;
        let seq = self.next_seq();
        let is_gold = item.gold;
        let entry = PrioItem {
            priority,
            seq,
            item,
        };
        if is_gold {
            self.gold.push(entry);
        } else {
            self.work.push(entry);
        }
    }

    fn pop(&mut self) -> Option<WorkItem<T>> {
        match (self.gold.is_empty(), self.work.is_empty()) {
            (true, true) => None,
            (false, true) => self.gold.pop().map(|p| p.item),
            (true, false) => self.work.pop().map(|p| p.item),
            (false, false) => {
                if self.coin_picks_gold() {
                    self.gold.pop().map(|p| p.item)
                } else {
                    self.work.pop().map(|p| p.item)
                }
            }
        }
    }

    fn len(&self) -> usize {
        self.gold.len() + self.work.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::search_framework::stage::WorkItemMeta;

    fn mk(priority: i32, gold: bool, replay_key: u64) -> WorkItem<()> {
        WorkItem {
            stage_id: "test",
            priority,
            gold,
            cost_hint: 1,
            replay_key,
            mass_hint: None,
            meta: WorkItemMeta {
                item_id: replay_key,
                parent_item_id: None,
                fanout_root_id: replay_key,
                depth_from_root: 0,
                spawn_seq: 0,
            },
            payload: (),
        }
    }

    /// Within the work lane, higher-priority items pop first.
    #[test]
    fn priority_orders_within_lane() {
        let mut q = LaneByPriority::with_gold_ratio_per_mille(0);
        // Push priorities [2, 1, 2, 1] all in work lane.
        q.push(mk(2, false, 1));
        q.push(mk(1, false, 2));
        q.push(mk(2, false, 3));
        q.push(mk(1, false, 4));

        // Both 2s come out first, then both 1s.
        let p1 = q.pop().unwrap().priority;
        let p2 = q.pop().unwrap().priority;
        let p3 = q.pop().unwrap().priority;
        let p4 = q.pop().unwrap().priority;
        assert_eq!((p1, p2, p3, p4), (2, 2, 1, 1));
    }

    /// Equal-priority items pop in insertion order (FIFO via seq tie-break).
    #[test]
    fn seq_breaks_priority_ties() {
        let mut q = LaneByPriority::with_gold_ratio_per_mille(0);
        for k in 0..5 {
            q.push(mk(0, false, k));
        }
        let mut got = Vec::new();
        while let Some(item) = q.pop() {
            got.push(item.replay_key);
        }
        assert_eq!(got, vec![0, 1, 2, 3, 4]);
    }

    /// Items only land in the gold lane when `gold = true` is set
    /// explicitly. With gold_ratio = 1.0, gold drains first.
    #[test]
    fn gold_lane_only_when_promoted() {
        let mut q = LaneByPriority::with_gold_ratio_per_mille(1000);
        // Mixed lanes at the same priority.
        q.push(mk(1, false, 1));
        q.push(mk(1, true, 2));
        q.push(mk(1, false, 3));
        q.push(mk(1, true, 4));

        let a = q.pop().unwrap().replay_key;
        let b = q.pop().unwrap().replay_key;
        // The two gold items come out first (FIFO within gold).
        assert_eq!((a, b), (2, 4));
        // Then the two work items.
        let c = q.pop().unwrap().replay_key;
        let d = q.pop().unwrap().replay_key;
        assert_eq!((c, d), (1, 3));
    }

    /// When one lane is empty, pops from the other regardless of the
    /// configured gold_ratio.
    #[test]
    fn empty_lane_falls_through() {
        // Only gold items, but gold_ratio is 0 (favor work).  Should
        // still drain the gold lane.
        let mut q = LaneByPriority::with_gold_ratio_per_mille(0);
        for k in 0..3 {
            q.push(mk(0, true, k));
        }
        let mut got = Vec::new();
        while let Some(item) = q.pop() {
            got.push(item.replay_key);
        }
        assert_eq!(got, vec![0, 1, 2]);
    }

    /// At gold_ratio = 500/1000, popping equal numbers of gold and work
    /// items at the same priority should split the first half of pops
    /// roughly 50/50.  Loose bounds — the goal is to detect "always
    /// gold" or "never gold" classifier bugs, not to validate RNG
    /// distribution.
    #[test]
    fn coin_split_balances_lanes_in_aggregate() {
        let mut q = LaneByPriority::with_gold_ratio_per_mille(500);
        for k in 0..1000 {
            q.push(mk(0, true, k));
        }
        for k in 1000..2000 {
            q.push(mk(0, false, k));
        }
        // Pop 1000.  Count how many came from gold (replay_key < 1000).
        let mut gold_count = 0;
        for _ in 0..1000 {
            let item = q.pop().expect("queue non-empty");
            if item.replay_key < 1000 {
                gold_count += 1;
            }
        }
        // Wide tolerance — we just want to rule out 0% or 100%.
        assert!(
            (400..=600).contains(&gold_count),
            "expected ~500 gold pops in first 1000, got {gold_count}",
        );
    }
}
