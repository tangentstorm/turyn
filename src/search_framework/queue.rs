use std::collections::VecDeque;

use crate::search_framework::stage::WorkItem;

pub trait SchedulerPolicy<T>: Send {
    fn push(&mut self, item: WorkItem<T>);
    fn pop(&mut self) -> Option<WorkItem<T>>;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// Baseline policy that mirrors today's DualQueue semantics:
/// a "gold" lane for high-value terminal-ish work and a general work lane.
pub struct GoldThenWork<T> {
    fairness_window: usize,
    gold_since_work: usize,
    gold: VecDeque<WorkItem<T>>,
    work: VecDeque<WorkItem<T>>,
}

impl<T> GoldThenWork<T> {
    pub fn new(fairness_window: usize) -> Self {
        Self {
            fairness_window: fairness_window.max(1),
            gold_since_work: 0,
            gold: VecDeque::new(),
            work: VecDeque::new(),
        }
    }

    fn is_gold(item: &WorkItem<T>) -> bool {
        item.priority > 0
    }
}

impl<T: Send> SchedulerPolicy<T> for GoldThenWork<T> {
    fn push(&mut self, item: WorkItem<T>) {
        if Self::is_gold(&item) {
            self.gold.push_back(item);
        } else {
            self.work.push_back(item);
        }
    }

    fn pop(&mut self) -> Option<WorkItem<T>> {
        if !self.gold.is_empty()
            && (self.work.is_empty() || self.gold_since_work < self.fairness_window)
        {
            self.gold_since_work += 1;
            return self.gold.pop_front();
        }

        if let Some(item) = self.work.pop_front() {
            self.gold_since_work = 0;
            return Some(item);
        }

        self.gold_since_work = 0;
        self.gold.pop_front()
    }

    fn len(&self) -> usize {
        self.gold.len() + self.work.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::search_framework::stage::WorkItemMeta;

    fn mk(priority: i32, replay_key: u64) -> WorkItem<()> {
        WorkItem {
            stage_id: "test",
            priority,
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

    #[test]
    fn fairness_window_prevents_work_starvation() {
        let mut q = GoldThenWork::new(2);
        q.push(mk(1, 1));
        q.push(mk(1, 2));
        q.push(mk(1, 3));
        q.push(mk(0, 4));

        let a = q.pop().unwrap().replay_key;
        let b = q.pop().unwrap().replay_key;
        let c = q.pop().unwrap().replay_key;
        assert_eq!((a, b, c), (1, 2, 4));
    }
}
