//! Phase-1 placeholders for legacy mode adapters.
pub mod apart_together;
pub mod mdd_stages;
pub mod stochastic;
pub mod sync;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdapterKind {
    Cross,
    Apart,
    Together,
    Sync,
    Stochastic,
}
