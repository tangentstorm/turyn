//! Phase-1 placeholders for legacy mode adapters.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdapterKind {
    Cross,
    Apart,
    Together,
    Sync,
    Stochastic,
}
