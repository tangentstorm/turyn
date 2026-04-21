//! Framework mode adapters — one module per `--wz` / `--stochastic`
//! entry point. All five search modes route through these.
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
