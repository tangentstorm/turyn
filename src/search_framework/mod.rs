//! Unified search framework runtime.
//!
//! `engine` owns the central coordinator + worker pool. `queue`,
//! `stage`, `events`, and `mass` supply the scheduler, stage
//! handler protocol, progress / forcing event schema, and TTC
//! mass model. `mode_adapters` carries the five per-mode shims
//! (`mdd_stages` for cross/apart/together, `sync` for the sync
//! walker, `stochastic` for sampling).
//!
//! Module-level `#![allow(dead_code)]`: the framework defines a
//! number of diagnostic / reporting surfaces (`render_sankey_text`,
//! `LevelCutAttribution`, `FanoutRootCounters`, `EdgeFlowCounters`,
//! the optional `Continuation::{Split, Resume}` deferral variants,
//! the `StageContext` snapshot fields, `StageHandler::id`) that
//! the current adapter set does not read yet. They're public API
//! the per-mode adapters reach for as they get smarter about
//! per-stage coverage-bits accounting and post-run visualisation;
//! treating them as dead would prune useful handles mid-migration.
#![allow(dead_code)]

pub mod engine;
pub mod events;
pub mod mass;
pub mod mode_adapters;
pub mod queue;
pub mod stage;
