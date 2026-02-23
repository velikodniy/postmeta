//! Font loading, metrics, and glyph outline extraction for `PostMeta`.
//!
//! This crate wraps `ttf-parser` to provide OpenType font support.
//! It is intentionally independent of `postmeta-graphics` — all types
//! are plain `f64`/`u16` values. Bridging to `PostMeta`'s graphics types
//! happens in the consuming crates (`postmeta-core`, `postmeta-svg`).

pub mod composite;
pub mod data;
pub mod error;
pub mod metrics;
pub mod outline;
pub mod provider;

mod embedded;

pub use composite::CompositeFontProvider;
pub use data::FontData;
pub use error::FontError;
pub use metrics::TextMetrics;
pub use outline::OutlineSink;
pub use provider::FontProvider;
