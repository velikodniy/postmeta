//! Font loading, metrics, and glyph outline extraction for `PostMeta`
//!
//! Wraps `ttf-parser` for OpenType support.
//! Intentionally independent of `postmeta-graphics`: all types are plain `f64`/`u16`, and consuming crates bridge to graphics types.

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
