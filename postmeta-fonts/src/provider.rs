//! Font provider trait

use crate::data::FontData;

/// Resolves font names to loaded font data
///
/// Names are matched as given; implementations handle any case normalization themselves.
pub trait FontProvider {
    /// Look up a font by name, returning `None` if it is not available
    fn font(&self, name: &str) -> Option<&FontData>;
}
