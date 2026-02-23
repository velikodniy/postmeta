//! Font provider trait.

use crate::data::FontData;

/// Trait for resolving font names to loaded font data.
///
/// Implementations may look up fonts from embedded data, the filesystem,
/// or any other source. Font names are matched as given; implementations
/// should handle case normalization internally if desired.
pub trait FontProvider {
    /// Look up a font by name. Returns `None` if the font is not available.
    fn font(&self, name: &str) -> Option<&FontData>;
}
