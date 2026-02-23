//! Text metric types.

/// Aggregate metrics for a rendered text string at a specific font size.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct TextMetrics {
    /// Total advance width in points (sum of character advances + kerning).
    pub width: f64,
    /// Maximum ascender height in points (positive, above baseline).
    pub height: f64,
    /// Maximum descender depth in points (positive, below baseline).
    pub depth: f64,
}
