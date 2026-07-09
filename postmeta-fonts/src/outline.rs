//! Glyph outline extraction

/// Receiver for glyph outline commands
///
/// A local trait rather than `ttf_parser::OutlineBuilder`, so consumers need not depend on `ttf-parser`.
/// Coordinates are in points, pre-scaled from design units, Y-up (matching font conventions and `MetaPost`).
pub trait OutlineSink {
    /// Start a new contour
    fn move_to(&mut self, x: f64, y: f64);
    fn line_to(&mut self, x: f64, y: f64);
    /// Quadratic Bezier segment (TrueType outlines)
    fn quad_to(&mut self, x1: f64, y1: f64, x: f64, y: f64);
    /// Cubic Bezier segment (CFF/OpenType outlines)
    fn curve_to(&mut self, x1: f64, y1: f64, x2: f64, y2: f64, x: f64, y: f64);
    fn close(&mut self);
}
