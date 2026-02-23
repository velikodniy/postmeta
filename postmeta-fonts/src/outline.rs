//! Glyph outline extraction.
//!
//! Defines [`OutlineSink`], a trait for receiving glyph outline commands.
//! This is our own trait (not `ttf_parser::OutlineBuilder`) so that
//! consumers do not need to depend on `ttf-parser` directly.
//! Coordinates are pre-scaled to the requested font size.

/// Receiver for glyph outline commands.
///
/// Coordinates are in points, pre-scaled from font design units.
/// The coordinate system is Y-up (matching font conventions and `MetaPost`).
pub trait OutlineSink {
    /// Start a new contour at the given point.
    fn move_to(&mut self, x: f64, y: f64);
    /// Draw a straight line to the given point.
    fn line_to(&mut self, x: f64, y: f64);
    /// Draw a quadratic Bezier curve (TrueType-style).
    fn quad_to(&mut self, x1: f64, y1: f64, x: f64, y: f64);
    /// Draw a cubic Bezier curve (CFF/OpenType-style).
    fn curve_to(&mut self, x1: f64, y1: f64, x2: f64, y2: f64, x: f64, y: f64);
    /// Close the current contour.
    fn close(&mut self);
}
