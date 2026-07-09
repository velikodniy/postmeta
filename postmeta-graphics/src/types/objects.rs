//! High-level graphical objects: text, fills, strokes, and pictures

use std::sync::Arc;

use super::geometry::Scalar;
use super::style::{Color, DashPattern, LineCap, LineJoin};
use crate::path::SharedPath;
use crate::pen::Pen;
use crate::transform::Transform;

// ---------------------------------------------------------------------------
// GraphicsObject
// ---------------------------------------------------------------------------

/// A single graphical object in a picture
#[derive(Debug, Clone, PartialEq)]
pub enum GraphicsObject {
    /// A filled region (path must be cyclic)
    Fill(FillObject),
    Stroke(StrokeObject),
    Text(TextObject),
    /// A nested picture (used for grouping, clipping, and bounding)
    Picture(crate::picture::Picture),
}

/// A filled contour
#[derive(Debug, Clone, PartialEq)]
pub struct FillObject {
    pub path: SharedPath,
    pub color: Color,
    /// Optional pen for `filldraw` (stroke the contour too)
    pub pen: Option<Pen>,
    pub line_join: LineJoin,
    pub miter_limit: Scalar,
}

/// A stroked path
#[derive(Debug, Clone, PartialEq)]
pub struct StrokeObject {
    pub path: SharedPath,
    pub pen: Pen,
    pub color: Color,
    pub dash: Option<DashPattern>,
    pub line_cap: LineCap,
    pub line_join: LineJoin,
    pub miter_limit: Scalar,
}

/// Precomputed text dimensions at the nominal font size
///
/// Populated by the interpreter from real font metrics (via `FontProvider`) or a heuristic fallback.
/// The graphics layer trusts these values for bounding-box and layout and never recomputes them.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct TextMetrics {
    /// Total advance width in points (character advances + kerning)
    pub width: Scalar,
    /// Ascender above the baseline, in points (positive upward)
    pub height: Scalar,
    /// Descender below the baseline, in points (positive downward)
    pub depth: Scalar,
}

/// A text label
#[derive(Debug, Clone, PartialEq)]
pub struct TextObject {
    pub text: Arc<str>,
    pub font_name: Arc<str>,
    pub font_size: Scalar,
    pub metrics: TextMetrics,
    pub color: Color,
    pub transform: Transform,
}
