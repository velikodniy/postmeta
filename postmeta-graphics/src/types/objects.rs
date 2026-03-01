//! High-level graphical objects: text, fills, strokes, and pictures.

use std::sync::Arc;

use super::geometry::Scalar;
use super::style::{Color, DashPattern, LineCap, LineJoin};
use crate::path::Path;
use crate::pen::Pen;
use crate::transform::Transform;

// ---------------------------------------------------------------------------
// Picture and GraphicsObject
// ---------------------------------------------------------------------------

/// A single graphical object in a picture.
#[derive(Debug, Clone, PartialEq)]
pub enum GraphicsObject {
    /// A filled region (path must be cyclic).
    Fill(FillObject),
    /// A stroked path.
    Stroke(StrokeObject),
    /// A text label.
    Text(TextObject),
    /// Begin a clipping region.
    ClipStart(Path),
    /// End the most recent clipping region.
    ClipEnd,
    /// Begin a bounding-box override region.
    SetBoundsStart(Path),
    /// End the most recent bounding-box override.
    SetBoundsEnd,
}

/// A filled contour.
#[derive(Debug, Clone, PartialEq)]
pub struct FillObject {
    pub path: Path,
    pub color: Color,
    /// Optional pen for "filldraw" (stroke the contour too).
    pub pen: Option<Pen>,
    pub line_join: LineJoin,
    pub miter_limit: Scalar,
}

/// A stroked path.
#[derive(Debug, Clone, PartialEq)]
pub struct StrokeObject {
    pub path: Path,
    pub pen: Pen,
    pub color: Color,
    pub dash: Option<DashPattern>,
    pub line_cap: LineCap,
    pub line_join: LineJoin,
    pub miter_limit: Scalar,
}

/// Precomputed text dimensions at the nominal font size.
///
/// Populated by the interpreter from real font metrics (via `FontProvider`)
/// or a heuristic fallback.  The graphics layer trusts these values and
/// never recomputes them — it simply uses them for bounding-box and layout.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct TextMetrics {
    /// Total advance width in points (character advances + kerning).
    pub width: Scalar,
    /// Ascender above the baseline, in points (positive upward).
    pub height: Scalar,
    /// Descender below the baseline, in points (positive downward).
    pub depth: Scalar,
}

/// A text label.
#[derive(Debug, Clone, PartialEq)]
pub struct TextObject {
    pub text: Arc<str>,
    pub font_name: Arc<str>,
    pub font_size: Scalar,
    pub metrics: TextMetrics,
    pub color: Color,
    pub transform: Transform,
}

/// An ordered collection of graphical objects.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Picture {
    pub objects: Vec<GraphicsObject>,
}

impl Picture {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            objects: Vec::new(),
        }
    }

    pub fn push(&mut self, obj: GraphicsObject) {
        self.objects.push(obj);
    }

    /// Append all objects from another picture.
    pub fn merge(&mut self, other: Self) {
        self.objects.extend(other.objects);
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
#[expect(
    clippy::float_cmp,
    reason = "exact float comparisons are intentional in tests"
)]
mod tests {
    use super::super::geometry::Point;
    use super::super::knot::Knot;
    use super::*;

    #[test]
    fn path_num_segments() {
        // Empty path
        let p = Path::new();
        assert_eq!(p.num_segments(), 0);

        // Open path with 3 knots = 2 segments
        let p = Path::from_knots(
            vec![
                Knot::new(Point::ZERO),
                Knot::new(Point::new(1.0, 0.0)),
                Knot::new(Point::new(1.0, 1.0)),
            ],
            false,
        );
        assert_eq!(p.num_segments(), 2);

        // Cyclic path with 3 knots = 3 segments
        let p = Path::from_knots(
            vec![
                Knot::new(Point::ZERO),
                Knot::new(Point::new(1.0, 0.0)),
                Knot::new(Point::new(1.0, 1.0)),
            ],
            true,
        );
        assert_eq!(p.num_segments(), 3);
    }

    #[test]
    fn picture_merge() {
        let mut p1 = Picture::new();
        p1.push(GraphicsObject::ClipEnd);
        let mut p2 = Picture::new();
        p2.push(GraphicsObject::SetBoundsEnd);
        p1.merge(p2);
        assert_eq!(p1.objects.len(), 2);
    }
}
