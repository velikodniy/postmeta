//! Axis-aligned bounding box computation.
//!
//! Provides [`BoundingBox`] and helpers for computing bounds of paths,
//! pens, and pictures.

use crate::path::{BezierPath, Path};
use crate::types::{GraphicsObject, KnotDirection, Pen, Picture, Point, Scalar, TextObject, Vec2};

// ---------------------------------------------------------------------------
// BoundingBox type
// ---------------------------------------------------------------------------

/// Axis-aligned bounding box.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct BoundingBox {
    pub min_x: Scalar,
    pub min_y: Scalar,
    pub max_x: Scalar,
    pub max_y: Scalar,
}

impl BoundingBox {
    /// An empty (inverted) bounding box.
    pub const EMPTY: Self = Self {
        min_x: Scalar::INFINITY,
        min_y: Scalar::INFINITY,
        max_x: Scalar::NEG_INFINITY,
        max_y: Scalar::NEG_INFINITY,
    };

    /// Check if this bounding box is valid (non-empty).
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.min_x <= self.max_x && self.min_y <= self.max_y
    }

    /// Width.
    #[must_use]
    pub fn width(&self) -> Scalar {
        if self.is_valid() {
            self.max_x - self.min_x
        } else {
            0.0
        }
    }

    /// Height.
    #[must_use]
    pub fn height(&self) -> Scalar {
        if self.is_valid() {
            self.max_y - self.min_y
        } else {
            0.0
        }
    }

    /// Lower-left corner.
    #[must_use]
    pub const fn llcorner(&self) -> Point {
        Point::new(self.min_x, self.min_y)
    }

    /// Lower-right corner.
    #[must_use]
    pub const fn lrcorner(&self) -> Point {
        Point::new(self.max_x, self.min_y)
    }

    /// Upper-left corner.
    #[must_use]
    pub const fn ulcorner(&self) -> Point {
        Point::new(self.min_x, self.max_y)
    }

    /// Upper-right corner.
    #[must_use]
    pub const fn urcorner(&self) -> Point {
        Point::new(self.max_x, self.max_y)
    }

    /// Expand to include a point.
    pub const fn include_point(&mut self, p: Point) {
        self.min_x = self.min_x.min(p.x);
        self.min_y = self.min_y.min(p.y);
        self.max_x = self.max_x.max(p.x);
        self.max_y = self.max_y.max(p.y);
    }

    /// Expand to include another bounding box.
    pub fn union(&mut self, other: &Self) {
        if other.is_valid() {
            self.min_x = self.min_x.min(other.min_x);
            self.min_y = self.min_y.min(other.min_y);
            self.max_x = self.max_x.max(other.max_x);
            self.max_y = self.max_y.max(other.max_y);
        }
    }

    /// Compute the bounding box of a path (control-point hull).
    ///
    /// This is a conservative estimate using the convex hull of all control
    /// points, not the tight bound. This matches `MetaPost`'s behavior.
    #[must_use]
    pub fn of_path(path: &Path) -> Self {
        path.knots.iter().fold(Self::EMPTY, |mut bb, knot| {
            bb.include_point(knot.point);
            if let KnotDirection::Explicit(cp) = knot.left {
                bb.include_point(cp);
            }
            if let KnotDirection::Explicit(cp) = knot.right {
                bb.include_point(cp);
            }
            bb
        })
    }

    /// Compute the bounding box of a [`BezierPath`] (control-point hull).
    ///
    /// This is a conservative estimate using the convex hull of all control
    /// points, not the tight bound. This matches `MetaPost`'s behavior.
    #[must_use]
    pub fn of_bezier_path(path: &BezierPath) -> Self {
        let mut bb = Self::EMPTY;
        for seg in path.segments() {
            let (min, max) = seg.bbox();
            bb.include_point(min);
            bb.include_point(max);
        }
        bb
    }

    /// Compute the bounding box of a picture.
    ///
    /// When `true_corners` is false, `SetBounds` regions override the
    /// computed bbox. When true, they are ignored.
    #[must_use]
    pub fn of_picture(pic: &Picture, true_corners: bool) -> Self {
        let mut bb = Self::EMPTY;
        let mut bounds_stack: Vec<Self> = Vec::new();

        for obj in &pic.objects {
            match obj {
                GraphicsObject::Fill(fill) => {
                    let pbb = Self::of_path(&fill.path);
                    bb.union(&pbb);
                }
                GraphicsObject::Stroke(stroke) => {
                    let mut pbb = Self::of_path(&stroke.path);
                    // Expand by pen extent (rough estimate)
                    let pen_extent = pen_max_extent(&stroke.pen);
                    pbb.min_x -= pen_extent;
                    pbb.min_y -= pen_extent;
                    pbb.max_x += pen_extent;
                    pbb.max_y += pen_extent;
                    bb.union(&pbb);
                }
                GraphicsObject::Text(text) => {
                    expand_for_text(text, &mut bb);
                }
                GraphicsObject::SetBoundsStart(path) if !true_corners => {
                    bounds_stack.push(bb);
                    bb = Self::of_path(path);
                }
                GraphicsObject::SetBoundsEnd if !true_corners => {
                    if let Some(prev) = bounds_stack.pop() {
                        let current = bb;
                        bb = prev;
                        bb.union(&current);
                    }
                }
                GraphicsObject::ClipStart(_)
                | GraphicsObject::ClipEnd
                | GraphicsObject::SetBoundsStart(_)
                | GraphicsObject::SetBoundsEnd => {}
            }
        }

        bb
    }
}

impl Default for BoundingBox {
    fn default() -> Self {
        Self::EMPTY
    }
}

// ---------------------------------------------------------------------------
// Private helpers
// ---------------------------------------------------------------------------

/// Rough estimate of the maximum pen extent (half-width).
fn pen_max_extent(pen: &Pen) -> Scalar {
    match pen {
        Pen::Elliptical(t) => {
            // Max of the two basis vector lengths (columns of the 2×2 matrix)
            let len1 = t.txx.hypot(t.tyx);
            let len2 = t.txy.hypot(t.tyy);
            len1.max(len2)
        }
        Pen::Polygonal(verts) => verts
            .iter()
            .map(|v| Vec2::from(*v).length())
            .fold(0.0, Scalar::max),
    }
}

/// Expand a bounding box to include a text object's extent.
///
/// Uses the precomputed [`TextMetrics`] stored on the object.  If all
/// metrics are zero (no font data available), the text contributes a
/// single degenerate point at its origin.
fn expand_for_text(text: &TextObject, bb: &mut BoundingBox) {
    let m = &text.metrics;
    let corners = [
        Point::new(0.0, -m.depth),
        Point::new(m.width, -m.depth),
        Point::new(m.width, m.height),
        Point::new(0.0, m.height),
    ];
    for corner in &corners {
        bb.include_point(text.transform.apply(*corner));
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
    use super::*;
    use crate::types::{Color, EPSILON, Knot, TextMetrics, Transform};
    use std::sync::Arc;

    fn make_unit_square() -> Path {
        // A cyclic square path with explicit controls (straight lines)
        let pts = [
            Point::new(0.0, 0.0),
            Point::new(10.0, 0.0),
            Point::new(10.0, 10.0),
            Point::new(0.0, 10.0),
        ];
        let knots = (0..4)
            .map(|i| {
                let j = (i + 1) % 4;
                let prev = (i + 3) % 4;
                let right_cp = Point::new(
                    pts[i].x + (pts[j].x - pts[i].x) / 3.0,
                    pts[i].y + (pts[j].y - pts[i].y) / 3.0,
                );
                let left_cp = Point::new(
                    pts[prev].x + 2.0 * (pts[i].x - pts[prev].x) / 3.0,
                    pts[prev].y + 2.0 * (pts[i].y - pts[prev].y) / 3.0,
                );
                Knot::with_controls(pts[i], left_cp, right_cp)
            })
            .collect();
        Path::from_knots(knots, true)
    }

    #[test]
    fn test_bounding_box_empty() {
        let bb = BoundingBox::EMPTY;
        assert!(!bb.is_valid());
        assert_eq!(bb.width(), 0.0);
        assert_eq!(bb.height(), 0.0);
    }

    #[test]
    fn test_bounding_box_include_point() {
        let mut bb = BoundingBox::EMPTY;
        bb.include_point(Point::new(1.0, 2.0));
        bb.include_point(Point::new(5.0, 8.0));
        assert!(bb.is_valid());
        assert!((bb.min_x - 1.0).abs() < EPSILON);
        assert!((bb.min_y - 2.0).abs() < EPSILON);
        assert!((bb.max_x - 5.0).abs() < EPSILON);
        assert!((bb.max_y - 8.0).abs() < EPSILON);
    }

    #[test]
    fn test_path_bbox() {
        let path = make_unit_square();
        let bb = BoundingBox::of_path(&path);
        assert!(bb.is_valid());
        assert!(bb.min_x < 0.1);
        assert!(bb.min_y < 0.1);
        assert!(bb.max_x > 9.9);
        assert!(bb.max_y > 9.9);
    }

    #[test]
    fn test_picture_bbox() {
        use crate::types::{Color, FillObject, LineJoin};
        let mut pic = Picture::new();
        let path = make_unit_square();
        pic.add_fill(FillObject {
            path,
            color: Color::BLACK,
            pen: None,
            line_join: LineJoin::Round,
            miter_limit: 10.0,
        });

        let bb = BoundingBox::of_picture(&pic, true);
        assert!(bb.is_valid());
        assert!(bb.width() > 9.0);
        assert!(bb.height() > 9.0);
    }

    #[test]
    fn test_bounding_box_corners() {
        let bb = BoundingBox {
            min_x: 1.0,
            min_y: 2.0,
            max_x: 5.0,
            max_y: 8.0,
        };
        assert_eq!(bb.llcorner(), Point::new(1.0, 2.0));
        assert_eq!(bb.lrcorner(), Point::new(5.0, 2.0));
        assert_eq!(bb.ulcorner(), Point::new(1.0, 8.0));
        assert_eq!(bb.urcorner(), Point::new(5.0, 8.0));
    }

    #[test]
    fn test_bounding_box_union() {
        let mut bb1 = BoundingBox {
            min_x: 0.0,
            min_y: 0.0,
            max_x: 5.0,
            max_y: 5.0,
        };
        let bb2 = BoundingBox {
            min_x: 3.0,
            min_y: 3.0,
            max_x: 10.0,
            max_y: 10.0,
        };
        bb1.union(&bb2);
        assert!((bb1.min_x).abs() < EPSILON);
        assert!((bb1.max_x - 10.0).abs() < EPSILON);
    }

    #[test]
    fn text_bbox_uses_stored_metrics() {
        let text = TextObject {
            text: Arc::from("Hello"),
            font_name: Arc::from("cmr10"),
            font_size: 10.0,
            metrics: TextMetrics {
                width: 25.0,
                height: 8.0,
                depth: 2.0,
            },
            color: Color::BLACK,
            transform: Transform::IDENTITY,
        };
        let mut pic = Picture::new();
        pic.objects.push(GraphicsObject::Text(text));
        let bb = BoundingBox::of_picture(&pic, false);

        assert!((bb.min_x).abs() < EPSILON, "min_x: {}", bb.min_x);
        assert!((bb.max_x - 25.0).abs() < EPSILON, "max_x: {}", bb.max_x);
        assert!((bb.max_y - 8.0).abs() < EPSILON, "max_y: {}", bb.max_y);
        assert!((bb.min_y + 2.0).abs() < EPSILON, "min_y: {}", bb.min_y);
    }

    #[test]
    fn text_bbox_zero_metrics_is_degenerate() {
        let text = TextObject {
            text: Arc::from("Hello"),
            font_name: Arc::from("cmr10"),
            font_size: 10.0,
            metrics: TextMetrics::default(),
            color: Color::BLACK,
            transform: Transform::IDENTITY,
        };
        let mut pic = Picture::new();
        pic.objects.push(GraphicsObject::Text(text));
        let bb = BoundingBox::of_picture(&pic, false);

        // Zero metrics → all four corners collapse to the origin.
        assert!(bb.min_x.abs() < EPSILON, "min_x: {}", bb.min_x);
        assert!(bb.max_x.abs() < EPSILON, "max_x: {}", bb.max_x);
        assert!(bb.min_y.abs() < EPSILON, "min_y: {}", bb.min_y);
        assert!(bb.max_y.abs() < EPSILON, "max_y: {}", bb.max_y);
    }

    #[test]
    fn pen_max_extent_elliptical() {
        let pen = Pen::circle(2.0);
        let extent = pen_max_extent(&pen);
        // pencircle scaled 2 should have extent ~1
        assert!((extent - 1.0).abs() < 0.01, "extent: {extent}");
    }

    #[test]
    fn pen_max_extent_polygonal() {
        let pen = Pen::Polygonal(vec![
            Point::new(3.0, 0.0),
            Point::new(0.0, 4.0),
            Point::new(-3.0, 0.0),
        ]);
        let extent = pen_max_extent(&pen);
        assert!((extent - 4.0).abs() < EPSILON, "extent: {extent}");
    }

    // -----------------------------------------------------------------------
    // BezierPath bounding box
    // -----------------------------------------------------------------------

    #[test]
    fn bezier_path_bbox() {
        use crate::path::bezier_path::SegmentControls;

        // Build a 10x10 square as a cyclic BezierPath with straight-line controls.
        let pts = [
            Point::new(0.0, 0.0),
            Point::new(10.0, 0.0),
            Point::new(10.0, 10.0),
            Point::new(0.0, 10.0),
        ];
        let controls = (0..4)
            .map(|i| {
                let j = (i + 1) % 4;
                SegmentControls {
                    post: pts[i].lerp(pts[j], 1.0 / 3.0),
                    pre: pts[i].lerp(pts[j], 2.0 / 3.0),
                }
            })
            .collect();
        let bp = BezierPath::from_parts(pts.to_vec(), controls, true);

        let bb = BoundingBox::of_bezier_path(&bp);
        assert!(bb.is_valid());
        assert!(bb.min_x < 0.1, "min_x: {}", bb.min_x);
        assert!(bb.min_y < 0.1, "min_y: {}", bb.min_y);
        assert!(bb.max_x > 9.9, "max_x: {}", bb.max_x);
        assert!(bb.max_y > 9.9, "max_y: {}", bb.max_y);
    }

    #[test]
    fn bezier_path_bbox_empty() {
        let bp = BezierPath::new();
        let bb = BoundingBox::of_bezier_path(&bp);
        assert!(!bb.is_valid());
    }

    #[test]
    fn bezier_path_bbox_single_segment() {
        use crate::path::bezier_path::SegmentControls;

        // A line from (2, 3) to (8, 7) with controls that bulge outward.
        let bp = BezierPath::from_parts(
            vec![Point::new(2.0, 3.0), Point::new(8.0, 7.0)],
            vec![SegmentControls {
                post: Point::new(4.0, 0.0), // below the line
                pre: Point::new(6.0, 10.0), // above the line
            }],
            false,
        );

        let bb = BoundingBox::of_bezier_path(&bp);
        assert!(bb.is_valid());
        // The bbox should encompass all 4 control points.
        assert!(bb.min_x <= 2.0 + EPSILON, "min_x: {}", bb.min_x);
        assert!(bb.min_y <= 0.0 + EPSILON, "min_y: {}", bb.min_y);
        assert!(bb.max_x >= 8.0 - EPSILON, "max_x: {}", bb.max_x);
        assert!(bb.max_y >= 10.0 - EPSILON, "max_y: {}", bb.max_y);
    }
}
