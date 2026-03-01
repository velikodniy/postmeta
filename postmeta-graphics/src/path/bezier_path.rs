//! Resolved cubic Bezier path representation.
//!
//! A [`BezierPath`] stores on-curve knot points and per-segment control point
//! pairs ([`SegmentControls`]).  It is produced by resolving a [`KnotPath`]
//! (running Hobby's algorithm) and provides efficient segment-level access
//! without the direction/tension metadata carried by knots.
//!
//! [`KnotPath`]: super::KnotPath

use crate::bezier::CubicSegment;
use crate::types::{Knot, KnotDirection, Point};

// ---------------------------------------------------------------------------
// SegmentControls
// ---------------------------------------------------------------------------

/// A pair of Bezier control handles for one cubic segment.
///
/// `post` is the handle leaving the start knot (postcontrol), and `pre` is
/// the handle arriving at the end knot (precontrol).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SegmentControls {
    /// Handle leaving the start knot (postcontrol).
    pub post: Point,
    /// Handle arriving at the end knot (precontrol).
    pub pre: Point,
}

// ---------------------------------------------------------------------------
// BezierPath
// ---------------------------------------------------------------------------

/// A resolved cubic Bezier path.
///
/// Stores the on-curve knot points and per-segment control point pairs.
/// Created by calling [`KnotPath::resolve()`](super::KnotPath::resolve).
#[derive(Debug, Clone, PartialEq)]
pub struct BezierPath {
    /// On-curve points at each knot.
    points: Vec<Point>,
    /// Per-segment control point pairs.
    controls: Vec<SegmentControls>,
    /// Whether the path is closed.
    is_cyclic: bool,
}

impl BezierPath {
    /// Create an empty open path.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            points: Vec::new(),
            controls: Vec::new(),
            is_cyclic: false,
        }
    }

    /// Construct a `BezierPath` from raw parts.
    ///
    /// # Panics
    ///
    /// Panics (in debug builds) if the number of controls does not match
    /// the expected segment count for the given points and cyclicity.
    #[must_use]
    pub fn from_parts(points: Vec<Point>, controls: Vec<SegmentControls>, is_cyclic: bool) -> Self {
        debug_assert_eq!(
            controls.len(),
            if points.is_empty() {
                0
            } else if is_cyclic {
                points.len()
            } else {
                points.len().saturating_sub(1)
            },
            "controls.len() does not match expected segment count for {} points (cyclic={})",
            points.len(),
            is_cyclic,
        );
        Self {
            points,
            controls,
            is_cyclic,
        }
    }

    /// Number of cubic segments in the path.
    #[must_use]
    pub fn num_segments(&self) -> usize {
        self.controls.len()
    }

    /// Number of on-curve knot points.
    #[must_use]
    pub fn num_knots(&self) -> usize {
        self.points.len()
    }

    /// Whether the path is cyclic (closed).
    #[must_use]
    pub const fn is_cyclic(&self) -> bool {
        self.is_cyclic
    }

    /// Get the on-curve point at knot index `i`.
    ///
    /// # Panics
    ///
    /// Panics if `i >= self.num_knots()`.
    #[must_use]
    pub fn knot_point(&self, i: usize) -> Point {
        self.points[i]
    }

    /// Get all on-curve knot points as a slice.
    #[must_use]
    pub fn knot_points(&self) -> &[Point] {
        &self.points
    }

    /// Get segment `i` as a [`CubicSegment`] (an owned 64-byte copy).
    ///
    /// # Panics
    ///
    /// Panics if `i >= self.num_segments()`.
    #[must_use]
    pub fn segment(&self, i: usize) -> CubicSegment {
        let ctrl = &self.controls[i];
        let j = (i + 1) % self.points.len();
        CubicSegment::new(self.points[i], ctrl.post, ctrl.pre, self.points[j])
    }

    /// Iterate over all segments as [`CubicSegment`] values.
    pub fn segments(&self) -> impl Iterator<Item = CubicSegment> + '_ {
        (0..self.num_segments()).map(move |i| self.segment(i))
    }

    /// Convert this resolved path back to a [`KnotPath`](super::KnotPath)
    /// with explicit control points.
    ///
    /// This is useful for operations (like path concatenation) that still
    /// operate on `KnotPath`.
    #[must_use]
    pub fn to_knot_path(&self) -> super::KnotPath {
        let n = self.num_segments();
        let mut knots = Vec::with_capacity(self.points.len());

        for (i, &point) in self.points.iter().enumerate() {
            let left = if i > 0 || self.is_cyclic {
                let seg_idx = if i == 0 { n - 1 } else { i - 1 };
                KnotDirection::Explicit(self.controls[seg_idx].pre)
            } else {
                KnotDirection::Open
            };

            let right = if i < n {
                KnotDirection::Explicit(self.controls[i].post)
            } else {
                KnotDirection::Open
            };

            knots.push(Knot {
                point,
                left,
                right,
                left_tension: 1.0,
                right_tension: 1.0,
            });
        }

        super::KnotPath::from_knots(knots, self.is_cyclic)
    }
}

impl Default for BezierPath {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{EPSILON, Knot, KnotDirection, Point};

    /// Helper: build a `BezierPath` for a straight line from (0,0) to (10,0).
    fn make_line_bezier() -> BezierPath {
        let points = vec![Point::new(0.0, 0.0), Point::new(10.0, 0.0)];
        let controls = vec![SegmentControls {
            post: Point::new(10.0 / 3.0, 0.0),
            pre: Point::new(20.0 / 3.0, 0.0),
        }];
        BezierPath::from_parts(points, controls, false)
    }

    /// Helper: build a cyclic triangle `BezierPath` with straight-line controls.
    fn make_triangle_bezier() -> BezierPath {
        let pts = [
            Point::new(0.0, 0.0),
            Point::new(10.0, 0.0),
            Point::new(5.0, 10.0),
        ];
        let controls = (0..3)
            .map(|i| {
                let j = (i + 1) % 3;
                SegmentControls {
                    post: pts[i].lerp(pts[j], 1.0 / 3.0),
                    pre: pts[i].lerp(pts[j], 2.0 / 3.0),
                }
            })
            .collect();
        BezierPath::from_parts(pts.to_vec(), controls, true)
    }

    // -- Test 1: BezierPath::new() is empty ----------------------------------

    #[test]
    fn new_is_empty() {
        let bp = BezierPath::new();
        assert_eq!(bp.num_segments(), 0);
        assert_eq!(bp.num_knots(), 0);
        assert!(!bp.is_cyclic());
        assert!(bp.knot_points().is_empty());
    }

    // -- Test 2: BezierPath::from_parts() with a simple line segment ----------

    #[test]
    fn from_parts_line_segment() {
        let bp = make_line_bezier();
        assert_eq!(bp.num_knots(), 2);
        assert_eq!(bp.num_segments(), 1);
        assert!(!bp.is_cyclic());
        assert!((bp.knot_point(0).x - 0.0).abs() < EPSILON);
        assert!((bp.knot_point(1).x - 10.0).abs() < EPSILON);
    }

    // -- Test 3: segment() returns correct CubicSegment ----------------------

    #[test]
    fn segment_returns_correct_cubic() {
        let bp = make_line_bezier();
        let seg = bp.segment(0);
        assert!((seg.p0.x - 0.0).abs() < EPSILON);
        assert!((seg.p1.x - 10.0 / 3.0).abs() < EPSILON);
        assert!((seg.p2.x - 20.0 / 3.0).abs() < EPSILON);
        assert!((seg.p3.x - 10.0).abs() < EPSILON);

        // Midpoint of a straight-line cubic should be at x=5
        let mid = seg.point_at(0.5);
        assert!((mid.x - 5.0).abs() < EPSILON);
        assert!((mid.y - 0.0).abs() < EPSILON);
    }

    // -- Test 4: segments() iterator -----------------------------------------

    #[test]
    fn segments_iterator() {
        let bp = make_triangle_bezier();
        let segs: Vec<_> = bp.segments().collect();
        assert_eq!(segs.len(), 3);

        // Each segment's p0 should match the corresponding knot point
        for (i, seg) in segs.iter().enumerate() {
            assert!(
                (seg.p0.x - bp.knot_point(i).x).abs() < EPSILON
                    && (seg.p0.y - bp.knot_point(i).y).abs() < EPSILON,
                "segment {i} p0 mismatch"
            );
        }
    }

    // -- Test 5: KnotPath::resolve() — 2-knot line, 1 segment ---------------

    #[test]
    fn resolve_two_knot_line() {
        let kp = super::super::KnotPath::from_knots(
            vec![
                Knot::new(Point::new(0.0, 0.0)),
                Knot::new(Point::new(10.0, 0.0)),
            ],
            false,
        );
        let bp = kp.resolve();
        assert_eq!(bp.num_segments(), 1);
        assert_eq!(bp.num_knots(), 2);
        assert!(!bp.is_cyclic());

        // Endpoints should match
        assert!((bp.knot_point(0).x - 0.0).abs() < EPSILON);
        assert!((bp.knot_point(1).x - 10.0).abs() < EPSILON);

        // Midpoint should be near (5, 0)
        let seg = bp.segment(0);
        let mid = seg.point_at(0.5);
        assert!((mid.x - 5.0).abs() < 0.5);
        assert!(mid.y.abs() < 0.5);
    }

    // -- Test 6: KnotPath::resolve() — cyclic triangle, 3 segments -----------

    #[test]
    fn resolve_cyclic_triangle() {
        let kp = super::super::KnotPath::from_knots(
            vec![
                Knot::new(Point::new(0.0, 0.0)),
                Knot::new(Point::new(10.0, 0.0)),
                Knot::new(Point::new(5.0, 10.0)),
            ],
            true,
        );
        let bp = kp.resolve();
        assert_eq!(bp.num_segments(), 3);
        assert_eq!(bp.num_knots(), 3);
        assert!(bp.is_cyclic());

        // Verify knot points match
        assert!((bp.knot_point(0).x - 0.0).abs() < EPSILON);
        assert!((bp.knot_point(0).y - 0.0).abs() < EPSILON);
        assert!((bp.knot_point(1).x - 10.0).abs() < EPSILON);
        assert!((bp.knot_point(2).x - 5.0).abs() < EPSILON);
        assert!((bp.knot_point(2).y - 10.0).abs() < EPSILON);
    }

    // -- Test 7: Roundtrip KnotPath → resolve → BezierPath → to_knot_path ---

    #[test]
    fn roundtrip_knot_bezier_knot() {
        // Open path
        let kp = super::super::KnotPath::from_knots(
            vec![
                Knot::new(Point::new(0.0, 0.0)),
                Knot::new(Point::new(5.0, 5.0)),
                Knot::new(Point::new(10.0, 0.0)),
            ],
            false,
        );
        let bp = kp.resolve();
        let kp2 = bp.to_knot_path();

        assert_eq!(kp2.knots.len(), 3);
        assert!(!kp2.is_cyclic);

        // Knot points should be preserved exactly
        assert!((kp2.knots[0].point.x - 0.0).abs() < EPSILON);
        assert!((kp2.knots[1].point.x - 5.0).abs() < EPSILON);
        assert!((kp2.knots[2].point.x - 10.0).abs() < EPSILON);

        // First knot left should be Open (open path endpoint)
        assert_eq!(kp2.knots[0].left, KnotDirection::Open);
        // Last knot right should be Open (open path endpoint)
        assert_eq!(kp2.knots[2].right, KnotDirection::Open);

        // Middle knot should have Explicit controls on both sides
        assert!(matches!(kp2.knots[1].left, KnotDirection::Explicit(_)));
        assert!(matches!(kp2.knots[1].right, KnotDirection::Explicit(_)));
    }

    #[test]
    fn roundtrip_cyclic() {
        let kp = super::super::KnotPath::from_knots(
            vec![
                Knot::new(Point::new(0.0, 0.0)),
                Knot::new(Point::new(10.0, 0.0)),
                Knot::new(Point::new(5.0, 10.0)),
            ],
            true,
        );
        let bp = kp.resolve();
        let kp2 = bp.to_knot_path();

        assert_eq!(kp2.knots.len(), 3);
        assert!(kp2.is_cyclic);

        // All knots should have Explicit controls on both sides (cyclic)
        for (i, knot) in kp2.knots.iter().enumerate() {
            assert!(
                matches!(knot.left, KnotDirection::Explicit(_)),
                "knot {i} left should be Explicit"
            );
            assert!(
                matches!(knot.right, KnotDirection::Explicit(_)),
                "knot {i} right should be Explicit"
            );
        }
    }

    // -- Default trait -------------------------------------------------------

    #[test]
    fn default_is_empty() {
        let bp = BezierPath::default();
        assert_eq!(bp.num_segments(), 0);
        assert_eq!(bp.num_knots(), 0);
    }

    // -- Cyclic segment wrapping ---------------------------------------------

    #[test]
    fn cyclic_last_segment_wraps() {
        let bp = make_triangle_bezier();
        // Segment 2 should connect knot 2 back to knot 0
        let seg = bp.segment(2);
        assert!((seg.p0.x - 5.0).abs() < EPSILON);
        assert!((seg.p0.y - 10.0).abs() < EPSILON);
        assert!((seg.p3.x - 0.0).abs() < EPSILON);
        assert!((seg.p3.y - 0.0).abs() < EPSILON);
    }
}
