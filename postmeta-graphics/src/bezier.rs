//! Cubic Bezier segment operations.
//!
//! This module provides the shared `CubicSegment` type and operations used
//! across the crate: de Casteljau evaluation, splitting, derivative
//! computation, and bounding boxes.

use crate::types::{KnotDirection, Path, Point, Scalar, Vec2};

/// Four control points of a cubic Bezier segment.
#[derive(Debug, Clone, Copy)]
pub struct CubicSegment {
    pub p0: Point,
    pub p1: Point,
    pub p2: Point,
    pub p3: Point,
}

impl CubicSegment {
    /// Create a new cubic segment from four control points.
    #[must_use]
    pub const fn new(p0: Point, p1: Point, p2: Point, p3: Point) -> Self {
        Self { p0, p1, p2, p3 }
    }

    /// Extract segment `i` from a resolved path.
    ///
    /// For a cyclic path with N knots, valid segment indices are `0..N`.
    /// For an open path with N knots, valid segment indices are `0..N-1`.
    ///
    /// Non-explicit knot directions fall back to the on-curve point.
    ///
    /// # Panics
    ///
    /// Panics if `i >= path.num_segments()` or the path is empty.
    #[must_use]
    pub fn from_path(path: &Path, i: usize) -> Self {
        debug_assert!(
            !path.knots.is_empty() && i < path.num_segments(),
            "segment index {i} out of range for path with {} segments",
            path.num_segments()
        );
        let j = (i + 1) % path.knots.len();
        let k0 = &path.knots[i];
        let k1 = &path.knots[j];

        let p1 = match k0.right {
            KnotDirection::Explicit(p) => p,
            _ => k0.point,
        };
        let p2 = match k1.left {
            KnotDirection::Explicit(p) => p,
            _ => k1.point,
        };

        Self {
            p0: k0.point,
            p1,
            p2,
            p3: k1.point,
        }
    }

    /// Evaluate the point at parameter `t` in [0, 1].
    #[expect(
        clippy::many_single_char_names,
        reason = "standard Bezier math variable names (a, b, c, d, s, t)"
    )]
    #[must_use]
    pub fn eval(&self, t: Scalar) -> Point {
        let s = 1.0 - t;
        let a = s * s * s;
        let b = 3.0 * s * s * t;
        let c = 3.0 * s * t * t;
        let d = t * t * t;
        Point::new(
            d.mul_add(
                self.p3.x,
                a.mul_add(self.p0.x, b.mul_add(self.p1.x, c * self.p2.x)),
            ),
            d.mul_add(
                self.p3.y,
                a.mul_add(self.p0.y, b.mul_add(self.p1.y, c * self.p2.y)),
            ),
        )
    }

    /// Evaluate the derivative (tangent vector) at parameter `t` in [0, 1].
    #[expect(
        clippy::many_single_char_names,
        reason = "standard Bezier math variable names (a, b, c, s, t)"
    )]
    #[must_use]
    pub fn eval_deriv(&self, t: Scalar) -> Vec2 {
        let s = 1.0 - t;
        let a = 3.0 * s * s;
        let b = 6.0 * s * t;
        let c = 3.0 * t * t;
        Vec2::new(
            a.mul_add(
                self.p1.x - self.p0.x,
                b.mul_add(self.p2.x - self.p1.x, c * (self.p3.x - self.p2.x)),
            ),
            a.mul_add(
                self.p1.y - self.p0.y,
                b.mul_add(self.p2.y - self.p1.y, c * (self.p3.y - self.p2.y)),
            ),
        )
    }

    /// Split at parameter `t` using de Casteljau's algorithm.
    ///
    /// Returns `(left_half, right_half)`.
    #[must_use]
    pub fn split(&self, t: Scalar) -> (Self, Self) {
        let ab = self.p0.lerp(self.p1, t);
        let bc = self.p1.lerp(self.p2, t);
        let cd = self.p2.lerp(self.p3, t);
        let abc = ab.lerp(bc, t);
        let bcd = bc.lerp(cd, t);
        let abcd = abc.lerp(bcd, t);

        (
            Self {
                p0: self.p0,
                p1: ab,
                p2: abc,
                p3: abcd,
            },
            Self {
                p0: abcd,
                p1: bcd,
                p2: cd,
                p3: self.p3,
            },
        )
    }

    /// Axis-aligned bounding box of the control-point hull: `(min, max)`.
    #[must_use]
    pub const fn bbox(&self) -> (Point, Point) {
        let min_x = self.p0.x.min(self.p1.x).min(self.p2.x).min(self.p3.x);
        let min_y = self.p0.y.min(self.p1.y).min(self.p2.y).min(self.p3.y);
        let max_x = self.p0.x.max(self.p1.x).max(self.p2.x).max(self.p3.x);
        let max_y = self.p0.y.max(self.p1.y).max(self.p2.y).max(self.p3.y);
        (Point::new(min_x, min_y), Point::new(max_x, max_y))
    }

    /// Maximum extent (diagonal of bounding box).
    #[must_use]
    pub fn extent(&self) -> Scalar {
        let (min, max) = self.bbox();
        (max.x - min.x).hypot(max.y - min.y)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::EPSILON;

    #[test]
    fn eval_endpoints() {
        let seg = CubicSegment::new(
            Point::new(0.0, 0.0),
            Point::new(1.0, 2.0),
            Point::new(3.0, 2.0),
            Point::new(4.0, 0.0),
        );
        let p0 = seg.eval(0.0);
        assert!((p0.x).abs() < EPSILON);
        assert!((p0.y).abs() < EPSILON);
        let p1 = seg.eval(1.0);
        assert!((p1.x - 4.0).abs() < EPSILON);
        assert!((p1.y).abs() < EPSILON);
    }

    #[test]
    fn eval_midpoint_of_line() {
        // Straight line: all control points collinear
        let seg = CubicSegment::new(
            Point::new(0.0, 0.0),
            Point::new(10.0 / 3.0, 0.0),
            Point::new(20.0 / 3.0, 0.0),
            Point::new(10.0, 0.0),
        );
        let mid = seg.eval(0.5);
        assert!((mid.x - 5.0).abs() < EPSILON);
        assert!((mid.y).abs() < EPSILON);
    }

    #[test]
    fn split_preserves_endpoints() {
        let seg = CubicSegment::new(
            Point::new(0.0, 0.0),
            Point::new(1.0, 2.0),
            Point::new(3.0, 2.0),
            Point::new(4.0, 0.0),
        );
        let (left, right) = seg.split(0.5);
        // Left starts at original start
        assert!((left.p0.x).abs() < EPSILON);
        // Right ends at original end
        assert!((right.p3.x - 4.0).abs() < EPSILON);
        // They meet at the midpoint
        assert!((left.p3.x - right.p0.x).abs() < EPSILON);
        assert!((left.p3.y - right.p0.y).abs() < EPSILON);
    }

    #[test]
    fn deriv_direction_of_line() {
        let seg = CubicSegment::new(
            Point::new(0.0, 0.0),
            Point::new(10.0 / 3.0, 0.0),
            Point::new(20.0 / 3.0, 0.0),
            Point::new(10.0, 0.0),
        );
        let d = seg.eval_deriv(0.5);
        assert!(d.x > 0.0);
        assert!(d.y.abs() < EPSILON);
    }

    #[test]
    fn bbox_contains_endpoints() {
        let seg = CubicSegment::new(
            Point::new(0.0, 0.0),
            Point::new(1.0, 5.0),
            Point::new(3.0, -1.0),
            Point::new(4.0, 0.0),
        );
        let (min, max) = seg.bbox();
        assert!(min.x <= 0.0 && max.x >= 4.0);
        assert!(min.y <= -1.0 && max.y >= 5.0);
    }

    #[test]
    fn point_lerp_basics() {
        let a = Point::new(0.0, 0.0);
        let b = Point::new(10.0, 20.0);
        let mid = a.lerp(b, 0.5);
        assert!((mid.x - 5.0).abs() < EPSILON);
        assert!((mid.y - 10.0).abs() < EPSILON);
        assert!((a.lerp(b, 0.0).x).abs() < EPSILON);
        assert!((a.lerp(b, 1.0).x - 10.0).abs() < EPSILON);
    }
}
