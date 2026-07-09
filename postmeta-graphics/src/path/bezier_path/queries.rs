//! Path query operations on [`BezierPath`]: point/direction evaluation, arc length, turning number, and control-point access at a time

use super::BezierPath;
use super::numeric::{bernstein_eval, bisect_arc_length, find_bernstein_roots, time_to_seg_frac};
use crate::types::{EPSILON, Point, Scalar, Vec2, index_to_scalar};

/// Number of subdivision steps per cubic segment for turning number
const TURNING_STEPS: usize = 64;
const TURNING_STEPS_F: Scalar = 64.0;

impl BezierPath {
    /// Get the point at time `t` on the path
    ///
    /// `t` ranges from 0 to `num_segments()`.
    /// Integer values correspond to knot points; fractional values interpolate along the cubic segment.
    #[must_use]
    pub fn point_at(&self, t: Scalar) -> Point {
        if self.points.is_empty() {
            return Point::ZERO;
        }
        let Some(t) = self.normalize_time(t) else {
            return self.points[0];
        };
        let (seg, frac) = time_to_seg_frac(t, self.num_segments());
        self.segment(seg).point_at(frac)
    }

    /// Get the tangent direction at time `t` on the path
    #[must_use]
    pub fn direction_at(&self, t: Scalar) -> Vec2 {
        if self.points.is_empty() {
            return Vec2::ZERO;
        }
        let Some(t) = self.normalize_time(t) else {
            return Vec2::ZERO;
        };
        let (seg, frac) = time_to_seg_frac(t, self.num_segments());
        self.segment(seg).direction_at(frac)
    }

    /// Find the first time at which the tangent matches a given direction
    ///
    /// The tangent derivative of each cubic segment is a degree-2 Bernstein polynomial.
    /// Rotating so that `dir` maps to the positive x-axis reduces the problem to finding roots of the y-component, solved via the quadratic formula.
    /// Returns `None` if no match exists.
    #[must_use]
    pub fn direction_time(&self, dir: Vec2) -> Option<Scalar> {
        if dir.x.abs() < EPSILON && dir.y.abs() < EPSILON {
            return Some(0.0); // zero direction matches immediately
        }

        let n = self.num_segments();
        if n == 0 {
            return None;
        }

        // Normalize direction for rotation
        let len = dir.x.hypot(dir.y);
        let (dx, dy) = (dir.x / len, dir.y / len);

        for i in 0..n {
            let seg = self.segment(i);

            // Derivative control points (B'(t)/3 = B(d1,d2,d3;t))
            let d1 = Vec2::new(seg.p1.x - seg.p0.x, seg.p1.y - seg.p0.y);
            let d2 = Vec2::new(seg.p2.x - seg.p1.x, seg.p2.y - seg.p1.y);
            let d3 = Vec2::new(seg.p3.x - seg.p2.x, seg.p3.y - seg.p2.y);

            // Rotate so that (dx,dy) -> (1,0): multiply by conjugate rotation
            let ry1 = d1.y.mul_add(dx, -d1.x * dy);
            let ry2 = d2.y.mul_add(dx, -d2.x * dy);
            let ry3 = d3.y.mul_add(dx, -d3.x * dy);

            let rx1 = d1.x.mul_add(dx, d1.y * dy);
            let rx2 = d2.x.mul_add(dx, d2.y * dy);
            let rx3 = d3.x.mul_add(dx, d3.y * dy);

            // t=0: tangent is zero or already matches direction
            if ry1.abs() < EPSILON && rx1 >= -EPSILON {
                return Some(index_to_scalar(i));
            }

            // Find roots of B(ry1, ry2, ry3; t) = 0 in [0,1]
            for t in find_bernstein_roots(ry1, ry2, ry3) {
                if (0.0..=1.0).contains(&t) {
                    let rx = bernstein_eval(rx1, rx2, rx3, t);
                    if rx >= -EPSILON {
                        return Some(index_to_scalar(i) + t);
                    }
                }
            }
        }

        None
    }

    /// Total arc length of the path
    #[must_use]
    pub fn arc_length(&self) -> Scalar {
        self.segments().map(|s| s.arc_length()).sum()
    }

    /// Find the time parameter at which the cumulative arc length from the start of the path equals `target`
    ///
    /// Returns a `MetaPost`-style time (integer part = segment index, fractional part = position within that segment).
    /// If `target` exceeds the total arc length, returns `num_segments()`; if `target <= 0`, returns 0.
    #[must_use]
    pub fn arc_time(&self, target: Scalar) -> Scalar {
        let n = self.num_segments();
        if n == 0 || target <= 0.0 {
            return 0.0;
        }

        let mut remaining = target;

        for i in 0..n {
            let seg = self.segment(i);
            let seg_len = seg.arc_length();

            if remaining <= seg_len {
                let local_t = bisect_arc_length(&seg, remaining);
                return index_to_scalar(i) + local_t;
            }

            remaining -= seg_len;
        }

        index_to_scalar(n) // target exceeds total arc length
    }

    /// Compute the turning number (winding count) of a cyclic path
    ///
    /// Accumulates the total signed angular change of the tangent vector around the curve and divides by 2*pi.
    /// Returns +1 for counterclockwise simple closed curves, -1 for clockwise, and 0 for non-cyclic or degenerate paths.
    #[must_use]
    pub fn turning_number(&self) -> Scalar {
        if !self.is_cyclic || self.points.len() < 2 {
            return 0.0;
        }

        let n = self.num_segments();
        if n == 0 {
            return 0.0;
        }

        let mut total_angle: Scalar = 0.0;

        let first_seg = self.segment(0);
        let mut prev_dir = first_seg.direction_at(0.0);

        // Degenerate zero direction: try a small offset
        if prev_dir.x.abs() < EPSILON && prev_dir.y.abs() < EPSILON {
            prev_dir = first_seg.direction_at(1e-6);
        }

        for i in 0..n {
            let seg = self.segment(i);

            for step in 1..=TURNING_STEPS {
                #[allow(clippy::cast_precision_loss)]
                let t = step as Scalar / TURNING_STEPS_F;
                let cur_dir = seg.direction_at(t);

                if cur_dir.x.abs() < EPSILON && cur_dir.y.abs() < EPSILON {
                    continue;
                }

                total_angle += prev_dir.cross(cur_dir).atan2(prev_dir.dot(cur_dir));

                prev_dir = cur_dir;
            }
        }

        (total_angle / (2.0 * std::f64::consts::PI)).round()
    }

    /// Get the precontrol (incoming control) point at time `t`
    ///
    /// For integer times, returns the precontrol of that knot.
    /// For fractional times, splits the segment and returns the inserted precontrol.
    #[must_use]
    pub fn precontrol_at(&self, t: Scalar) -> Point {
        if self.points.is_empty() {
            return Point::ZERO;
        }
        let Some(t) = self.normalize_time(t) else {
            return self.points[0];
        };
        let n = self.num_segments();
        let (seg, frac) = time_to_seg_frac(t, n);

        if frac.abs() < EPSILON {
            // At a knot point: return its precontrol
            if !self.is_cyclic && seg == 0 {
                return self.points[0];
            }
            // The precontrol of knot `seg` is the `pre` of the preceding segment
            let prev_seg = if seg == 0 { n - 1 } else { seg - 1 };
            self.controls[prev_seg].pre
        } else {
            let cubic = self.segment(seg % n);
            let (left_part, _) = cubic.split(frac);
            left_part.p2
        }
    }

    /// Get the postcontrol (outgoing control) point at time `t`
    ///
    /// For integer times, returns the postcontrol of that knot.
    /// For fractional times, splits the segment and returns the inserted postcontrol.
    #[must_use]
    pub fn postcontrol_at(&self, t: Scalar) -> Point {
        if self.points.is_empty() {
            return Point::ZERO;
        }
        let Some(t) = self.normalize_time(t) else {
            return self.points[0];
        };
        let n = self.num_segments();
        let (seg, frac) = time_to_seg_frac(t, n);

        if frac.abs() < EPSILON {
            // At a knot point: return its postcontrol
            let knot_idx = seg % self.points.len();
            if !self.is_cyclic && knot_idx == self.points.len() - 1 {
                return self.points[knot_idx];
            }
            self.controls[knot_idx].post
        } else {
            let cubic = self.segment(seg % n);
            let (_, right_part) = cubic.split(frac);
            right_part.p1
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::super::SegmentControls;
    use super::*;
    use crate::test_helpers;

    /// Build a cyclic square `BezierPath` with straight-line controls
    fn make_square_bezier() -> BezierPath {
        let pts = [
            Point::new(0.0, 0.0),
            Point::new(1.0, 0.0),
            Point::new(1.0, 1.0),
            Point::new(0.0, 1.0),
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
        BezierPath::from_parts(pts.to_vec(), controls, true)
    }

    // -- point_at -----------------------------------------------------------

    #[test]
    fn point_at_line_endpoints() {
        let bp = test_helpers::line();
        let p0 = bp.point_at(0.0);
        assert!(p0.x.abs() < EPSILON);
        assert!(p0.y.abs() < EPSILON);

        let p1 = bp.point_at(1.0);
        assert!((p1.x - 10.0).abs() < EPSILON);
    }

    #[test]
    fn point_at_line_midpoint() {
        let bp = test_helpers::line();
        let pmid = bp.point_at(0.5);
        assert!((pmid.x - 5.0).abs() < EPSILON);
    }

    #[test]
    fn point_at_clamps_open() {
        let bp = test_helpers::line();
        let p_neg = bp.point_at(-1.0);
        assert!(p_neg.x.abs() < EPSILON);

        let p_over = bp.point_at(5.0);
        assert!((p_over.x - 10.0).abs() < EPSILON);
    }

    #[test]
    fn point_at_empty() {
        let bp = BezierPath::new();
        assert_eq!(bp.point_at(0.0), Point::ZERO);
    }

    // -- direction_at -------------------------------------------------------

    #[test]
    fn direction_at_line() {
        let bp = test_helpers::line();
        let d = bp.direction_at(0.5);
        assert!(d.x > 0.0);
        assert!(d.y.abs() < EPSILON);
    }

    #[test]
    fn direction_at_empty() {
        let bp = BezierPath::new();
        assert_eq!(bp.direction_at(0.0), Vec2::ZERO);
    }

    // -- direction_time -----------------------------------------------------

    #[test]
    fn direction_time_east_on_line() {
        let bp = test_helpers::line();
        let t = bp.direction_time(Vec2::new(1.0, 0.0));
        let t = t.expect("east direction should be found");
        assert!((t - 0.0).abs() < 0.01, "expected ~0, got {t}");
    }

    #[test]
    fn direction_time_west_not_found() {
        let bp = test_helpers::line();
        assert!(
            bp.direction_time(Vec2::new(-1.0, 0.0)).is_none(),
            "west should not be found on an eastward line"
        );
    }

    #[test]
    fn direction_time_zero_dir() {
        let bp = test_helpers::line();
        let t = bp
            .direction_time(Vec2::new(0.0, 0.0))
            .expect("zero direction always matches");
        assert!((t - 0.0).abs() < EPSILON);
    }

    #[test]
    fn direction_time_on_triangle() {
        let bp = test_helpers::triangle();
        let t = bp
            .direction_time(Vec2::new(1.0, 0.0))
            .expect("east direction should be found");
        assert!(t >= 0.0 && t < 0.5, "expected near 0, got {t}");
    }

    // -- arc_length ---------------------------------------------------------

    #[test]
    fn arc_length_line() {
        let bp = test_helpers::line();
        let len = bp.arc_length();
        assert!((len - 10.0).abs() < 0.01, "expected ~10, got {len}");
    }

    #[test]
    fn arc_length_empty() {
        let bp = BezierPath::new();
        assert_eq!(bp.arc_length(), 0.0);
    }

    // -- arc_time -----------------------------------------------------------

    #[test]
    fn arc_time_zero() {
        let bp = test_helpers::line();
        assert!((bp.arc_time(0.0)).abs() < EPSILON);
    }

    #[test]
    fn arc_time_full() {
        let bp = test_helpers::line();
        let total = bp.arc_length();
        let t = bp.arc_time(total + 1.0);
        assert!(
            (t - 1.0).abs() < EPSILON,
            "expected num_segments=1, got {t}"
        );
    }

    #[test]
    fn arc_time_half_line() {
        let bp = test_helpers::line();
        let t = bp.arc_time(5.0);
        // For a straight line of length 10, arc_time(5) should be ~0.5
        assert!((t - 0.5).abs() < 0.01, "expected ~0.5, got {t}");
    }

    // -- turning_number -----------------------------------------------------

    #[test]
    fn turning_number_ccw_triangle() {
        let bp = test_helpers::triangle();
        assert_eq!(bp.turning_number(), 1.0);
    }

    #[test]
    fn turning_number_cw_triangle() {
        let bp = test_helpers::triangle();
        let rev = bp.reverse();
        assert_eq!(rev.turning_number(), -1.0);
    }

    #[test]
    fn turning_number_open_path() {
        let bp = test_helpers::line();
        assert_eq!(bp.turning_number(), 0.0);
    }

    #[test]
    fn turning_number_ccw_square() {
        let bp = make_square_bezier();
        assert_eq!(bp.turning_number(), 1.0);
    }

    #[test]
    fn turning_number_single_point() {
        let bp = BezierPath::from_parts(vec![Point::new(5.0, 5.0)], vec![], false);
        assert_eq!(bp.turning_number(), 0.0);
    }

    // -- precontrol_at / postcontrol_at -------------------------------------

    #[test]
    fn precontrol_at_open_endpoints() {
        let bp = test_helpers::line();

        // t=0 on an open path: the precontrol is the point itself
        let pre0 = bp.precontrol_at(0.0);
        assert!((pre0.x - 0.0).abs() < EPSILON, "expected 0, got {}", pre0.x);

        // t=1: the pre control of segment 0
        let pre1 = bp.precontrol_at(1.0);
        assert!(
            (pre1.x - 20.0 / 3.0).abs() < EPSILON,
            "expected 20/3, got {}",
            pre1.x
        );
    }

    #[test]
    fn postcontrol_at_open_endpoints() {
        let bp = test_helpers::line();

        // t=0: the post control of segment 0
        let post0 = bp.postcontrol_at(0.0);
        assert!(
            (post0.x - 10.0 / 3.0).abs() < EPSILON,
            "expected 10/3, got {}",
            post0.x
        );

        // t=1 (last knot, open path): the point itself
        let post1 = bp.postcontrol_at(1.0);
        assert!(
            (post1.x - 10.0).abs() < EPSILON,
            "expected 10, got {}",
            post1.x
        );
    }

    #[test]
    fn precontrol_at_fractional_time() {
        let bp = test_helpers::line();
        // Fractional time: precontrol comes from splitting the segment; for a
        // straight line the split at 0.5 gives a precontrol near the midpoint
        let pre_half = bp.precontrol_at(0.5);
        assert!(pre_half.x > 0.0 && pre_half.x < 10.0);
    }

    #[test]
    fn postcontrol_at_fractional_time() {
        let bp = test_helpers::line();
        let post_half = bp.postcontrol_at(0.5);
        assert!(post_half.x > 0.0 && post_half.x < 10.0);
    }

    #[test]
    fn precontrol_at_cyclic_knot() {
        let bp = test_helpers::triangle();
        // t=0 on a cyclic path uses the pre of segment n-1
        let pre0 = bp.precontrol_at(0.0);
        let expected = bp.segment_controls(2).pre;
        assert!(
            (pre0.x - expected.x).abs() < EPSILON && (pre0.y - expected.y).abs() < EPSILON,
            "pre0={pre0:?}, expected={expected:?}"
        );
    }

    #[test]
    fn precontrol_at_empty() {
        let bp = BezierPath::new();
        assert_eq!(bp.precontrol_at(0.0), Point::ZERO);
    }

    #[test]
    fn postcontrol_at_empty() {
        let bp = BezierPath::new();
        assert_eq!(bp.postcontrol_at(0.0), Point::ZERO);
    }
}
