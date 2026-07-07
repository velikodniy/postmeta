//! Subpath extraction and reversal for [`BezierPath`].

use super::numeric::time_to_seg_frac;
use super::{BezierPath, SegmentControls};
use crate::types::{EPSILON, Point, Scalar, index_to_scalar, scalar_to_index};

impl BezierPath {
    /// Extract a subpath from time `t1` to time `t2`.
    ///
    /// The first and last segments are split at their fractional times
    /// using de Casteljau subdivision; intermediate segments are copied
    /// wholesale. For cyclic paths, times may wrap around (e.g.,
    /// `subpath(3.5, 1.5)` on a 4-segment cycle follows the long way
    /// around). If `t1 > t2`, the result is computed forward and then
    /// reversed.
    #[must_use]
    pub fn subpath(&self, t1: Scalar, t2: Scalar) -> Self {
        if self.points.is_empty() {
            return Self::new();
        }

        let n = self.num_segments();
        if n == 0 {
            return Self::from_parts(vec![self.points[0]], vec![], false);
        }

        // Handle reversed direction: swap, compute, reverse result.
        let (a, b, reversed) = if t1 <= t2 {
            (t1, t2, false)
        } else {
            (t2, t1, true)
        };

        let n_f = index_to_scalar(n);

        // Normalize following MetaPost's chop_path.
        let (a, b) = if self.is_cyclic {
            let shift = a.div_euclid(n_f) * n_f;
            (a - shift, b - shift)
        } else {
            (a.clamp(0.0, n_f), b.clamp(0.0, n_f))
        };

        let result = self.subpath_normalized(a, b, n);
        if reversed { result.reverse() } else { result }
    }

    /// Core subpath extraction with `0 <= a` and `a <= b`.
    ///
    /// For cyclic paths `b` may exceed `n` (indicating wrap-around).
    fn subpath_normalized(&self, start: Scalar, end: Scalar, num_segs: usize) -> Self {
        let (seg1, frac1) = time_to_seg_frac(start, num_segs);
        // For end we decompose manually since it can exceed num_segs for cyclic paths.
        let seg2_raw = scalar_to_index(end).min(if self.is_cyclic {
            usize::MAX
        } else {
            num_segs - 1
        });
        let frac2 = end - index_to_scalar(seg2_raw);

        if seg1 == seg2_raw && frac2 > frac1 {
            // Both endpoints in the same segment
            return self.subpath_single_segment(seg1, frac1, frac2);
        }

        let mut points = Vec::new();
        let mut controls = Vec::new();

        // Start knot from splitting first segment
        let seg1_wrapped = seg1 % num_segs;
        let cubic_first = self.segment(seg1_wrapped);
        let (_, right_part) = cubic_first.split(frac1);
        let start_pt = cubic_first.point_at(frac1);
        points.push(start_pt);

        // End of first partial segment
        let next_knot_idx = (seg1 + 1) % self.points.len();
        controls.push(SegmentControls {
            post: right_part.p1,
            pre: right_part.p2,
        });
        points.push(self.points[next_knot_idx]);

        // Full intermediate segments (wrapping via modulo for cyclic paths)
        for seg in (seg1 + 1)..seg2_raw {
            let seg_idx = seg % num_segs;
            let next_idx = (seg + 1) % self.points.len();
            controls.push(self.controls[seg_idx]);
            points.push(self.points[next_idx]);
        }

        // Split last segment
        if frac2.abs() > EPSILON {
            let seg2_wrapped = seg2_raw % num_segs;
            let cubic_last = self.segment(seg2_wrapped);
            let (left_part, _) = cubic_last.split(frac2);
            let end_pt = cubic_last.point_at(frac2);

            controls.push(SegmentControls {
                post: left_part.p1,
                pre: left_part.p2,
            });
            points.push(end_pt);
        }

        Self::from_parts(points, controls, false)
    }

    /// Extract a subpath where both endpoints lie in the same segment.
    fn subpath_single_segment(&self, seg: usize, frac1: Scalar, frac2: Scalar) -> Self {
        let cubic = self.segment(seg);
        let (_, right) = cubic.split(frac1);
        let t_inner = if (1.0 - frac1).abs() < EPSILON {
            0.0
        } else {
            (frac2 - frac1) / (1.0 - frac1)
        };
        let (sub, _) = right.split(t_inner);
        let p0 = cubic.point_at(frac1);
        let p1 = cubic.point_at(frac2);
        Self::from_parts(
            vec![p0, p1],
            vec![SegmentControls {
                post: sub.p1,
                pre: sub.p2,
            }],
            false,
        )
    }

    /// Reverse the traversal direction of the path.
    ///
    /// Each segment's post/pre control handles are swapped. For cyclic
    /// paths, `MetaPost` convention keeps knot 0 as the start: the order
    /// `0,1,...,n-1` becomes `0,n-1,...,1`, preserving the cyclic start
    /// knot identity.
    #[must_use]
    pub fn reverse(&self) -> Self {
        if self.points.is_empty() {
            return Self::new();
        }

        if self.is_cyclic {
            // MetaPost-style reverse for cycles keeps the same start knot.
            // Original: 0 -> 1 -> 2 -> ... -> n-1 -> 0
            // Reversed: 0 -> n-1 -> n-2 -> ... -> 1 -> 0
            let n = self.points.len();
            let mut points = Vec::with_capacity(n);
            let mut controls = Vec::with_capacity(n);

            points.push(self.points[0]);
            for i in (1..n).rev() {
                points.push(self.points[i]);
            }

            // The original segment i connects point[i] -> point[(i+1)%n]
            // with controls[i] = { post, pre }.
            // In the reversed path, the segment from point[0] to point[n-1]
            // (which was the original segment n-1 -> 0) needs its controls
            // swapped.
            //
            // Reversed segment j goes from reversed_points[j] to
            // reversed_points[(j+1)%n].
            // reversed_points[0] = original[0]
            // reversed_points[1] = original[n-1]
            // reversed_points[2] = original[n-2]
            // ...
            // reversed_points[k] = original[(n-k) % n] for k >= 1, and
            //                       original[0] for k == 0.
            //
            // Reversed segment 0: original[0] -> original[n-1]
            //   This is the reverse of original segment (n-1): original[n-1] -> original[0]
            //   Original controls[n-1] = { post, pre }
            //   Reversed: { post: pre, pre: post } (swap)
            //
            // Reversed segment j (1 <= j < n): original[(n-j) % n] -> original[(n-j-1) % n]
            //   This is the reverse of original segment (n-j-1): original[n-j-1] -> original[n-j]
            //   Original controls[n-j-1] = { post, pre }
            //   Reversed: { post: pre, pre: post }

            // Segment 0: reverse of original segment (n-1)
            let orig_seg = n - 1;
            controls.push(SegmentControls {
                post: self.controls[orig_seg].pre,
                pre: self.controls[orig_seg].post,
            });

            // Segments 1..n-1: segment j reverses original segment (n-j-1)
            for j in 1..n {
                let orig_seg = n - j - 1;
                controls.push(SegmentControls {
                    post: self.controls[orig_seg].pre,
                    pre: self.controls[orig_seg].post,
                });
            }

            return Self::from_parts(points, controls, true);
        }

        // Open path: simply reverse everything, swapping post/pre.
        let points: Vec<Point> = self.points.iter().rev().copied().collect();
        let controls: Vec<SegmentControls> = self
            .controls
            .iter()
            .rev()
            .map(|c| SegmentControls {
                post: c.pre,
                pre: c.post,
            })
            .collect();

        Self::from_parts(points, controls, false)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_helpers;

    // -- subpath ------------------------------------------------------------

    #[test]
    fn subpath_full_line() {
        let bp = test_helpers::line();
        let sub = bp.subpath(0.0, 1.0);
        assert_eq!(sub.num_knots(), 2);
        assert_eq!(sub.num_segments(), 1);
        let p0 = sub.point_at(0.0);
        let p1 = sub.point_at(1.0);
        assert!(p0.x.abs() < EPSILON);
        assert!((p1.x - 10.0).abs() < EPSILON);
    }

    #[test]
    fn subpath_half_line() {
        let bp = test_helpers::line();
        let sub = bp.subpath(0.0, 0.5);
        let end = sub.point_at(index_to_scalar(sub.num_segments()));
        assert!((end.x - 5.0).abs() < 0.1);
    }

    #[test]
    fn subpath_empty() {
        let bp = BezierPath::new();
        let sub = bp.subpath(0.0, 1.0);
        assert_eq!(sub.num_segments(), 0);
    }

    #[test]
    fn subpath_cyclic_wrap() {
        let tri = test_helpers::triangle();
        let sub = tri.subpath(2.5, 0.5);
        assert!(!sub.knot_points().is_empty());

        let p_start = sub.point_at(0.0);
        let p_end = sub.point_at(index_to_scalar(sub.num_segments()));

        let expected_start = tri.point_at(2.5);
        assert!(
            (p_start.x - expected_start.x).abs() < 0.1
                && (p_start.y - expected_start.y).abs() < 0.1,
            "start: {p_start:?}, expected: {expected_start:?}"
        );

        let expected_end = tri.point_at(0.5);
        assert!(
            (p_end.x - expected_end.x).abs() < 0.1 && (p_end.y - expected_end.y).abs() < 0.1,
            "end: {p_end:?}, expected: {expected_end:?}"
        );
    }

    #[test]
    fn subpath_cyclic_forward_wrap() {
        let tri = test_helpers::triangle();
        let sub = tri.subpath(2.5, 4.5);
        assert!(sub.num_knots() >= 3, "should span multiple segments");

        let p_start = sub.point_at(0.0);
        let p_end = sub.point_at(index_to_scalar(sub.num_segments()));

        let expected_start = tri.point_at(2.5);
        assert!(
            (p_start.x - expected_start.x).abs() < 0.1
                && (p_start.y - expected_start.y).abs() < 0.1,
            "start: {p_start:?}, expected: {expected_start:?}"
        );

        let expected_end = tri.point_at(1.5);
        assert!(
            (p_end.x - expected_end.x).abs() < 0.1 && (p_end.y - expected_end.y).abs() < 0.1,
            "end: {p_end:?}, expected: {expected_end:?}"
        );
    }

    // -- reverse ------------------------------------------------------------

    #[test]
    fn reverse_open_preserves_points() {
        let bp = test_helpers::line();
        let rev = bp.reverse();
        assert_eq!(rev.num_knots(), 2);
        assert!((rev.knot_point(0).x - 10.0).abs() < EPSILON);
        assert!(rev.knot_point(1).x.abs() < EPSILON);
    }

    #[test]
    fn reverse_open_swaps_controls() {
        let bp = test_helpers::line();
        let rev = bp.reverse();
        // The original controls were post=10/3, pre=20/3
        // After reverse, the single segment goes 10 -> 0
        // with post=20/3 (was pre), pre=10/3 (was post)
        let ctrl = rev.segment_controls(0);
        assert!((ctrl.post.x - 20.0 / 3.0).abs() < EPSILON);
        assert!((ctrl.pre.x - 10.0 / 3.0).abs() < EPSILON);
    }

    #[test]
    fn reverse_cyclic_keeps_start() {
        let bp = test_helpers::triangle();
        let rev = bp.reverse();
        assert!(rev.is_cyclic());
        assert_eq!(rev.num_knots(), 3);
        assert_eq!(rev.knot_point(0), bp.knot_point(0));
    }

    #[test]
    fn reverse_cyclic_time_mapping() {
        let bp = test_helpers::triangle();
        let rev = bp.reverse();
        let n = index_to_scalar(bp.num_segments());

        for &t in &[0.0, 0.25, 0.9, 1.5, 2.2] {
            let p_rev = rev.point_at(t);
            let mapped = ((n - t) % n + n) % n;
            let p_orig = bp.point_at(mapped);
            assert!(
                (p_rev.x - p_orig.x).abs() < 1e-6 && (p_rev.y - p_orig.y).abs() < 1e-6,
                "t={t}: rev={p_rev:?}, orig={p_orig:?}, mapped={mapped}"
            );
        }
    }

    #[test]
    fn reverse_empty() {
        let bp = BezierPath::new();
        let rev = bp.reverse();
        assert_eq!(rev.num_segments(), 0);
        assert_eq!(rev.num_knots(), 0);
    }

    #[test]
    fn reverse_involution() {
        // Reversing twice should give back the original
        let bp = test_helpers::line();
        let rev2 = bp.reverse().reverse();
        assert_eq!(rev2.num_knots(), bp.num_knots());
        for i in 0..bp.num_knots() {
            assert!(
                (rev2.knot_point(i).x - bp.knot_point(i).x).abs() < EPSILON
                    && (rev2.knot_point(i).y - bp.knot_point(i).y).abs() < EPSILON,
                "knot {i}: rev2={:?}, orig={:?}",
                rev2.knot_point(i),
                bp.knot_point(i)
            );
        }
    }

    #[test]
    fn reverse_cyclic_involution() {
        let bp = test_helpers::triangle();
        let rev2 = bp.reverse().reverse();
        for i in 0..bp.num_knots() {
            assert!(
                (rev2.knot_point(i).x - bp.knot_point(i).x).abs() < EPSILON
                    && (rev2.knot_point(i).y - bp.knot_point(i).y).abs() < EPSILON,
                "knot {i}: rev2={:?}, orig={:?}",
                rev2.knot_point(i),
                bp.knot_point(i)
            );
        }
        // Also check controls
        for i in 0..bp.num_segments() {
            let orig = bp.segment_controls(i);
            let rev2c = rev2.segment_controls(i);
            assert!(
                (rev2c.post.x - orig.post.x).abs() < EPSILON
                    && (rev2c.post.y - orig.post.y).abs() < EPSILON
                    && (rev2c.pre.x - orig.pre.x).abs() < EPSILON
                    && (rev2c.pre.y - orig.pre.y).abs() < EPSILON,
                "segment {i}: rev2={rev2c:?}, orig={orig:?}"
            );
        }
    }

    #[test]
    fn subpath_cyclic_negative_time_wraps() {
        // subpath(-0.5, 0.5) on a cyclic path must produce the same points
        // as the equivalent wrapped range: point_at(t) for t in [-0.5, 0.5]
        // equals point_at(t + n) for the cyclic path.
        let path = crate::test_helpers::square();
        let sub = path.subpath(-0.5, 0.5);
        // The range crosses one knot boundary: two partial segments.
        assert_eq!(sub.num_segments(), 2);
        let start = sub.point_at(0.0);
        let expected_start = path.point_at(-0.5);
        assert!(
            (start.x - expected_start.x).abs() < 1e-9 && (start.y - expected_start.y).abs() < 1e-9,
            "start {start:?} != {expected_start:?}"
        );
        let end = sub.point_at(2.0);
        let expected_end = path.point_at(0.5);
        assert!(
            (end.x - expected_end.x).abs() < 1e-9 && (end.y - expected_end.y).abs() < 1e-9,
            "end {end:?} != {expected_end:?}"
        );
    }
}
