//! Curve-curve intersection using bisection.
//!
//! Implements `MetaPost`'s `intersectiontimes` operator: given two paths,
//! find the (time1, time2) pair where they intersect.
//!
//! The algorithm recursively bisects both curves and checks bounding-box
//! overlap, stopping when the sub-curves are small enough.

use crate::bezier::CubicSegment;
use crate::path::BezierPath;
use crate::types::{Point, Scalar, index_to_scalar};

/// Result of an intersection search.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Intersection {
    /// Time parameter on the first path.
    pub t1: Scalar,
    /// Time parameter on the second path.
    pub t2: Scalar,
}

/// Find the first intersection between two [`BezierPath`]s.
///
/// Returns `None` if the paths don't intersect.
/// The returned times are in the range [0, `path.num_segments()`].
#[must_use]
pub fn intersection_times(path1: &BezierPath, path2: &BezierPath) -> Option<Intersection> {
    let n1 = path1.num_segments();
    let n2 = path2.num_segments();

    if n1 == 0 || n2 == 0 {
        return None;
    }

    let mut work = 0_u32;
    for i in 0..n1 {
        for j in 0..n2 {
            let seg1 = path1.segment(i);
            let seg2 = path2.segment(j);

            if let Some((t1, t2)) =
                intersect_cubics(&seg1, &seg2, Interval::UNIT, Interval::UNIT, 0, &mut work)
            {
                return Some(Intersection {
                    t1: index_to_scalar(i) + t1,
                    t2: index_to_scalar(j) + t2,
                });
            }
        }
    }

    None
}

/// Find all intersections between two [`BezierPath`]s.
#[must_use]
pub fn all_intersection_times(path1: &BezierPath, path2: &BezierPath) -> Vec<Intersection> {
    let n1 = path1.num_segments();
    let n2 = path2.num_segments();

    if n1 == 0 || n2 == 0 {
        return Vec::new();
    }

    let mut ctx = FindAllContext {
        seg1_offset: 0.0,
        seg2_offset: 0.0,
        results: Vec::new(),
        work: 0,
    };

    for i in 0..n1 {
        for j in 0..n2 {
            let seg1 = path1.segment(i);
            let seg2 = path2.segment(j);
            ctx.seg1_offset = index_to_scalar(i);
            ctx.seg2_offset = index_to_scalar(j);
            ctx.recurse(&seg1, &seg2, Interval::UNIT, Interval::UNIT, 0);
        }
    }

    ctx.results
}

// ---------------------------------------------------------------------------
// Bounding box overlap
// ---------------------------------------------------------------------------

/// Axis-aligned bounding box overlap test.
///
/// Returns `true` when the two AABBs share any area (inclusive of edges).
fn bbox_overlap(a: &(Point, Point), b: &(Point, Point)) -> bool {
    a.0.x <= b.1.x && a.1.x >= b.0.x && a.0.y <= b.1.y && a.1.y >= b.0.y
}

// ---------------------------------------------------------------------------
// Bisection intersection algorithm
// ---------------------------------------------------------------------------

/// Maximum recursion depth for bisection.
///
/// `MetaPost`'s `mp.web` uses ~17 levels. We use 20 for margin with `f64` precision.
const MAX_DEPTH: u32 = 20;

/// Maximum number of bbox overlap tests before giving up.
///
/// `MetaPost` uses `max_patience = 5000` backtracks. We count all overlap
/// tests as work units with a comparable budget.
const MAX_WORK: u32 = 5000;

/// Tolerance for convergence.
const INTERSECT_TOL: Scalar = 1e-6;

/// A time parameter interval `[lo, hi]` within a single cubic segment.
#[derive(Clone, Copy)]
struct Interval {
    lo: Scalar,
    hi: Scalar,
}

impl Interval {
    const UNIT: Self = Self { lo: 0.0, hi: 1.0 };

    const fn mid(self) -> Scalar {
        f64::midpoint(self.lo, self.hi)
    }

    const fn left(self) -> Self {
        Self {
            lo: self.lo,
            hi: self.mid(),
        }
    }

    const fn right(self) -> Self {
        Self {
            lo: self.mid(),
            hi: self.hi,
        }
    }
}

/// Find one intersection between two cubic segments by recursive bisection.
///
/// Both curves are split at their midpoints and the four sub-pairs are
/// tested. Sub-pairs whose bounding boxes don't overlap are pruned.
/// When a sub-curve's extent falls below the tolerance, the midpoint
/// of the parameter interval is reported as the intersection.
fn intersect_cubics(
    seg1: &CubicSegment,
    seg2: &CubicSegment,
    iv1: Interval,
    iv2: Interval,
    depth: u32,
    work: &mut u32,
) -> Option<(Scalar, Scalar)> {
    *work += 1;
    if *work > MAX_WORK {
        return Some((iv1.mid(), iv2.mid()));
    }

    let bb1 = seg1.bbox();
    let bb2 = seg2.bbox();

    if !bbox_overlap(&bb1, &bb2) {
        return None;
    }

    // Check convergence
    if seg1.extent() < INTERSECT_TOL && seg2.extent() < INTERSECT_TOL {
        return Some((iv1.mid(), iv2.mid()));
    }

    if depth >= MAX_DEPTH {
        return Some((iv1.mid(), iv2.mid()));
    }

    // Bisect both curves
    let (s1_left, s1_right) = seg1.split(0.5);
    let (s2_left, s2_right) = seg2.split(0.5);
    let d = depth + 1;

    // Try all 4 combinations (LL, LR, RL, RR), return the first hit
    intersect_cubics(&s1_left, &s2_left, iv1.left(), iv2.left(), d, work)
        .or_else(|| intersect_cubics(&s1_left, &s2_right, iv1.left(), iv2.right(), d, work))
        .or_else(|| intersect_cubics(&s1_right, &s2_left, iv1.right(), iv2.left(), d, work))
        .or_else(|| intersect_cubics(&s1_right, &s2_right, iv1.right(), iv2.right(), d, work))
}

/// Accumulator for `find_all` recursive intersection search.
struct FindAllContext {
    seg1_offset: Scalar,
    seg2_offset: Scalar,
    results: Vec<Intersection>,
    work: u32,
}

impl FindAllContext {
    fn recurse(
        &mut self,
        seg1: &CubicSegment,
        seg2: &CubicSegment,
        iv1: Interval,
        iv2: Interval,
        depth: u32,
    ) {
        self.work += 1;
        if self.work > MAX_WORK {
            return;
        }

        let bb1 = seg1.bbox();
        let bb2 = seg2.bbox();

        if !bbox_overlap(&bb1, &bb2) {
            return;
        }

        if (seg1.extent() < INTERSECT_TOL && seg2.extent() < INTERSECT_TOL) || depth >= MAX_DEPTH {
            let t1 = self.seg1_offset + iv1.mid();
            let t2 = self.seg2_offset + iv2.mid();

            // Avoid duplicate results
            let dominated = self.results.iter().any(|r| {
                (r.t1 - t1).abs() < INTERSECT_TOL * 10.0 && (r.t2 - t2).abs() < INTERSECT_TOL * 10.0
            });
            if !dominated {
                self.results.push(Intersection { t1, t2 });
            }
            return;
        }

        let (s1_left, s1_right) = seg1.split(0.5);
        let (s2_left, s2_right) = seg2.split(0.5);

        let d = depth + 1;
        for (s1, i1) in [(&s1_left, iv1.left()), (&s1_right, iv1.right())] {
            for (s2, i2) in [(&s2_left, iv2.left()), (&s2_right, iv2.right())] {
                self.recurse(s1, s2, i1, i2, d);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::path::bezier_path::SegmentControls;
    use crate::types::Scalar;

    /// Make a horizontal line `BezierPath` from (x0, y) to (x1, y).
    fn hline(x0: Scalar, x1: Scalar, y: Scalar) -> BezierPath {
        let dx = (x1 - x0) / 3.0;
        BezierPath::from_parts(
            vec![Point::new(x0, y), Point::new(x1, y)],
            vec![SegmentControls {
                post: Point::new(x0 + dx, y),
                pre: Point::new(x1 - dx, y),
            }],
            false,
        )
    }

    /// Make a vertical line `BezierPath` from (x, y0) to (x, y1).
    fn vline(x: Scalar, y0: Scalar, y1: Scalar) -> BezierPath {
        let dy = (y1 - y0) / 3.0;
        BezierPath::from_parts(
            vec![Point::new(x, y0), Point::new(x, y1)],
            vec![SegmentControls {
                post: Point::new(x, y0 + dy),
                pre: Point::new(x, y1 - dy),
            }],
            false,
        )
    }

    #[test]
    fn test_crossing_lines() {
        let h = hline(0.0, 10.0, 5.0);
        let v = vline(5.0, 0.0, 10.0);

        let result = intersection_times(&h, &v);
        assert!(result.is_some(), "expected intersection");
        let ix = result.unwrap();
        assert!((ix.t1 - 0.5).abs() < 0.01, "t1 = {}", ix.t1);
        assert!((ix.t2 - 0.5).abs() < 0.01, "t2 = {}", ix.t2);
    }

    #[test]
    fn test_no_intersection() {
        let h1 = hline(0.0, 10.0, 0.0);
        let h2 = hline(0.0, 10.0, 5.0);
        assert!(intersection_times(&h1, &h2).is_none());
    }

    #[test]
    fn test_empty_path() {
        let empty = BezierPath::new();
        let line = hline(0.0, 10.0, 5.0);
        assert!(intersection_times(&empty, &line).is_none());
        assert!(intersection_times(&line, &empty).is_none());
    }

    #[test]
    fn test_all_intersections() {
        let h = hline(0.0, 10.0, 5.0);
        let v = vline(5.0, 0.0, 10.0);
        let all = all_intersection_times(&h, &v);
        assert_eq!(all.len(), 1);
    }

    #[test]
    fn test_method_crossing_lines() {
        let h = hline(0.0, 10.0, 5.0);
        let v = vline(5.0, 0.0, 10.0);

        let result = h.intersection_times(&v);
        assert!(result.is_some(), "expected intersection via method");
        let ix = result.unwrap();
        assert!((ix.t1 - 0.5).abs() < 0.01, "t1 = {}", ix.t1);
        assert!((ix.t2 - 0.5).abs() < 0.01, "t2 = {}", ix.t2);
    }

    #[test]
    fn test_method_all_intersections() {
        let h = hline(0.0, 10.0, 5.0);
        let v = vline(5.0, 0.0, 10.0);
        let all = h.all_intersection_times(&v);
        assert_eq!(all.len(), 1);
    }

    #[test]
    fn test_bbox_overlap_yes() {
        let a = (Point::new(0.0, 0.0), Point::new(5.0, 5.0));
        let b = (Point::new(3.0, 3.0), Point::new(8.0, 8.0));
        assert!(bbox_overlap(&a, &b));
    }

    #[test]
    fn test_bbox_overlap_no() {
        let a = (Point::new(0.0, 0.0), Point::new(2.0, 2.0));
        let b = (Point::new(3.0, 3.0), Point::new(5.0, 5.0));
        assert!(!bbox_overlap(&a, &b));
    }
}
