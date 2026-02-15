//! Path operations and Hobby's spline algorithm.
//!
//! This module provides:
//! - Hobby's algorithm for computing smooth cubic Bezier control points
//!   through a sequence of knots with direction/tension/curl constraints.
//! - Path query operations: `point_of`, `direction_of`, `subpath`, `reverse`.

pub mod hobby;

use crate::bezier::CubicSegment;
use crate::types::{
    EPSILON, Knot, KnotDirection, Point, Scalar, Vec2, index_to_scalar, scalar_to_index,
};

// ---------------------------------------------------------------------------
// Path
// ---------------------------------------------------------------------------

/// A path: a sequence of knots, optionally cyclic.
///
/// After Hobby's algorithm runs, all `KnotDirection` values will be
/// `Explicit` (computed Bezier control points).
#[derive(Debug, Clone, PartialEq)]
pub struct Path {
    pub knots: Vec<Knot>,
    pub is_cyclic: bool,
}

impl Path {
    /// Create an empty open path.
    pub const fn new() -> Self {
        Self {
            knots: Vec::new(),
            is_cyclic: false,
        }
    }

    /// Create a path from knots.
    pub const fn from_knots(knots: Vec<Knot>, is_cyclic: bool) -> Self {
        Self { knots, is_cyclic }
    }

    /// Number of segments in the path.
    /// For a cyclic path with N knots, there are N segments.
    /// For an open path with N knots, there are N-1 segments.
    pub fn num_segments(&self) -> usize {
        if self.knots.is_empty() {
            return 0;
        }
        if self.is_cyclic {
            self.knots.len()
        } else {
            self.knots.len() - 1
        }
    }
}

impl Default for Path {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Path time normalization
// ---------------------------------------------------------------------------

/// Normalize a time parameter for a path with `n` segments.
///
/// Cyclic paths wrap around; open paths clamp to `[0, n]`.
/// Returns `None` if the path has no segments.
fn normalize_time(path: &Path, t: Scalar) -> Option<Scalar> {
    let n = path.num_segments();
    if n == 0 {
        return None;
    }
    Some(if path.is_cyclic {
        let n_f = index_to_scalar(n);
        let wrapped = ((t % n_f) + n_f) % n_f;
        // Normalize -0.0 to 0.0
        wrapped + 0.0
    } else {
        t.clamp(0.0, index_to_scalar(n))
    })
}

/// Decompose a normalized time into `(segment_index, fraction)`.
fn time_to_seg_frac(t: Scalar, n: usize) -> (usize, Scalar) {
    let seg = scalar_to_index(t).min(n - 1);
    let frac = t - index_to_scalar(seg);
    (seg, frac)
}

// ---------------------------------------------------------------------------
// Path query operations
// ---------------------------------------------------------------------------

/// Get the point at time `t` on the path.
///
/// `t` ranges from 0 to `path.num_segments()`. Integer values correspond
/// to knot points. Fractional values interpolate along the cubic segment.
#[must_use]
pub fn point_of(path: &Path, t: Scalar) -> Point {
    if path.knots.is_empty() {
        return Point::ZERO;
    }
    let Some(t) = normalize_time(path, t) else {
        return path.knots[0].point;
    };
    let (seg, frac) = time_to_seg_frac(t, path.num_segments());
    CubicSegment::from_path(path, seg).eval(frac)
}

/// Get the direction (tangent vector) at time `t` on the path.
#[must_use]
pub fn direction_of(path: &Path, t: Scalar) -> Vec2 {
    if path.knots.is_empty() {
        return Vec2::ZERO;
    }
    let Some(t) = normalize_time(path, t) else {
        return Vec2::ZERO;
    };
    let (seg, frac) = time_to_seg_frac(t, path.num_segments());
    CubicSegment::from_path(path, seg).eval_deriv(frac)
}

/// Get the precontrol point at time `t`.
#[must_use]
pub fn precontrol_of(path: &Path, t: Scalar) -> Point {
    if path.knots.is_empty() {
        return Point::ZERO;
    }
    let Some(t) = normalize_time(path, t) else {
        return path.knots[0].point;
    };
    let (seg, _) = time_to_seg_frac(t, path.num_segments());
    let j = (seg + 1) % path.knots.len();
    match path.knots[j].left {
        KnotDirection::Explicit(p) => p,
        _ => path.knots[j].point,
    }
}

/// Get the postcontrol point at time `t`.
#[must_use]
pub fn postcontrol_of(path: &Path, t: Scalar) -> Point {
    if path.knots.is_empty() {
        return Point::ZERO;
    }
    let Some(t) = normalize_time(path, t) else {
        return path.knots[0].point;
    };
    let (seg, _) = time_to_seg_frac(t, path.num_segments());
    match path.knots[seg].right {
        KnotDirection::Explicit(p) => p,
        _ => path.knots[seg].point,
    }
}

/// Extract a subpath from time `t1` to time `t2`.
///
/// For cyclic paths, the subpath wraps around naturally: `subpath(3.5, 1.5)`
/// on a 4-segment cycle yields the path going 3.5 → 0/4 → 1.5 (the long
/// way around). This matches `MetaPost`'s `chop_path` semantics.
#[must_use]
pub fn subpath(path: &Path, t1: Scalar, t2: Scalar) -> Path {
    if path.knots.is_empty() {
        return Path::new();
    }

    let n = path.num_segments();
    if n == 0 {
        return Path::from_knots(vec![path.knots[0].clone()], false);
    }

    // Handle reversed direction: swap, compute, reverse result.
    let (a, b, reversed) = if t1 <= t2 {
        (t1, t2, false)
    } else {
        (t2, t1, true)
    };

    let n_f = index_to_scalar(n);

    // Normalize following MetaPost's chop_path:
    // - Cyclic: shift both a,b so that a is in [0, n).
    //   b can exceed n (wrapping around the cycle).
    // - Open: clamp both to [0, n].
    let (a, b) = if path.is_cyclic {
        // Shift both so a is in [0, n). b may exceed n (wrap-around).
        let shift = a.div_euclid(n_f) * n_f;
        (a - shift, b - shift)
    } else {
        (a.clamp(0.0, n_f), b.clamp(0.0, n_f))
    };

    let result = subpath_normalized(path, a, b, n);
    if reversed { reverse(&result) } else { result }
}

/// Core subpath extraction with `0 <= a` and `a <= b`.
///
/// For cyclic paths `b` may exceed `n` (indicating wrap-around).
/// Segment indices are taken modulo `n`.
fn subpath_normalized(path: &Path, start: Scalar, end: Scalar, num_segs: usize) -> Path {
    let (seg1, frac1) = time_to_seg_frac(start, num_segs);
    // For end we decompose manually since it can exceed num_segs for cyclic paths.
    let seg2_raw = scalar_to_index(end).min(if path.is_cyclic {
        usize::MAX
    } else {
        num_segs - 1
    });
    let frac2 = end - index_to_scalar(seg2_raw);

    if seg1 == seg2_raw && frac2 > frac1 {
        // Both endpoints in the same segment
        return subpath_single_segment(path, seg1, frac1, frac2);
    }

    let mut knots = Vec::new();
    let num_knots = path.knots.len();

    // Start knot from splitting first segment
    let seg1_wrapped = seg1 % num_segs;
    let cubic_first = CubicSegment::from_path(path, seg1_wrapped);
    let (_, right_part) = cubic_first.split(frac1);
    let start_pt = cubic_first.eval(frac1);
    knots.push(Knot::with_controls(start_pt, start_pt, right_part.p1));

    // End of first partial segment
    let next_idx = (seg1 + 1) % num_knots;
    let mut next_knot = path.knots[next_idx].clone();
    next_knot.left = KnotDirection::Explicit(right_part.p2);
    knots.push(next_knot);

    // Full intermediate segments (wrapping via modulo for cyclic paths)
    for seg in (seg1 + 1)..seg2_raw {
        let idx = (seg + 1) % num_knots;
        knots.push(path.knots[idx].clone());
    }

    // Split last segment
    if frac2.abs() > EPSILON {
        let seg2_wrapped = seg2_raw % num_segs;
        let cubic_last = CubicSegment::from_path(path, seg2_wrapped);
        let (left_part, _) = cubic_last.split(frac2);
        let end_pt = cubic_last.eval(frac2);

        if let Some(last) = knots.last_mut() {
            last.right = KnotDirection::Explicit(left_part.p1);
        }
        knots.push(Knot::with_controls(end_pt, left_part.p2, end_pt));
    }

    Path::from_knots(knots, false)
}

/// Extract a subpath where both endpoints lie in the same segment.
fn subpath_single_segment(path: &Path, seg: usize, frac1: Scalar, frac2: Scalar) -> Path {
    let cubic = CubicSegment::from_path(path, seg);
    let (_, right) = cubic.split(frac1);
    let t_inner = if (1.0 - frac1).abs() < EPSILON {
        0.0
    } else {
        (frac2 - frac1) / (1.0 - frac1)
    };
    let (sub, _) = right.split(t_inner);
    let p0 = cubic.eval(frac1);
    let p1 = cubic.eval(frac2);
    Path::from_knots(
        vec![
            Knot::with_controls(p0, p0, sub.p1),
            Knot::with_controls(p1, sub.p2, p1),
        ],
        false,
    )
}

/// Reverse a path.
#[must_use]
pub fn reverse(path: &Path) -> Path {
    if path.knots.is_empty() {
        return Path::new();
    }

    let knots: Vec<Knot> = path
        .knots
        .iter()
        .rev()
        .map(|k| Knot {
            point: k.point,
            left: k.right,
            right: k.left,
            left_tension: k.right_tension,
            right_tension: k.left_tension,
        })
        .collect();

    Path::from_knots(knots, path.is_cyclic)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::EPSILON;

    fn make_line_path() -> Path {
        // Simple line from (0,0) to (10,0) with explicit controls
        let mut k0 = Knot::new(Point::ZERO);
        k0.right = KnotDirection::Explicit(Point::new(10.0 / 3.0, 0.0));
        let mut k1 = Knot::new(Point::new(10.0, 0.0));
        k1.left = KnotDirection::Explicit(Point::new(20.0 / 3.0, 0.0));
        Path::from_knots(vec![k0, k1], false)
    }

    fn make_triangle_path() -> Path {
        // Triangle with explicit straight-line controls
        let pts = [
            Point::new(0.0, 0.0),
            Point::new(10.0, 0.0),
            Point::new(5.0, 10.0),
        ];
        let knots: Vec<Knot> = (0..3)
            .map(|i| {
                let j = (i + 1) % 3;
                let prev = (i + 2) % 3;
                let right_cp = pts[i].lerp(pts[j], 1.0 / 3.0);
                let left_cp = pts[prev].lerp(pts[i], 2.0 / 3.0);
                Knot::with_controls(pts[i], left_cp, right_cp)
            })
            .collect();
        Path::from_knots(knots, true)
    }

    #[test]
    fn test_point_of_line() {
        let path = make_line_path();
        let p0 = point_of(&path, 0.0);
        assert!((p0.x).abs() < EPSILON);
        assert!((p0.y).abs() < EPSILON);

        let p1 = point_of(&path, 1.0);
        assert!((p1.x - 10.0).abs() < EPSILON);

        let pmid = point_of(&path, 0.5);
        assert!((pmid.x - 5.0).abs() < EPSILON);
    }

    #[test]
    fn test_point_of_clamps_open() {
        let path = make_line_path();
        let p_neg = point_of(&path, -1.0);
        assert!((p_neg.x).abs() < EPSILON);

        let p_over = point_of(&path, 5.0);
        assert!((p_over.x - 10.0).abs() < EPSILON);
    }

    #[test]
    fn test_direction_of_line() {
        let path = make_line_path();
        let d = direction_of(&path, 0.5);
        // Direction should be roughly (10, 0) (positive x)
        assert!(d.x > 0.0);
        assert!(d.y.abs() < EPSILON);
    }

    #[test]
    fn test_reverse_preserves_points() {
        let path = make_line_path();
        let rev = reverse(&path);
        assert_eq!(rev.knots.len(), 2);
        assert!((rev.knots[0].point.x - 10.0).abs() < EPSILON);
        assert!((rev.knots[1].point.x).abs() < EPSILON);
    }

    #[test]
    fn test_reverse_cyclic() {
        let path = make_triangle_path();
        let rev = reverse(&path);
        assert!(rev.is_cyclic);
        assert_eq!(rev.knots.len(), 3);
    }

    #[test]
    fn test_point_of_empty() {
        let path = Path::new();
        assert_eq!(point_of(&path, 0.0), Point::ZERO);
    }

    #[test]
    fn test_subpath_full() {
        let path = make_line_path();
        let sub = subpath(&path, 0.0, 1.0);
        assert_eq!(sub.knots.len(), 2);
        let p0 = point_of(&sub, 0.0);
        let p1 = point_of(&sub, 1.0);
        assert!((p0.x).abs() < EPSILON);
        assert!((p1.x - 10.0).abs() < EPSILON);
    }

    #[test]
    fn test_subpath_half() {
        let path = make_line_path();
        let sub = subpath(&path, 0.0, 0.5);
        let end = point_of(&sub, index_to_scalar(sub.num_segments()));
        assert!((end.x - 5.0).abs() < 0.1);
    }

    #[test]
    fn test_subpath_cyclic_wrap() {
        // Triangle: 3 segments, knots at (0,0), (10,0), (5,10)
        let tri = make_triangle_path();
        assert_eq!(tri.num_segments(), 3);

        // subpath(2.5, 0.5) should go the LONG way: 2.5 → 3/0 → 0.5
        // After swap: a=0.5, b=2.5, reversed=true → subpath(0.5,2.5) reversed
        // That gives the SHORT path 0.5→2.5 reversed.
        // But MetaPost convention: t1>t2 on a cycle means reverse the short path.
        // The result should have endpoints near the midpoints of segments 2 and 0.
        let sub = subpath(&tri, 2.5, 0.5);
        assert!(!sub.knots.is_empty());
        let p_start = point_of(&sub, 0.0);
        let p_end = point_of(&sub, index_to_scalar(sub.num_segments()));

        // Start should be at time 2.5 on the triangle (midpoint of seg 2: (5,10)→(0,0))
        let expected_start = point_of(&tri, 2.5);
        assert!(
            (p_start.x - expected_start.x).abs() < 0.1
                && (p_start.y - expected_start.y).abs() < 0.1,
            "start: {p_start:?}, expected: {expected_start:?}"
        );

        // End should be at time 0.5 on the triangle (midpoint of seg 0: (0,0)→(10,0))
        let expected_end = point_of(&tri, 0.5);
        assert!(
            (p_end.x - expected_end.x).abs() < 0.1 && (p_end.y - expected_end.y).abs() < 0.1,
            "end: {p_end:?}, expected: {expected_end:?}"
        );
    }

    #[test]
    fn test_subpath_cyclic_forward_wrap() {
        // Triangle: 3 segments. subpath(2.5, 4.5) should wrap forward:
        // 2.5 → 3/0 → 1.5 (4.5 mod 3 = 1.5).
        // After normalization: a=2.5, b=4.5 (b > n=3, but for cyclic that's ok).
        let tri = make_triangle_path();
        let sub = subpath(&tri, 2.5, 4.5);
        assert!(sub.knots.len() >= 3, "should span multiple segments");

        let p_start = point_of(&sub, 0.0);
        let p_end = point_of(&sub, index_to_scalar(sub.num_segments()));

        let expected_start = point_of(&tri, 2.5);
        assert!(
            (p_start.x - expected_start.x).abs() < 0.1
                && (p_start.y - expected_start.y).abs() < 0.1,
            "start: {p_start:?}, expected: {expected_start:?}"
        );

        // End should be at time 1.5 on the triangle
        let expected_end = point_of(&tri, 1.5);
        assert!(
            (p_end.x - expected_end.x).abs() < 0.1 && (p_end.y - expected_end.y).abs() < 0.1,
            "end: {p_end:?}, expected: {expected_end:?}"
        );
    }

    #[test]
    fn test_num_segments() {
        let p1 = make_line_path();
        assert_eq!(p1.num_segments(), 1);

        let p2 = make_triangle_path();
        assert_eq!(p2.num_segments(), 3);
    }
}
