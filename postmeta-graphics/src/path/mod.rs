//! Path operations and Hobby's spline algorithm.
//!
//! This module provides:
//! - Hobby's algorithm for computing smooth cubic Bezier control points
//!   through a sequence of knots with direction/tension/curl constraints.
//! - Path query operations: `point_of`, `direction_of`, `subpath`, `reverse`.

pub mod hobby;

use crate::bezier::CubicSegment;
use crate::types::{
    index_to_scalar, scalar_to_index, Knot, KnotDirection, Path, Point, Scalar, Vec2, EPSILON,
};

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
#[must_use]
pub fn subpath(path: &Path, t1: Scalar, t2: Scalar) -> Path {
    if path.knots.is_empty() {
        return Path::new();
    }

    let n = path.num_segments();
    if n == 0 {
        return Path::from_knots(vec![path.knots[0].clone()], false);
    }

    // Handle reversed direction
    if t1 > t2 {
        let result = subpath(path, t2, t1);
        return reverse(&result);
    }

    let mut knots = Vec::new();

    let (seg1, frac1) = time_to_seg_frac(t1, n);
    let (seg2, frac2) = time_to_seg_frac(t2, n);

    if seg1 == seg2 && frac2 > frac1 {
        // Both endpoints in the same segment
        let cubic = CubicSegment::from_path(path, seg1);
        let (_, right) = cubic.split(frac1);
        let t_inner = if (1.0 - frac1).abs() < EPSILON {
            0.0
        } else {
            (frac2 - frac1) / (1.0 - frac1)
        };
        let (sub, _) = right.split(t_inner);
        let p0 = cubic.eval(frac1);
        let p1 = cubic.eval(frac2);
        knots.push(Knot::with_controls(p0, p0, sub.p1));
        knots.push(Knot::with_controls(p1, sub.p2, p1));
    } else {
        // Start knot from splitting first segment
        let cubic1 = CubicSegment::from_path(path, seg1);
        let (_, right_part) = cubic1.split(frac1);
        let start_pt = cubic1.eval(frac1);
        knots.push(Knot::with_controls(start_pt, start_pt, right_part.p1));

        // End of first partial segment
        let j1 = (seg1 + 1) % path.knots.len();
        let mut k = path.knots[j1].clone();
        k.left = KnotDirection::Explicit(right_part.p2);
        knots.push(k);

        // Full intermediate segments
        for seg in (seg1 + 1)..seg2 {
            let j = (seg + 1) % path.knots.len();
            knots.push(path.knots[j].clone());
        }

        // Split last segment
        if frac2.abs() > EPSILON {
            let cubic_last = CubicSegment::from_path(path, seg2);
            let (left_part, _) = cubic_last.split(frac2);
            let end_pt = cubic_last.eval(frac2);

            if let Some(last) = knots.last_mut() {
                last.right = KnotDirection::Explicit(left_part.p1);
            }
            knots.push(Knot::with_controls(end_pt, left_part.p2, end_pt));
        }
    }

    Path::from_knots(knots, false)
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
    fn test_num_segments() {
        let p1 = make_line_path();
        assert_eq!(p1.num_segments(), 1);

        let p2 = make_triangle_path();
        assert_eq!(p2.num_segments(), 3);
    }
}
