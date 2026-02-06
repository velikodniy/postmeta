//! Path operations and Hobby's spline algorithm.
//!
//! This module provides:
//! - Conversion between `Path` (`MetaPost` knot representation) and
//!   `kurbo::BezPath` (cubic Bezier segments).
//! - Hobby's algorithm for computing smooth cubic Bezier control points
//!   through a sequence of knots with direction/tension/curl constraints.
//! - Path query operations: `point_of`, `direction_of`, `subpath`, `reverse`.

pub mod hobby;

use kurbo::{BezPath, PathEl, Point, Vec2};

use crate::types::{Knot, KnotDirection, Path, Scalar, EPSILON};

// ---------------------------------------------------------------------------
// Path → BezPath conversion
// ---------------------------------------------------------------------------

/// Convert a fully-resolved `Path` (all directions `Explicit`) to a `kurbo::BezPath`.
///
/// Panics if any knot direction is not `Explicit`.
pub fn to_bez_path(path: &Path) -> BezPath {
    let mut bp = BezPath::new();
    if path.knots.is_empty() {
        return bp;
    }

    bp.move_to(path.knots[0].point);

    let n = path.num_segments();
    for i in 0..n {
        let j = (i + 1) % path.knots.len();
        let k0 = &path.knots[i];
        let k1 = &path.knots[j];

        let KnotDirection::Explicit(cp1) = k0.right else {
            panic!("path not fully resolved: knot {i} right direction is not Explicit")
        };
        let KnotDirection::Explicit(cp2) = k1.left else {
            panic!("path not fully resolved: knot {j} left direction is not Explicit")
        };

        bp.curve_to(cp1, cp2, k1.point);
    }

    if path.is_cyclic {
        bp.close_path();
    }

    bp
}

/// Create a `Path` from a sequence of explicit cubic Bezier segments.
pub fn from_bez_path(bp: &BezPath, is_cyclic: bool) -> Path {
    let elements = bp.elements();
    let mut knots: Vec<Knot> = Vec::new();

    for el in elements {
        match *el {
            PathEl::MoveTo(p) => {
                knots.push(Knot::new(p));
            }
            PathEl::CurveTo(cp1, cp2, p) => {
                // Set the right control of the previous knot
                if let Some(prev) = knots.last_mut() {
                    prev.right = KnotDirection::Explicit(cp1);
                }
                // Create the new knot with left control
                let mut k = Knot::new(p);
                k.left = KnotDirection::Explicit(cp2);
                knots.push(k);
            }
            PathEl::LineTo(p) => {
                // A line is a degenerate cubic where controls = endpoints
                if let Some(prev) = knots.last_mut() {
                    prev.right = KnotDirection::Explicit(prev.point);
                }
                let mut k = Knot::new(p);
                k.left = KnotDirection::Explicit(p);
                knots.push(k);
            }
            PathEl::ClosePath | PathEl::QuadTo(..) => {}
        }
    }

    Path::from_knots(knots, is_cyclic)
}

// ---------------------------------------------------------------------------
// Path query operations
// ---------------------------------------------------------------------------

/// Get the point at time `t` on the path.
///
/// `t` ranges from 0 to `path.num_segments()`. Integer values correspond
/// to knot points. Fractional values interpolate along the cubic segment.
pub fn point_of(path: &Path, t: Scalar) -> Point {
    if path.knots.is_empty() {
        return Point::ZERO;
    }

    let n = path.num_segments();
    if n == 0 {
        return path.knots[0].point;
    }

    // Clamp for open paths; wrap for cyclic
    let t = if path.is_cyclic {
        let n_f = n as Scalar;
        ((t % n_f) + n_f) % n_f
    } else {
        t.clamp(0.0, n as Scalar)
    };

    let seg = (t.floor() as usize).min(n - 1);
    let frac = t - seg as Scalar;

    let cubic = get_segment(path, seg);
    eval_cubic(&cubic, frac)
}

/// Get the direction (tangent vector) at time `t` on the path.
pub fn direction_of(path: &Path, t: Scalar) -> Vec2 {
    if path.knots.is_empty() || path.num_segments() == 0 {
        return Vec2::ZERO;
    }

    let n = path.num_segments();
    let t = if path.is_cyclic {
        let n_f = n as Scalar;
        ((t % n_f) + n_f) % n_f
    } else {
        t.clamp(0.0, n as Scalar)
    };

    let seg = (t.floor() as usize).min(n - 1);
    let frac = t - seg as Scalar;

    let cubic = get_segment(path, seg);
    eval_cubic_deriv(&cubic, frac)
}

/// Get the precontrol point at time `t`.
pub fn precontrol_of(path: &Path, t: Scalar) -> Point {
    if path.knots.is_empty() {
        return Point::ZERO;
    }
    let n = path.num_segments();
    if n == 0 {
        return path.knots[0].point;
    }

    let t = if path.is_cyclic {
        let n_f = n as Scalar;
        ((t % n_f) + n_f) % n_f
    } else {
        t.clamp(0.0, n as Scalar)
    };

    let seg = (t.floor() as usize).min(n - 1);
    let j = (seg + 1) % path.knots.len();
    match path.knots[j].left {
        KnotDirection::Explicit(p) => p,
        _ => path.knots[j].point,
    }
}

/// Get the postcontrol point at time `t`.
pub fn postcontrol_of(path: &Path, t: Scalar) -> Point {
    if path.knots.is_empty() {
        return Point::ZERO;
    }
    let n = path.num_segments();
    if n == 0 {
        return path.knots[0].point;
    }

    let t = if path.is_cyclic {
        let n_f = n as Scalar;
        ((t % n_f) + n_f) % n_f
    } else {
        t.clamp(0.0, n as Scalar)
    };

    let seg = (t.floor() as usize).min(n - 1);
    match path.knots[seg].right {
        KnotDirection::Explicit(p) => p,
        _ => path.knots[seg].point,
    }
}

/// Extract a subpath from time `t1` to time `t2`.
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

    // Split the first segment at t1
    let seg1 = (t1.floor() as usize).min(n - 1);
    let frac1 = t1 - seg1 as Scalar;

    let seg2 = (t2.floor() as usize).min(n - 1);
    let frac2 = t2 - seg2 as Scalar;

    if seg1 == seg2 && frac2 > frac1 {
        // Both endpoints in the same segment
        let cubic = get_segment(path, seg1);
        let (_, right) = split_cubic(&cubic, frac1);
        let t_inner = if (1.0 - frac1).abs() < EPSILON {
            0.0
        } else {
            (frac2 - frac1) / (1.0 - frac1)
        };
        let (sub, _) = split_cubic(&right, t_inner);
        let p0 = eval_cubic(&cubic, frac1);
        let p1 = eval_cubic(&cubic, frac2);
        knots.push(Knot::with_controls(p0, p0, sub.p1));
        knots.push(Knot::with_controls(p1, sub.p2, p1));
    } else {
        // Start knot from splitting first segment
        let cubic1 = get_segment(path, seg1);
        let (_, right_part) = split_cubic(&cubic1, frac1);
        let start_pt = eval_cubic(&cubic1, frac1);
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
            let cubic_last = get_segment(path, seg2);
            let (left_part, _) = split_cubic(&cubic_last, frac2);
            let end_pt = eval_cubic(&cubic_last, frac2);

            if let Some(last) = knots.last_mut() {
                last.right = KnotDirection::Explicit(left_part.p1);
            }
            knots.push(Knot::with_controls(end_pt, left_part.p2, end_pt));
        }
    }

    Path::from_knots(knots, false)
}

/// Reverse a path.
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
// Internal helpers
// ---------------------------------------------------------------------------

/// Representation of a cubic Bezier segment by 4 control points.
struct Cubic {
    p0: Point,
    p1: Point,
    p2: Point,
    p3: Point,
}

/// Extract segment `i` as a Cubic.
fn get_segment(path: &Path, i: usize) -> Cubic {
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

    Cubic {
        p0: k0.point,
        p1,
        p2,
        p3: k1.point,
    }
}

/// Evaluate a cubic at parameter `t` in [0, 1].
#[allow(clippy::many_single_char_names)]
fn eval_cubic(c: &Cubic, t: Scalar) -> Point {
    let s = 1.0 - t;
    let a = s * s * s;
    let b = 3.0 * s * s * t;
    let cc = 3.0 * s * t * t;
    let d = t * t * t;
    Point::new(
        d.mul_add(c.p3.x, a * c.p0.x + b * c.p1.x + cc * c.p2.x),
        d.mul_add(c.p3.y, a * c.p0.y + b * c.p1.y + cc * c.p2.y),
    )
}

/// Evaluate the derivative of a cubic at parameter `t` in [0, 1].
#[allow(clippy::many_single_char_names)]
fn eval_cubic_deriv(c: &Cubic, t: Scalar) -> Vec2 {
    let s = 1.0 - t;
    let a = 3.0 * s * s;
    let b = 6.0 * s * t;
    let cc = 3.0 * t * t;
    Vec2::new(
        a * (c.p1.x - c.p0.x) + b * (c.p2.x - c.p1.x) + cc * (c.p3.x - c.p2.x),
        a * (c.p1.y - c.p0.y) + b * (c.p2.y - c.p1.y) + cc * (c.p3.y - c.p2.y),
    )
}

/// Split a cubic at parameter `t` using de Casteljau's algorithm.
/// Returns (`left_half`, `right_half`).
fn split_cubic(c: &Cubic, t: Scalar) -> (Cubic, Cubic) {
    let ab = lerp_pt(c.p0, c.p1, t);
    let bc = lerp_pt(c.p1, c.p2, t);
    let cd = lerp_pt(c.p2, c.p3, t);
    let abc = lerp_pt(ab, bc, t);
    let bcd = lerp_pt(bc, cd, t);
    let abcd = lerp_pt(abc, bcd, t);

    (
        Cubic {
            p0: c.p0,
            p1: ab,
            p2: abc,
            p3: abcd,
        },
        Cubic {
            p0: abcd,
            p1: bcd,
            p2: cd,
            p3: c.p3,
        },
    )
}

fn lerp_pt(a: Point, b: Point, t: Scalar) -> Point {
    Point::new(t.mul_add(b.x - a.x, a.x), t.mul_add(b.y - a.y, a.y))
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
                let right_cp = lerp_pt(pts[i], pts[j], 1.0 / 3.0);
                let left_cp = lerp_pt(pts[prev], pts[i], 2.0 / 3.0);
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
    fn test_to_bez_path_open() {
        let path = make_line_path();
        let bp = to_bez_path(&path);
        let elements = bp.elements();
        assert_eq!(elements.len(), 2); // MoveTo + CurveTo
    }

    #[test]
    fn test_to_bez_path_cyclic() {
        let path = make_triangle_path();
        let bp = to_bez_path(&path);
        let elements = bp.elements();
        // MoveTo + 3 CurveTos + ClosePath = 5
        assert_eq!(elements.len(), 5);
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
        let end = point_of(&sub, sub.num_segments() as Scalar);
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
