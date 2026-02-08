//! Pen operations for `MetaPost`.
//!
//! `MetaPost` pens come in two forms:
//! - **Elliptical**: a transformed unit circle (`pencircle scaled 2` etc.).
//!   Stored as a `kurbo::Affine` mapping the unit circle to the pen shape.
//! - **Polygonal**: a convex polygon of vertices (`makepen`).
//!
//! Key operations:
//! - `makepen` — convert a convex path to a polygonal pen
//! - `makepath` — convert a pen back to a path
//! - `penoffset` — find the pen offset in a given direction

use kurbo::{Point, Vec2};

use crate::types::{index_to_scalar, GraphicsError, Knot, Path, Pen, Scalar};

// ---------------------------------------------------------------------------
// pencircle / nullpen
// ---------------------------------------------------------------------------

/// Create a circular pen of the given diameter.
#[must_use]
pub fn pencircle(diameter: Scalar) -> Pen {
    Pen::circle(diameter)
}

/// The null pen: a single point at the origin.
#[must_use]
pub const fn nullpen() -> Pen {
    Pen::Elliptical(kurbo::Affine::new([0.0, 0.0, 0.0, 0.0, 0.0, 0.0]))
}

// ---------------------------------------------------------------------------
// makepen — path to pen
// ---------------------------------------------------------------------------

/// Convert a cyclic path (after Hobby's algorithm) to a polygonal pen.
///
/// Extracts the on-curve points and computes the convex hull.
/// The path must be cyclic. Returns a polygonal pen with vertices in
/// counter-clockwise order.
///
/// Degenerate cases are allowed:
/// - 1 knot: a single-point pen (like `penspeck`)
/// - 2 knots: a line-segment pen (like `penrazor`)
///
/// # Errors
///
/// Returns [`GraphicsError::InvalidPen`] if the path is not cyclic or is
/// empty.
pub fn makepen(path: &Path) -> Result<Pen, GraphicsError> {
    if !path.is_cyclic {
        return Err(GraphicsError::InvalidPen("makepen requires a cyclic path"));
    }
    if path.knots.is_empty() {
        return Err(GraphicsError::InvalidPen(
            "makepen requires a non-empty path",
        ));
    }

    let points: Vec<Point> = path.knots.iter().map(|k| k.point).collect();
    let hull = convex_hull(&points);
    Ok(Pen::Polygonal(hull))
}

// ---------------------------------------------------------------------------
// makepath — pen to path
// ---------------------------------------------------------------------------

/// Convert a pen to a path.
///
/// - Elliptical pens produce an 8-knot approximation of the transformed circle.
/// - Polygonal pens produce a cyclic path through the vertices.
#[must_use]
pub fn makepath(pen: &Pen) -> Path {
    match pen {
        Pen::Elliptical(affine) => make_ellipse_path(affine),
        Pen::Polygonal(vertices) => {
            let knots = vertices
                .iter()
                .enumerate()
                .map(|(i, &p)| {
                    let prev = if i == 0 { vertices.len() - 1 } else { i - 1 };
                    let next = (i + 1) % vertices.len();

                    // Straight-line controls for polygonal pens
                    let left_cp = lerp(vertices[prev], p, 2.0 / 3.0);
                    let right_cp = lerp(p, vertices[next], 1.0 / 3.0);
                    Knot::with_controls(p, left_cp, right_cp)
                })
                .collect();
            Path::from_knots(knots, true)
        }
    }
}

/// Generate an 8-point approximation of an ellipse from an affine transform
/// of the unit circle.
///
/// The 8 points are at 0, 45, 90, ..., 315 degrees on the unit circle,
/// transformed by the affine. Control points use the standard cubic
/// approximation constant `kappa = 4*(sqrt(2)-1)/3 ≈ 0.5522847`.
fn make_ellipse_path(affine: &kurbo::Affine) -> Path {
    // Magic constant for cubic approximation of a quarter-circle arc
    const KAPPA: Scalar = 0.552_284_749_831;

    let n = 8;
    let mut knots = Vec::with_capacity(n);

    for i in 0..n {
        let angle = index_to_scalar(i) * std::f64::consts::FRAC_PI_4;
        let cos_a = angle.cos();
        let sin_a = angle.sin();

        // Point on unit circle
        let p = Point::new(cos_a, sin_a);
        // Tangent direction (perpendicular to radius)
        let tangent = Vec2::new(-sin_a, cos_a);

        let on_curve = affine_transform_point(affine, p);
        let right_cp = affine_transform_point(
            affine,
            Point::new(KAPPA.mul_add(tangent.x, p.x), KAPPA.mul_add(tangent.y, p.y)),
        );
        let left_cp = affine_transform_point(
            affine,
            Point::new(
                KAPPA.mul_add(-tangent.x, p.x),
                KAPPA.mul_add(-tangent.y, p.y),
            ),
        );

        knots.push(Knot::with_controls(on_curve, left_cp, right_cp));
    }

    Path::from_knots(knots, true)
}

// ---------------------------------------------------------------------------
// penoffset — find pen boundary in a given direction
// ---------------------------------------------------------------------------

/// Find the pen offset (support point) in the given direction.
///
/// Returns the point on the pen boundary that is furthest in the
/// direction `dir`. This is used for computing stroked path envelopes.
#[must_use]
pub fn penoffset(pen: &Pen, dir: Vec2) -> Point {
    match pen {
        Pen::Elliptical(affine) => {
            // For an elliptical pen: find the point on the transformed circle
            // that has the outward normal in direction `dir`.
            //
            // If T maps the unit circle to the pen, then the offset in direction
            // d is T * normalize(T^{-T} * d).
            let coeffs = affine.as_coeffs();
            let det = coeffs[0].mul_add(coeffs[3], -(coeffs[2] * coeffs[1]));
            if det.abs() < 1e-30 {
                return Point::ZERO;
            }
            // Inverse transpose
            let inv_t_x = coeffs[3].mul_add(dir.x, -(coeffs[1] * dir.y)) / det;
            let inv_t_y = (-coeffs[2]).mul_add(dir.x, coeffs[0] * dir.y) / det;
            let len = inv_t_x.hypot(inv_t_y);
            if len < 1e-30 {
                return Point::ZERO;
            }
            let unit_x = inv_t_x / len;
            let unit_y = inv_t_y / len;
            affine_transform_point(affine, Point::new(unit_x, unit_y))
        }
        Pen::Polygonal(vertices) => {
            // Find the vertex with the maximum dot product with dir
            vertices
                .iter()
                .copied()
                .max_by(|a, b| {
                    let da = dir.x.mul_add(a.x, dir.y * a.y);
                    let db = dir.x.mul_add(b.x, dir.y * b.y);
                    da.partial_cmp(&db).unwrap_or(std::cmp::Ordering::Equal)
                })
                .unwrap_or(Point::ZERO)
        }
    }
}

// ---------------------------------------------------------------------------
// Convex hull
// ---------------------------------------------------------------------------

/// Compute the convex hull of a set of points.
/// Returns vertices in counter-clockwise order.
#[must_use]
pub fn convex_hull(points: &[Point]) -> Vec<Point> {
    if points.len() < 3 {
        return points.to_vec();
    }

    // Andrew's monotone chain algorithm
    let mut sorted: Vec<Point> = points.to_vec();
    sorted.sort_by(|a, b| {
        a.x.partial_cmp(&b.x)
            .unwrap_or(std::cmp::Ordering::Equal)
            .then(a.y.partial_cmp(&b.y).unwrap_or(std::cmp::Ordering::Equal))
    });

    let mut hull: Vec<Point> = Vec::with_capacity(2 * sorted.len());

    // Build lower hull
    for &p in &sorted {
        while hull.len() >= 2 && cross(hull[hull.len() - 2], hull[hull.len() - 1], p) <= 0.0 {
            hull.pop();
        }
        hull.push(p);
    }

    // Build upper hull
    let lower_len = hull.len() + 1;
    for &p in sorted.iter().rev() {
        while hull.len() >= lower_len && cross(hull[hull.len() - 2], hull[hull.len() - 1], p) <= 0.0
        {
            hull.pop();
        }
        hull.push(p);
    }

    hull.pop(); // Remove the last point (duplicate of first)
    hull
}

/// 2D cross product of vectors OA and OB.
fn cross(o: Point, a: Point, b: Point) -> Scalar {
    (a.x - o.x).mul_add(b.y - o.y, -((a.y - o.y) * (b.x - o.x)))
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn affine_transform_point(a: &kurbo::Affine, p: Point) -> Point {
    let c = a.as_coeffs();
    Point::new(
        c[0].mul_add(p.x, c[2].mul_add(p.y, c[4])),
        c[1].mul_add(p.x, c[3].mul_add(p.y, c[5])),
    )
}

fn lerp(a: Point, b: Point, t: Scalar) -> Point {
    Point::new(t.mul_add(b.x - a.x, a.x), t.mul_add(b.y - a.y, a.y))
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
    use crate::types::EPSILON;

    #[test]
    fn test_pencircle_default() {
        let pen = pencircle(1.0);
        match pen {
            Pen::Elliptical(a) => {
                let c = a.as_coeffs();
                assert!((c[0] - 0.5).abs() < EPSILON);
                assert!((c[3] - 0.5).abs() < EPSILON);
            }
            Pen::Polygonal(_) => panic!("expected elliptical"),
        }
    }

    #[test]
    fn test_nullpen() {
        let pen = nullpen();
        match pen {
            Pen::Elliptical(a) => {
                let c = a.as_coeffs();
                assert!(c[0].abs() < EPSILON);
                assert!(c[3].abs() < EPSILON);
            }
            Pen::Polygonal(_) => panic!("expected elliptical"),
        }
    }

    #[test]
    fn test_makepath_elliptical_has_8_knots() {
        let pen = pencircle(2.0);
        let path = makepath(&pen);
        assert!(path.is_cyclic);
        assert_eq!(path.knots.len(), 8);
    }

    #[test]
    fn test_makepath_elliptical_points_on_circle() {
        let pen = pencircle(2.0); // radius = 1.0
        let path = makepath(&pen);
        for knot in &path.knots {
            let r = knot.point.to_vec2().length();
            assert!(
                (r - 1.0).abs() < 0.01,
                "point {:?} not on unit circle: r = {r}",
                knot.point
            );
        }
    }

    #[test]
    fn test_makepen_triangle() {
        let knots = vec![
            Knot::with_controls(
                Point::new(0.0, 0.0),
                Point::new(-0.5, -0.5),
                Point::new(0.5, 0.0),
            ),
            Knot::with_controls(
                Point::new(1.0, 0.0),
                Point::new(0.5, 0.0),
                Point::new(1.0, 0.5),
            ),
            Knot::with_controls(
                Point::new(0.5, 1.0),
                Point::new(1.0, 0.5),
                Point::new(0.0, 0.5),
            ),
        ];
        let path = Path::from_knots(knots, true);
        let pen = makepen(&path).unwrap();
        match pen {
            Pen::Polygonal(verts) => {
                assert!(verts.len() >= 3);
            }
            Pen::Elliptical(_) => panic!("expected polygonal"),
        }
    }

    #[test]
    fn test_penoffset_circle_right() {
        let pen = pencircle(2.0); // radius 1
        let offset = penoffset(&pen, Vec2::new(1.0, 0.0));
        assert!((offset.x - 1.0).abs() < 0.01, "offset.x = {}", offset.x);
        assert!(offset.y.abs() < 0.01, "offset.y = {}", offset.y);
    }

    #[test]
    fn test_penoffset_circle_up() {
        let pen = pencircle(2.0); // radius 1
        let offset = penoffset(&pen, Vec2::new(0.0, 1.0));
        assert!(offset.x.abs() < 0.01, "offset.x = {}", offset.x);
        assert!((offset.y - 1.0).abs() < 0.01, "offset.y = {}", offset.y);
    }

    #[test]
    fn test_penoffset_polygonal() {
        let pen = Pen::Polygonal(vec![
            Point::new(-1.0, 0.0),
            Point::new(1.0, 0.0),
            Point::new(0.0, 1.0),
        ]);
        let offset = penoffset(&pen, Vec2::new(1.0, 0.0));
        assert!((offset.x - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_convex_hull_square() {
        let points = vec![
            Point::new(0.0, 0.0),
            Point::new(1.0, 0.0),
            Point::new(1.0, 1.0),
            Point::new(0.0, 1.0),
            Point::new(0.5, 0.5), // interior point
        ];
        let hull = convex_hull(&points);
        assert_eq!(hull.len(), 4);
    }

    #[test]
    fn test_convex_hull_triangle() {
        let points = vec![
            Point::new(0.0, 0.0),
            Point::new(2.0, 0.0),
            Point::new(1.0, 2.0),
        ];
        let hull = convex_hull(&points);
        assert_eq!(hull.len(), 3);
    }

    #[test]
    fn test_convex_hull_collinear() {
        let points = vec![
            Point::new(0.0, 0.0),
            Point::new(1.0, 0.0),
            Point::new(2.0, 0.0),
        ];
        let hull = convex_hull(&points);
        // Collinear points: hull is degenerate (2 points)
        assert!(hull.len() <= 3);
    }
}
