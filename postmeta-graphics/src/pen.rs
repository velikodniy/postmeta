//! Pen operations for `MetaPost`.
//!
//! `MetaPost` pens come in two forms:
//! - **Elliptical**: a transformed unit circle (`pencircle scaled 2` etc.).
//!   Stored as an affine matrix mapping the unit circle to the pen shape.
//! - **Polygonal**: a convex polygon of vertices (`makepen`).
//!
//! Key operations:
//! - `makepen` — convert a convex path to a polygonal pen
//! - `makepath` — convert a pen back to a path
//! - `penoffset` — find the pen offset in a given direction

use crate::error::GraphicsError;
use crate::path::{BezierPath, Path, SegmentControls};
use crate::transform::Transform;
use crate::types::{Knot, NEAR_ZERO, Point, Scalar, Vec2, index_to_scalar};

// ---------------------------------------------------------------------------
// Pen
// ---------------------------------------------------------------------------

/// A pen: either elliptical (common) or polygonal.
#[derive(Debug, Clone, PartialEq)]
pub enum Pen {
    /// An elliptical pen defined by an affine transform of the unit circle.
    /// The transform maps the unit circle to the pen shape.
    Elliptical(Transform),
    /// A convex polygonal pen defined by its vertices in counter-clockwise
    /// order.
    Polygonal(Vec<Point>),
}

impl Pen {
    /// Create a circular pen with the given diameter centered at origin.
    #[must_use]
    pub const fn circle(diameter: Scalar) -> Self {
        let r = diameter / 2.0;
        Self::Elliptical(Transform {
            txx: r,
            tyy: r,
            ..Transform::IDENTITY
        })
    }

    /// The null pen: a single point at the origin.
    #[must_use]
    pub const fn null() -> Self {
        Self::Elliptical(Transform::ZERO)
    }

    /// Find the pen offset (support point) in the given direction.
    ///
    /// Returns the point on the pen boundary that is furthest in the
    /// direction `dir`. This is used for computing stroked path envelopes.
    #[must_use]
    pub fn offset(&self, dir: Vec2) -> Point {
        penoffset(self, dir)
    }
}

impl Default for Pen {
    /// The default pen is a circle with diameter 0.5.
    fn default() -> Self {
        Self::circle(0.5)
    }
}

// ---------------------------------------------------------------------------
// makepen — path to pen
// ---------------------------------------------------------------------------

/// Convert a path to a polygonal pen.
///
/// Extracts the on-curve points and computes the convex hull.
/// Returns a polygonal pen with vertices in counter-clockwise order.
///
/// If the path is not cyclic the ends are implicitly connected by a
/// straight line, matching the original `MetaPost` behaviour (mp.web §302).
///
/// Degenerate cases are allowed:
/// - 1 knot: a single-point pen (like `penspeck`)
/// - 2 knots: a line-segment pen (like `penrazor`)
///
/// # Errors
///
/// Returns [`GraphicsError::InvalidPen`] if the path is empty.
pub fn makepen(path: &Path) -> Result<Pen, GraphicsError> {
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
        Pen::Elliptical(t) => make_ellipse_path(t),
        Pen::Polygonal(vertices) => {
            let knots = vertices
                .iter()
                .enumerate()
                .map(|(i, &p)| {
                    let prev = if i == 0 { vertices.len() - 1 } else { i - 1 };
                    let next = (i + 1) % vertices.len();

                    // Straight-line controls for polygonal pens
                    let left_cp = vertices[prev].lerp(p, 2.0 / 3.0);
                    let right_cp = p.lerp(vertices[next], 1.0 / 3.0);
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
/// transformed by the affine. Control points use the cubic Bezier
/// approximation constant for 45° arcs: `kappa = (4/3) * tan(π/16)`.
fn make_ellipse_path(t: &Transform) -> Path {
    // Cubic approximation constant for a 45° arc (8 segments per circle).
    // kappa = (4/3) * tan(π/16) ≈ 0.26520784
    const KAPPA: Scalar = 0.265_207_840_674;

    let knots = (0..8)
        .map(|i| {
            let angle = index_to_scalar(i) * std::f64::consts::FRAC_PI_4;
            let (sin_a, cos_a) = angle.sin_cos();

            let p = Point::new(cos_a, sin_a);
            let tangent = Vec2::new(-sin_a, cos_a);

            let on_curve = t.apply(p);
            let right_cp = t.apply(p + tangent * KAPPA);
            let left_cp = t.apply(p - tangent * KAPPA);

            Knot::with_controls(on_curve, left_cp, right_cp)
        })
        .collect();

    Path::from_knots(knots, true)
}

// ---------------------------------------------------------------------------
// BezierPath ↔ Pen conversions
// ---------------------------------------------------------------------------

/// `makepen` for `BezierPath`: convert a bezier path to a polygonal pen.
///
/// Extracts the on-curve knot points and computes their convex hull.
///
/// # Errors
///
/// Returns [`GraphicsError::InvalidPen`] if the path has no knot points.
impl TryFrom<&BezierPath> for Pen {
    type Error = GraphicsError;

    fn try_from(path: &BezierPath) -> Result<Self, Self::Error> {
        if path.knot_points().is_empty() {
            return Err(GraphicsError::InvalidPen(
                "makepen requires a non-empty path",
            ));
        }
        let hull = convex_hull(path.knot_points());
        Ok(Self::Polygonal(hull))
    }
}

/// `makepath` for `BezierPath`: convert a pen to a `BezierPath`.
///
/// - **Elliptical** pens produce an 8-knot circular approximation built as
///   a `BezierPath` with explicit cubic controls.
/// - **Polygonal** pens produce a cyclic `BezierPath` with straight-line
///   segments through the vertices.
impl From<&Pen> for BezierPath {
    fn from(pen: &Pen) -> Self {
        match pen {
            Pen::Elliptical(t) => make_ellipse_bezier_path(t),
            Pen::Polygonal(vertices) => {
                if vertices.is_empty() {
                    return Self::new();
                }
                let n = vertices.len();
                let controls: Vec<SegmentControls> = (0..n)
                    .map(|i| {
                        let j = (i + 1) % n;
                        SegmentControls {
                            post: vertices[i].lerp(vertices[j], 1.0 / 3.0),
                            pre: vertices[i].lerp(vertices[j], 2.0 / 3.0),
                        }
                    })
                    .collect();
                Self::from_parts(vertices.clone(), controls, true)
            }
        }
    }
}

/// Generate an 8-point approximation of an ellipse as a [`BezierPath`].
///
/// Same mathematics as [`make_ellipse_path`], but produces a `BezierPath`
/// directly (no `Knot`/`KnotDirection` overhead).
fn make_ellipse_bezier_path(t: &Transform) -> BezierPath {
    const KAPPA: Scalar = 0.265_207_840_674;
    const N: usize = 8;

    let mut points = Vec::with_capacity(N);
    let mut controls = Vec::with_capacity(N);

    for i in 0..N {
        let angle = index_to_scalar(i) * std::f64::consts::FRAC_PI_4;
        let (sin_a, cos_a) = angle.sin_cos();

        let p = Point::new(cos_a, sin_a);
        let tangent = Vec2::new(-sin_a, cos_a);

        let on_curve = t.apply(p);
        let right_cp = t.apply(p + tangent * KAPPA);
        let left_cp = t.apply(p - tangent * KAPPA);

        points.push(on_curve);

        // Build the segment control from this knot to the next.
        // The "post" handle of segment i is the right_cp of knot i.
        // The "pre" handle of segment i is the left_cp of knot (i+1).
        // We'll set the pre handle in the next iteration; for now, store
        // the right_cp and fix up later.
        //
        // Actually, we have all the data now — compute knot i+1's left_cp.
        let j = (i + 1) % N;
        let angle_j = index_to_scalar(j) * std::f64::consts::FRAC_PI_4;
        let (sin_j, cos_j) = angle_j.sin_cos();
        let p_j = Point::new(cos_j, sin_j);
        let tangent_j = Vec2::new(-sin_j, cos_j);
        let left_cp_j = t.apply(p_j - tangent_j * KAPPA);

        controls.push(SegmentControls {
            post: right_cp,
            pre: left_cp_j,
        });

        // Suppress unused variable warning — left_cp is the pre-handle
        // for the segment ending at this knot, which was already set in
        // the previous iteration's controls entry.
        let _ = left_cp;
    }

    BezierPath::from_parts(points, controls, true)
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
        Pen::Elliptical(t) => {
            // For an elliptical pen: find the point on the transformed circle
            // that has the outward normal in direction `dir`.
            //
            // If T maps the unit circle to the pen, the offset in direction d
            // is T_linear * normalize(T_linear^{-T} * d).  Only the 2x2 linear
            // part matters — translation represents the pen's origin, not its
            // shape.
            let det = t.txx.mul_add(t.tyy, -(t.txy * t.tyx));
            if det.abs() < NEAR_ZERO {
                return Point::ZERO;
            }
            // Inverse transpose of the 2x2 part
            let inv_t_x = t.tyy.mul_add(dir.x, -(t.tyx * dir.y)) / det;
            let inv_t_y = (-t.txy).mul_add(dir.x, t.txx * dir.y) / det;
            let len = inv_t_x.hypot(inv_t_y);
            if len < NEAR_ZERO {
                return Point::ZERO;
            }
            let unit_x = inv_t_x / len;
            let unit_y = inv_t_y / len;
            // Apply only the linear part (no translation)
            Point::new(
                t.txx.mul_add(unit_x, t.txy * unit_y),
                t.tyx.mul_add(unit_x, t.tyy * unit_y),
            )
        }
        Pen::Polygonal(vertices) => {
            // Find the vertex with the maximum dot product with dir
            vertices
                .iter()
                .copied()
                .max_by(|a, b| {
                    let da = dir.x.mul_add(a.x, dir.y * a.y);
                    let db = dir.x.mul_add(b.x, dir.y * b.y);
                    da.total_cmp(&db)
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
    sorted.sort_by(|a, b| a.x.total_cmp(&b.x).then(a.y.total_cmp(&b.y)));

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
    let oa = a - o;
    let ob = b - o;
    oa.x.mul_add(ob.y, -(oa.y * ob.x))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::EPSILON;

    #[test]
    fn test_pencircle() {
        let pen = Pen::circle(1.0);
        match pen {
            Pen::Elliptical(t) => {
                assert!((t.txx - 0.5).abs() < EPSILON);
                assert!((t.tyy - 0.5).abs() < EPSILON);
            }
            Pen::Polygonal(_) => panic!("expected elliptical"),
        }
    }

    #[test]
    fn test_nullpen() {
        let pen = Pen::null();
        match pen {
            Pen::Elliptical(t) => {
                assert!(t.txx.abs() < EPSILON);
                assert!(t.tyy.abs() < EPSILON);
            }
            Pen::Polygonal(_) => panic!("expected elliptical"),
        }
    }

    #[test]
    fn pen_circle() {
        let p = Pen::circle(2.0);
        match p {
            Pen::Elliptical(t) => {
                assert!((t.txx - 1.0).abs() < EPSILON); // scale x
                assert!((t.tyy - 1.0).abs() < EPSILON); // scale y
                assert!(t.txy.abs() < EPSILON);
                assert!(t.tyx.abs() < EPSILON);
            }
            Pen::Polygonal(_) => panic!("expected elliptical"),
        }
    }

    #[test]
    fn test_makepath_elliptical_has_8_knots() {
        let pen = Pen::circle(2.0);
        let path = makepath(&pen);
        assert!(path.is_cyclic);
        assert_eq!(path.knots.len(), 8);
    }

    #[test]
    fn test_makepath_elliptical_points_on_circle() {
        let pen = Pen::circle(2.0); // radius = 1.0
        let path = makepath(&pen);
        for knot in &path.knots {
            let r = Vec2::from(knot.point).length();
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
        let pen = Pen::circle(2.0); // radius 1
        let offset = penoffset(&pen, Vec2::new(1.0, 0.0));
        assert!((offset.x - 1.0).abs() < 0.01, "offset.x = {}", offset.x);
        assert!(offset.y.abs() < 0.01, "offset.y = {}", offset.y);
    }

    #[test]
    fn test_penoffset_circle_up() {
        let pen = Pen::circle(2.0); // radius 1
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

    /// mp.web §302: non-cyclic paths are auto-closed by makepen.
    #[test]
    fn test_makepen_non_cyclic_auto_closes() {
        let knots = vec![
            Knot::new(Point::new(0.0, 0.0)),
            Knot::new(Point::new(1.0, 0.0)),
        ];
        let path = Path::from_knots(knots, false);
        assert!(!path.is_cyclic);
        let pen = makepen(&path).expect("makepen should accept non-cyclic path");
        match pen {
            Pen::Polygonal(verts) => {
                assert_eq!(verts.len(), 2);
            }
            Pen::Elliptical(_) => panic!("expected polygonal"),
        }
    }

    #[test]
    fn test_makepen_single_knot() {
        let path = Path::from_knots(vec![Knot::new(Point::new(5.0, 3.0))], true);
        let pen = makepen(&path).expect("single-knot makepen should work");
        match pen {
            Pen::Polygonal(verts) => {
                assert_eq!(verts.len(), 1);
                assert!((verts[0].x - 5.0).abs() < EPSILON);
                assert!((verts[0].y - 3.0).abs() < EPSILON);
            }
            Pen::Elliptical(_) => panic!("expected polygonal"),
        }
    }

    // -----------------------------------------------------------------------
    // TryFrom<&BezierPath> for Pen
    // -----------------------------------------------------------------------

    #[test]
    fn try_from_bezier_path_triangle() {
        // A triangle BezierPath with 3 knot points.
        let bp = BezierPath::from_parts(
            vec![
                Point::new(0.0, 0.0),
                Point::new(1.0, 0.0),
                Point::new(0.5, 1.0),
            ],
            vec![
                SegmentControls {
                    post: Point::new(0.33, 0.0),
                    pre: Point::new(0.67, 0.0),
                },
                SegmentControls {
                    post: Point::new(1.0, 0.33),
                    pre: Point::new(0.75, 0.67),
                },
                SegmentControls {
                    post: Point::new(0.25, 0.67),
                    pre: Point::new(0.0, 0.33),
                },
            ],
            true,
        );
        let pen = Pen::try_from(&bp).expect("triangle should produce a pen");
        match pen {
            Pen::Polygonal(verts) => {
                assert_eq!(verts.len(), 3, "triangle hull should have 3 vertices");
            }
            Pen::Elliptical(_) => panic!("expected polygonal"),
        }
    }

    #[test]
    fn try_from_bezier_path_empty_fails() {
        let bp = BezierPath::new();
        let result = Pen::try_from(&bp);
        assert!(result.is_err(), "empty BezierPath should fail");
    }

    #[test]
    fn try_from_bezier_path_single_point() {
        let bp = BezierPath::from_parts(vec![Point::new(3.0, 4.0)], vec![], false);
        let pen = Pen::try_from(&bp).expect("single-point BezierPath should succeed");
        match pen {
            Pen::Polygonal(verts) => {
                assert_eq!(verts.len(), 1);
                assert!((verts[0].x - 3.0).abs() < EPSILON);
                assert!((verts[0].y - 4.0).abs() < EPSILON);
            }
            Pen::Elliptical(_) => panic!("expected polygonal"),
        }
    }

    // -----------------------------------------------------------------------
    // From<&Pen> for BezierPath
    // -----------------------------------------------------------------------

    #[test]
    fn from_pen_elliptical_has_8_knots() {
        let pen = Pen::circle(2.0);
        let bp = BezierPath::from(&pen);
        assert!(bp.is_cyclic());
        assert_eq!(bp.num_knots(), 8);
        assert_eq!(bp.num_segments(), 8);
    }

    #[test]
    fn from_pen_elliptical_points_on_circle() {
        let pen = Pen::circle(2.0); // radius = 1.0
        let bp = BezierPath::from(&pen);
        for i in 0..bp.num_knots() {
            let p = bp.knot_point(i);
            let r = Vec2::from(p).length();
            assert!(
                (r - 1.0).abs() < 0.01,
                "knot {i} at {p:?} not on unit circle: r = {r}"
            );
        }
    }

    #[test]
    fn from_pen_polygonal_triangle() {
        let pen = Pen::Polygonal(vec![
            Point::new(0.0, 0.0),
            Point::new(1.0, 0.0),
            Point::new(0.5, 1.0),
        ]);
        let bp = BezierPath::from(&pen);
        assert!(bp.is_cyclic());
        assert_eq!(bp.num_knots(), 3);
        assert_eq!(bp.num_segments(), 3);

        // Knot points should match the vertices.
        assert!((bp.knot_point(0).x).abs() < EPSILON);
        assert!((bp.knot_point(0).y).abs() < EPSILON);
        assert!((bp.knot_point(1).x - 1.0).abs() < EPSILON);
        assert!((bp.knot_point(2).y - 1.0).abs() < EPSILON);
    }

    #[test]
    fn from_pen_polygonal_empty() {
        let pen = Pen::Polygonal(vec![]);
        let bp = BezierPath::from(&pen);
        assert_eq!(bp.num_knots(), 0);
        assert_eq!(bp.num_segments(), 0);
    }

    // -----------------------------------------------------------------------
    // Pen::offset method
    // -----------------------------------------------------------------------

    #[test]
    fn pen_offset_circle_right() {
        let pen = Pen::circle(2.0); // radius 1
        let offset = pen.offset(Vec2::new(1.0, 0.0));
        assert!((offset.x - 1.0).abs() < 0.01, "offset.x = {}", offset.x);
        assert!(offset.y.abs() < 0.01, "offset.y = {}", offset.y);
    }

    #[test]
    fn pen_offset_circle_up() {
        let pen = Pen::circle(2.0); // radius 1
        let offset = pen.offset(Vec2::new(0.0, 1.0));
        assert!(offset.x.abs() < 0.01, "offset.x = {}", offset.x);
        assert!((offset.y - 1.0).abs() < 0.01, "offset.y = {}", offset.y);
    }

    #[test]
    fn pen_offset_polygonal() {
        let pen = Pen::Polygonal(vec![
            Point::new(-1.0, 0.0),
            Point::new(1.0, 0.0),
            Point::new(0.0, 1.0),
        ]);
        let offset = pen.offset(Vec2::new(1.0, 0.0));
        assert!((offset.x - 1.0).abs() < EPSILON);
    }

    #[test]
    fn pen_offset_diagonal() {
        let pen = Pen::circle(2.0); // radius 1
        let dir = Vec2::new(1.0, 1.0);
        let offset = pen.offset(dir);
        // Should be at ~(1/sqrt(2), 1/sqrt(2)) ≈ (0.707, 0.707)
        let expected = 1.0 / 2.0_f64.sqrt();
        assert!(
            (offset.x - expected).abs() < 0.01,
            "offset.x = {}, expected {}",
            offset.x,
            expected
        );
        assert!(
            (offset.y - expected).abs() < 0.01,
            "offset.y = {}, expected {}",
            offset.y,
            expected
        );
    }

    // -----------------------------------------------------------------------
    // Roundtrip: BezierPath → Pen → BezierPath
    // -----------------------------------------------------------------------

    #[test]
    fn roundtrip_bezier_pen_bezier() {
        // Start with an elliptical pen, convert to BezierPath, then back to Pen.
        let original = Pen::circle(2.0);
        let bp = BezierPath::from(&original);
        let pen = Pen::try_from(&bp).expect("roundtrip should succeed");
        // The result is a polygonal pen (8 vertices from the circle approximation).
        match pen {
            Pen::Polygonal(verts) => {
                assert_eq!(verts.len(), 8);
                // All vertices should be approximately on the unit circle.
                for v in &verts {
                    let r = Vec2::from(*v).length();
                    assert!(
                        (r - 1.0).abs() < 0.01,
                        "vertex {v:?} not on unit circle: r = {r}"
                    );
                }
            }
            Pen::Elliptical(_) => panic!("expected polygonal after roundtrip"),
        }
    }
}
