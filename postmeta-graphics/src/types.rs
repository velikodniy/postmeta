//! Core types shared across the `PostMeta` system.
//!
//! These types define the fundamental data structures for the `MetaPost`
//! graphics model: paths, pens, pictures, transforms, and colors.

use std::sync::Arc;

use kurbo::{Affine, Point};

// ---------------------------------------------------------------------------
// Scalar
// ---------------------------------------------------------------------------

/// Convenience alias. `MetaPost` historically used 16.16 fixed-point;
/// we use f64 for modern compatibility with `kurbo` and WASM.
pub type Scalar = f64;

/// Tolerance for floating-point comparisons.
pub const EPSILON: Scalar = 1.0 / 65536.0;

/// Maximum coordinate value (matches `MetaPost`'s `infinity`).
pub const INFINITY_VAL: Scalar = 4_095.999_98;

/// Convert degrees to radians.
#[inline]
pub const fn deg_to_rad(deg: Scalar) -> Scalar {
    deg.to_radians()
}

/// Convert radians to degrees.
#[inline]
pub const fn rad_to_deg(rad: Scalar) -> Scalar {
    rad.to_degrees()
}

// ---------------------------------------------------------------------------
// Color
// ---------------------------------------------------------------------------

/// RGB color with components in [0, 1].
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Color {
    pub r: Scalar,
    pub g: Scalar,
    pub b: Scalar,
}

impl Color {
    pub const BLACK: Self = Self {
        r: 0.0,
        g: 0.0,
        b: 0.0,
    };
    pub const WHITE: Self = Self {
        r: 1.0,
        g: 1.0,
        b: 1.0,
    };

    #[inline]
    pub const fn new(r: Scalar, g: Scalar, b: Scalar) -> Self {
        Self { r, g, b }
    }
}

impl Default for Color {
    fn default() -> Self {
        Self::BLACK
    }
}

// ---------------------------------------------------------------------------
// LineCap / LineJoin
// ---------------------------------------------------------------------------

/// Stroke line-cap styles (matches SVG / PostScript).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum LineCap {
    Butt = 0,
    #[default]
    Round = 1,
    Square = 2,
}

impl LineCap {
    pub const fn from_f64(v: Scalar) -> Self {
        match v as i32 {
            0 => Self::Butt,
            2 => Self::Square,
            _ => Self::Round,
        }
    }
}

/// Stroke line-join styles (matches SVG / PostScript).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum LineJoin {
    Miter = 0,
    #[default]
    Round = 1,
    Bevel = 2,
}

impl LineJoin {
    pub const fn from_f64(v: Scalar) -> Self {
        match v as i32 {
            0 => Self::Miter,
            2 => Self::Bevel,
            _ => Self::Round,
        }
    }
}

// ---------------------------------------------------------------------------
// DashPattern
// ---------------------------------------------------------------------------

/// A dash pattern: alternating on/off lengths with an offset.
#[derive(Debug, Clone, PartialEq)]
pub struct DashPattern {
    /// Alternating on, off, on, off, ... lengths.
    pub dashes: Vec<Scalar>,
    /// Starting offset into the pattern.
    pub offset: Scalar,
}

// ---------------------------------------------------------------------------
// KnotType — direction constraint at a path knot
// ---------------------------------------------------------------------------

/// Direction/control constraint for one side of a path knot.
#[derive(Debug, Clone, Copy, PartialEq, Default)]
pub enum KnotDirection {
    /// Control point has been explicitly computed as a Bezier handle.
    Explicit(Point),
    /// A specific direction angle (in degrees).
    Given(Scalar),
    /// Curl parameter (default 1.0 at open-path endpoints).
    Curl(Scalar),
    /// Let the algorithm choose the direction.
    #[default]
    Open,
}

// ---------------------------------------------------------------------------
// Knot
// ---------------------------------------------------------------------------

/// A single knot in a `MetaPost` path.
///
/// Each knot has a point plus left (incoming) and right (outgoing)
/// direction constraints and tension values.
#[derive(Debug, Clone, PartialEq)]
pub struct Knot {
    /// The on-curve point.
    pub point: Point,
    /// Incoming (left) direction constraint.
    pub left: KnotDirection,
    /// Outgoing (right) direction constraint.
    pub right: KnotDirection,
    /// Tension on the incoming side (default 1.0; negative = "at least").
    pub left_tension: Scalar,
    /// Tension on the outgoing side (default 1.0; negative = "at least").
    pub right_tension: Scalar,
}

impl Knot {
    /// Create a new knot at the given point with default (open) constraints.
    pub const fn new(point: Point) -> Self {
        Self {
            point,
            left: KnotDirection::Open,
            right: KnotDirection::Open,
            left_tension: 1.0,
            right_tension: 1.0,
        }
    }

    /// Create a knot with explicit Bezier control points already computed.
    pub const fn with_controls(point: Point, left_cp: Point, right_cp: Point) -> Self {
        Self {
            point,
            left: KnotDirection::Explicit(left_cp),
            right: KnotDirection::Explicit(right_cp),
            left_tension: 1.0,
            right_tension: 1.0,
        }
    }
}

// ---------------------------------------------------------------------------
// Path
// ---------------------------------------------------------------------------

/// A `MetaPost` path: a sequence of knots, optionally cyclic.
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

    /// The "length" of the path in `MetaPost` terms (number of segments).
    pub fn length(&self) -> usize {
        self.num_segments()
    }
}

impl Default for Path {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Pen
// ---------------------------------------------------------------------------

/// A `MetaPost` pen: either elliptical (common) or polygonal.
#[derive(Debug, Clone, PartialEq)]
pub enum Pen {
    /// An elliptical pen defined by an affine transform of the unit circle.
    /// The transform maps the unit circle to the pen shape.
    Elliptical(Affine),
    /// A convex polygonal pen defined by its vertices in counter-clockwise
    /// order.
    Polygonal(Vec<Point>),
}

impl Pen {
    /// Create a circular pen with the given diameter centered at origin.
    pub fn circle(diameter: Scalar) -> Self {
        let r = diameter / 2.0;
        Self::Elliptical(Affine::scale(r))
    }

    /// The default pen: a circle of diameter 0.5bp.
    pub fn default_pen() -> Self {
        Self::circle(0.5)
    }
}

impl Default for Pen {
    fn default() -> Self {
        Self::circle(0.0)
    }
}

// ---------------------------------------------------------------------------
// Transform (MetaPost-level, 6-component)
// ---------------------------------------------------------------------------

/// A `MetaPost` transform with named components.
///
/// Maps point (x, y) to:
///   (tx + txx*x + txy*y, ty + tyx*x + tyy*y)
///
/// This directly wraps `kurbo::Affine` but with `MetaPost` naming.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Transform {
    pub tx: Scalar,
    pub ty: Scalar,
    pub txx: Scalar,
    pub txy: Scalar,
    pub tyx: Scalar,
    pub tyy: Scalar,
}

impl Transform {
    pub const IDENTITY: Self = Self {
        tx: 0.0,
        ty: 0.0,
        txx: 1.0,
        txy: 0.0,
        tyx: 0.0,
        tyy: 1.0,
    };

    /// Convert to a kurbo `Affine`.
    ///
    /// kurbo Affine coefficients: [a, b, c, d, e, f]
    /// mapping: x' = a*x + c*y + e,  y' = b*x + d*y + f
    #[inline]
    pub const fn to_affine(self) -> Affine {
        Affine::new([self.txx, self.tyx, self.txy, self.tyy, self.tx, self.ty])
    }

    /// Create from a kurbo `Affine`.
    #[inline]
    pub const fn from_affine(a: Affine) -> Self {
        let c = a.as_coeffs();
        Self {
            txx: c[0],
            tyx: c[1],
            txy: c[2],
            tyy: c[3],
            tx: c[4],
            ty: c[5],
        }
    }

    /// Apply this transform to a point.
    #[inline]
    pub fn apply_to_point(&self, p: Point) -> Point {
        Point::new(
            self.txy.mul_add(p.y, self.txx.mul_add(p.x, self.tx)),
            self.tyy.mul_add(p.y, self.tyx.mul_add(p.x, self.ty)),
        )
    }
}

impl Default for Transform {
    fn default() -> Self {
        Self::IDENTITY
    }
}

// ---------------------------------------------------------------------------
// Picture and GraphicsObject
// ---------------------------------------------------------------------------

/// A single graphical object in a picture.
#[derive(Debug, Clone, PartialEq)]
pub enum GraphicsObject {
    /// A filled region (path must be cyclic).
    Fill(FillObject),
    /// A stroked path.
    Stroke(StrokeObject),
    /// A text label.
    Text(TextObject),
    /// Begin a clipping region.
    ClipStart(Path),
    /// End the most recent clipping region.
    ClipEnd,
    /// Begin a bounding-box override region.
    SetBoundsStart(Path),
    /// End the most recent bounding-box override.
    SetBoundsEnd,
}

/// A filled contour.
#[derive(Debug, Clone, PartialEq)]
pub struct FillObject {
    pub path: Path,
    pub color: Color,
    /// Optional pen for "filldraw" (stroke the contour too).
    pub pen: Option<Pen>,
    pub line_join: LineJoin,
    pub miter_limit: Scalar,
}

/// A stroked path.
#[derive(Debug, Clone, PartialEq)]
pub struct StrokeObject {
    pub path: Path,
    pub pen: Pen,
    pub color: Color,
    pub dash: Option<DashPattern>,
    pub line_cap: LineCap,
    pub line_join: LineJoin,
    pub miter_limit: Scalar,
}

/// A text label.
#[derive(Debug, Clone, PartialEq)]
pub struct TextObject {
    pub text: Arc<str>,
    pub font_name: Arc<str>,
    pub font_size: Scalar,
    pub color: Color,
    pub transform: Transform,
}

/// An ordered collection of graphical objects.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Picture {
    pub objects: Vec<GraphicsObject>,
}

impl Picture {
    pub const fn new() -> Self {
        Self {
            objects: Vec::new(),
        }
    }

    pub fn push(&mut self, obj: GraphicsObject) {
        self.objects.push(obj);
    }

    /// Append all objects from another picture.
    pub fn merge(&mut self, other: &Self) {
        self.objects.extend(other.objects.iter().cloned());
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
#[allow(clippy::float_cmp)]
mod tests {
    use super::*;

    #[test]
    fn color_defaults() {
        assert_eq!(Color::default(), Color::BLACK);
        assert_eq!(Color::WHITE, Color::new(1.0, 1.0, 1.0));
    }

    #[test]
    fn linecap_from_f64() {
        assert_eq!(LineCap::from_f64(0.0), LineCap::Butt);
        assert_eq!(LineCap::from_f64(1.0), LineCap::Round);
        assert_eq!(LineCap::from_f64(2.0), LineCap::Square);
        assert_eq!(LineCap::from_f64(99.0), LineCap::Round);
    }

    #[test]
    fn linejoin_from_f64() {
        assert_eq!(LineJoin::from_f64(0.0), LineJoin::Miter);
        assert_eq!(LineJoin::from_f64(1.0), LineJoin::Round);
        assert_eq!(LineJoin::from_f64(2.0), LineJoin::Bevel);
    }

    #[test]
    fn knot_defaults() {
        let k = Knot::new(Point::new(1.0, 2.0));
        assert_eq!(k.point, Point::new(1.0, 2.0));
        assert_eq!(k.left, KnotDirection::Open);
        assert_eq!(k.right, KnotDirection::Open);
        assert_eq!(k.left_tension, 1.0);
        assert_eq!(k.right_tension, 1.0);
    }

    #[test]
    fn path_num_segments() {
        // Empty path
        let p = Path::new();
        assert_eq!(p.num_segments(), 0);

        // Open path with 3 knots = 2 segments
        let p = Path::from_knots(
            vec![
                Knot::new(Point::ZERO),
                Knot::new(Point::new(1.0, 0.0)),
                Knot::new(Point::new(1.0, 1.0)),
            ],
            false,
        );
        assert_eq!(p.num_segments(), 2);

        // Cyclic path with 3 knots = 3 segments
        let p = Path::from_knots(
            vec![
                Knot::new(Point::ZERO),
                Knot::new(Point::new(1.0, 0.0)),
                Knot::new(Point::new(1.0, 1.0)),
            ],
            true,
        );
        assert_eq!(p.num_segments(), 3);
    }

    #[test]
    fn transform_identity_roundtrip() {
        let t = Transform::IDENTITY;
        let a = t.to_affine();
        let t2 = Transform::from_affine(a);
        assert_eq!(t, t2);
    }

    #[test]
    fn transform_apply() {
        let t = Transform {
            tx: 10.0,
            ty: 20.0,
            txx: 2.0,
            txy: 0.0,
            tyx: 0.0,
            tyy: 3.0,
        };
        let p = t.apply_to_point(Point::new(1.0, 1.0));
        assert!((p.x - 12.0).abs() < EPSILON);
        assert!((p.y - 23.0).abs() < EPSILON);
    }

    #[test]
    fn pen_circle() {
        let p = Pen::circle(2.0);
        match p {
            Pen::Elliptical(a) => {
                let c = a.as_coeffs();
                assert!((c[0] - 1.0).abs() < EPSILON); // scale x
                assert!((c[3] - 1.0).abs() < EPSILON); // scale y
            }
            Pen::Polygonal(_) => panic!("expected elliptical"),
        }
    }

    #[test]
    fn picture_merge() {
        let mut p1 = Picture::new();
        p1.push(GraphicsObject::ClipEnd);
        let mut p2 = Picture::new();
        p2.push(GraphicsObject::SetBoundsEnd);
        p1.merge(&p2);
        assert_eq!(p1.objects.len(), 2);
    }

    #[test]
    fn deg_rad_roundtrip() {
        let deg = 45.0;
        let rad = deg_to_rad(deg);
        let deg2 = rad_to_deg(rad);
        assert!((deg - deg2).abs() < EPSILON);
    }
}
