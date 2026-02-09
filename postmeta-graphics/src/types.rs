//! Core types shared across the `PostMeta` system.
//!
//! These types define the fundamental data structures for the `MetaPost`
//! graphics model: paths, pens, pictures, transforms, and colors.

use std::fmt;
use std::ops;
use std::sync::Arc;

// ---------------------------------------------------------------------------
// Point
// ---------------------------------------------------------------------------

/// A 2D point.
///
/// This is the fundamental position type used throughout `PostMeta`.
/// Points represent locations; for displacements use [`Vec2`].
#[derive(Clone, Copy, Default, PartialEq)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

impl Point {
    /// The origin (0, 0).
    pub const ZERO: Self = Self { x: 0.0, y: 0.0 };

    /// Create a new point.
    #[inline]
    #[must_use]
    pub const fn new(x: f64, y: f64) -> Self {
        Self { x, y }
    }

    /// Convert this point to a [`Vec2`] (displacement from the origin).
    #[inline]
    #[must_use]
    pub const fn to_vec2(self) -> Vec2 {
        Vec2 {
            x: self.x,
            y: self.y,
        }
    }
}

impl fmt::Debug for Point {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({:?}, {:?})", self.x, self.y)
    }
}

/// `Point - Point = Vec2` (displacement between two points).
impl ops::Sub for Point {
    type Output = Vec2;

    #[inline]
    fn sub(self, rhs: Self) -> Vec2 {
        Vec2 {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
        }
    }
}

// ---------------------------------------------------------------------------
// Vec2
// ---------------------------------------------------------------------------

/// A 2D vector (displacement).
///
/// Unlike [`Point`], a `Vec2` represents a direction and magnitude,
/// not a location. `Point - Point` yields a `Vec2`.
#[derive(Clone, Copy, Default, Debug, PartialEq)]
pub struct Vec2 {
    pub x: f64,
    pub y: f64,
}

impl Vec2 {
    /// The zero vector.
    pub const ZERO: Self = Self { x: 0.0, y: 0.0 };

    /// Create a new vector.
    #[inline]
    #[must_use]
    pub const fn new(x: f64, y: f64) -> Self {
        Self { x, y }
    }

    /// Euclidean length (magnitude).
    #[inline]
    #[must_use]
    pub fn length(self) -> f64 {
        self.x.hypot(self.y)
    }
}

// ---------------------------------------------------------------------------
// Error
// ---------------------------------------------------------------------------

/// Errors returned by graphics operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GraphicsError {
    /// A path has unresolved knot directions (not yet processed by Hobby's
    /// algorithm).
    UnresolvedPath {
        /// Index of the knot with the unresolved direction.
        knot: usize,
        /// Which side of the knot is unresolved (`"left"` or `"right"`).
        side: &'static str,
    },
    /// `makepen` was called with an invalid path.
    InvalidPen(&'static str),
}

impl fmt::Display for GraphicsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnresolvedPath { knot, side } => {
                write!(
                    f,
                    "path not fully resolved: knot {knot} {side} direction is not Explicit"
                )
            }
            Self::InvalidPen(msg) => write!(f, "invalid pen: {msg}"),
        }
    }
}

impl std::error::Error for GraphicsError {}

// ---------------------------------------------------------------------------
// Scalar
// ---------------------------------------------------------------------------

/// Convenience alias. `MetaPost` historically used 16.16 fixed-point;
/// we use f64 for modern compatibility and WASM support.
pub type Scalar = f64;

/// Tolerance for floating-point comparisons.
pub const EPSILON: Scalar = 1.0 / 65536.0;

/// Maximum coordinate value (matches `MetaPost`'s `infinity`).
pub const INFINITY_VAL: Scalar = 4_095.999_98;

/// Convert a segment index to a path time parameter.
///
/// Path operations use `f64` time parameters where integer values correspond
/// to knot indices. Segment counts in any practical path are far below 2^52,
/// so no precision is lost.
#[inline]
#[must_use]
#[expect(
    clippy::cast_precision_loss,
    reason = "path segment counts are far below 2^52"
)]
pub const fn index_to_scalar(i: usize) -> Scalar {
    i as Scalar
}

/// Convert a non-negative path time parameter to a segment index.
///
/// The caller must ensure `t >= 0.0`. Values are floored before conversion.
#[inline]
#[must_use]
#[expect(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "path time parameters are non-negative and small"
)]
pub fn scalar_to_index(t: Scalar) -> usize {
    t.floor() as usize
}

/// Convert degrees to radians.
#[inline]
#[must_use]
pub const fn deg_to_rad(deg: Scalar) -> Scalar {
    deg.to_radians()
}

/// Convert radians to degrees.
#[inline]
#[must_use]
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
    #[must_use]
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
    #[expect(
        clippy::cast_possible_truncation,
        reason = "linecap/linejoin values are small integers (0, 1, 2)"
    )]
    #[must_use]
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
    #[expect(
        clippy::cast_possible_truncation,
        reason = "linecap/linejoin values are small integers (0, 1, 2)"
    )]
    #[must_use]
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
    /// A specific direction angle (in radians).
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
    #[must_use]
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
    #[must_use]
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
    #[must_use]
    pub const fn new() -> Self {
        Self {
            knots: Vec::new(),
            is_cyclic: false,
        }
    }

    /// Create a path from knots.
    #[must_use]
    pub const fn from_knots(knots: Vec<Knot>, is_cyclic: bool) -> Self {
        Self { knots, is_cyclic }
    }

    /// Number of segments in the path.
    /// For a cyclic path with N knots, there are N segments.
    /// For an open path with N knots, there are N-1 segments.
    #[must_use]
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
    #[must_use]
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
        Self::Elliptical(Transform::scale(r))
    }

    /// The default pen: a circle of diameter 0.5bp.
    #[must_use]
    pub const fn default_pen() -> Self {
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

    /// The zero transform (all components zero). Used for the null pen.
    pub const ZERO: Self = Self {
        tx: 0.0,
        ty: 0.0,
        txx: 0.0,
        txy: 0.0,
        tyx: 0.0,
        tyy: 0.0,
    };

    /// A uniform scale transform.
    #[inline]
    #[must_use]
    pub const fn scale(s: Scalar) -> Self {
        Self {
            txx: s,
            tyy: s,
            ..Self::IDENTITY
        }
    }

    /// Compose two transforms: `self` applied first, then `other`.
    ///
    /// Equivalent to matrix multiplication `other * self`.
    #[inline]
    #[must_use]
    pub fn then(&self, other: &Self) -> Self {
        Self {
            txx: other.txx.mul_add(self.txx, other.txy * self.tyx),
            txy: other.txx.mul_add(self.txy, other.txy * self.tyy),
            tyx: other.tyx.mul_add(self.txx, other.tyy * self.tyx),
            tyy: other.tyx.mul_add(self.txy, other.tyy * self.tyy),
            tx: other
                .txx
                .mul_add(self.tx, other.txy.mul_add(self.ty, other.tx)),
            ty: other
                .tyx
                .mul_add(self.tx, other.tyy.mul_add(self.ty, other.ty)),
        }
    }

    /// Apply this transform to a point.
    #[inline]
    #[must_use]
    pub fn apply_to_point(&self, p: Point) -> Point {
        Point::new(
            self.txy.mul_add(p.y, self.txx.mul_add(p.x, self.tx)),
            self.tyy.mul_add(p.y, self.tyx.mul_add(p.x, self.ty)),
        )
    }

    /// Extract the six coefficients in row-major order:
    /// `[txx, txy, tyx, tyy, tx, ty]`.
    #[inline]
    #[must_use]
    pub const fn as_coeffs(&self) -> [Scalar; 6] {
        [self.txx, self.txy, self.tyx, self.tyy, self.tx, self.ty]
    }
}

/// `Transform * Transform` composes transforms (apply left, then right).
impl ops::Mul for Transform {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        self.then(&rhs)
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
    #[must_use]
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
#[expect(
    clippy::float_cmp,
    reason = "exact float comparisons are intentional in tests"
)]
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
    fn transform_compose_identity() {
        let t = Transform {
            tx: 1.0,
            ty: 2.0,
            txx: 3.0,
            txy: 4.0,
            tyx: 5.0,
            tyy: 6.0,
        };
        // Composing with identity should be a no-op
        let r = t.then(&Transform::IDENTITY);
        assert_eq!(t, r);
        let r = Transform::IDENTITY.then(&t);
        assert_eq!(t, r);
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
