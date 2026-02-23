//! Core types shared across the `PostMeta` system.

use std::fmt;
use std::ops;
use std::sync::Arc;

use crate::math;
use crate::path::Path;

// ---------------------------------------------------------------------------
// Scalar
// ---------------------------------------------------------------------------

/// Convenience alias. `MetaPost` historically used 16.16 fixed-point;
/// we use f64 for compatibility and WASM support.
pub type Scalar = f64;

/// Tolerance for floating-point comparisons.
pub const EPSILON: Scalar = 1.0 / 65536.0;

/// Near-zero guard for avoiding division by zero or singularity.
///
/// Used as a denominator check / vector-length check where we want to
/// detect degenerate transforms, zero-length vectors, etc.
pub const NEAR_ZERO: Scalar = 1e-30;

/// Convert a segment index to a path time parameter.
///
/// Path operations use `f64` time parameters where integer values correspond
/// to knot indices. Segment counts in any practical path are far below 2^52,
/// so no precision is lost.
#[expect(
    clippy::cast_precision_loss,
    reason = "path segment counts are far below 2^52"
)]
#[must_use]
pub const fn index_to_scalar(i: usize) -> Scalar {
    i as Scalar
}

/// Convert a non-negative path time parameter to a segment index.
///
/// The caller must ensure `t >= 0.0`. Values are floored before conversion.
#[expect(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "path time parameters are non-negative and small"
)]
#[must_use]
pub fn scalar_to_index(t: Scalar) -> usize {
    t.floor() as usize
}

// ---------------------------------------------------------------------------
// Point
// ---------------------------------------------------------------------------

/// A 2D point.
///
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
    #[must_use]
    pub const fn new(x: f64, y: f64) -> Self {
        Self { x, y }
    }

    /// Linearly interpolate between `self` and `other`.
    ///
    /// `t = 0` returns `self`, `t = 1` returns `other`.
    #[must_use]
    pub fn lerp(self, other: Self, t: Scalar) -> Self {
        Self::new(
            t.mul_add(other.x - self.x, self.x),
            t.mul_add(other.y - self.y, self.y),
        )
    }
}

impl fmt::Debug for Point {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({:?}, {:?})", self.x, self.y)
    }
}

/// `Point + Vec2 = Point` (translate a point by a displacement).
impl ops::Add<Vec2> for Point {
    type Output = Self;

    fn add(self, rhs: Vec2) -> Self {
        Self {
            x: self.x + rhs.x,
            y: self.y + rhs.y,
        }
    }
}

/// `Point - Vec2 = Point` (translate a point by the negated displacement).
impl ops::Sub<Vec2> for Point {
    type Output = Self;

    fn sub(self, rhs: Vec2) -> Self {
        Self {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
        }
    }
}

/// `Point - Point = Vec2` (displacement between two points).
impl ops::Sub for Point {
    type Output = Vec2;

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
/// `Vec2` represents a direction and magnitude, not a location.
#[derive(Clone, Copy, Default, Debug, PartialEq)]
pub struct Vec2 {
    pub x: f64,
    pub y: f64,
}

impl Vec2 {
    /// The zero vector.
    pub const ZERO: Self = Self { x: 0.0, y: 0.0 };

    /// Create a new vector.
    #[must_use]
    pub const fn new(x: f64, y: f64) -> Self {
        Self { x, y }
    }

    /// Euclidean length (magnitude).
    #[must_use]
    pub fn length(self) -> f64 {
        self.x.hypot(self.y)
    }

    /// Angle in radians, measured counter-clockwise from the positive x-axis.
    #[must_use]
    pub fn direction(self) -> Scalar {
        let angle = self.y.atan2(self.x);
        // Normalize to (-pi, pi]
        math::normalize_angle(angle)
    }

    // Angle from `self` to `other`, in the range (-pi, pi].
    #[must_use]
    pub fn angle_to(self, other: Self) -> Scalar {
        let diff = other.direction() - self.direction();
        math::normalize_angle(diff)
    }
}

/// Convert a point to a [`Vec2`] (displacement from the origin).
impl From<Point> for Vec2 {
    fn from(p: Point) -> Self {
        Self { x: p.x, y: p.y }
    }
}

/// `Vec2 + Vec2`.
impl ops::Add for Vec2 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self {
            x: self.x + rhs.x,
            y: self.y + rhs.y,
        }
    }
}

/// `Vec2 - Vec2`.
impl ops::Sub for Vec2 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Self {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
        }
    }
}

/// `-Vec2` (negate).
impl ops::Neg for Vec2 {
    type Output = Self;

    fn neg(self) -> Self {
        Self {
            x: -self.x,
            y: -self.y,
        }
    }
}

/// `Vec2 * Scalar` (scale).
impl ops::Mul<Scalar> for Vec2 {
    type Output = Self;

    fn mul(self, rhs: Scalar) -> Self {
        Self {
            x: self.x * rhs,
            y: self.y * rhs,
        }
    }
}

/// `Scalar * Vec2` (scale).
impl ops::Mul<Vec2> for Scalar {
    type Output = Vec2;

    fn mul(self, rhs: Vec2) -> Vec2 {
        Vec2 {
            x: self * rhs.x,
            y: self * rhs.y,
        }
    }
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

    #[must_use]
    pub const fn new(r: Scalar, g: Scalar, b: Scalar) -> Self {
        Self { r, g, b }
    }
}

// ---------------------------------------------------------------------------
// LineCap / LineJoin
// ---------------------------------------------------------------------------

/// Stroke line-cap styles.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum LineCap {
    Butt = 0,
    #[default]
    Round = 1,
    Square = 2,
}

/// Convert a `Scalar` to a `LineCap` by interpreting it as an integer code.
#[expect(
    clippy::cast_possible_truncation,
    reason = "linecap/linejoin values are small integers (0, 1, 2)"
)]
impl From<Scalar> for LineCap {
    fn from(v: Scalar) -> Self {
        match v as i32 {
            0 => Self::Butt,
            2 => Self::Square,
            _ => Self::Round,
        }
    }
}

/// Stroke line-join styles.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum LineJoin {
    Miter = 0,
    #[default]
    Round = 1,
    Bevel = 2,
}

impl From<Scalar> for LineJoin {
    #[expect(
        clippy::cast_possible_truncation,
        reason = "linecap/linejoin values are small integers (0, 1, 2)"
    )]
    fn from(v: Scalar) -> Self {
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
    /// A specific direction angle in **radians**.
    ///
    /// Note: degrees are used externally, but angles are converted to
    /// radians at parse time. All internal computations use radians.
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

/// A single knot in a path.
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
}

impl Default for Pen {
    /// The default pen is a circle with diameter 0.5.
    fn default() -> Self {
        Self::circle(0.5)
    }
}

// ---------------------------------------------------------------------------
// Transform
// ---------------------------------------------------------------------------

/// A transform with named components.
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

    /// Compose two transforms: `self` applied first, then `other`.
    ///
    /// Equivalent to matrix multiplication `other * self`.
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
    #[must_use]
    pub fn apply(&self, p: Point) -> Point {
        Point::new(
            self.txy.mul_add(p.y, self.txx.mul_add(p.x, self.tx)),
            self.tyy.mul_add(p.y, self.tyx.mul_add(p.x, self.ty)),
        )
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

/// Precomputed text dimensions at the nominal font size.
///
/// Populated by the interpreter from real font metrics (via `FontProvider`)
/// or a heuristic fallback.  The graphics layer trusts these values and
/// never recomputes them — it simply uses them for bounding-box and layout.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct TextMetrics {
    /// Total advance width in points (character advances + kerning).
    pub width: Scalar,
    /// Ascender above the baseline, in points (positive upward).
    pub height: Scalar,
    /// Descender below the baseline, in points (positive downward).
    pub depth: Scalar,
}

/// A text label.
#[derive(Debug, Clone, PartialEq)]
pub struct TextObject {
    pub text: Arc<str>,
    pub font_name: Arc<str>,
    pub font_size: Scalar,
    pub metrics: TextMetrics,
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
    pub fn merge(&mut self, other: Self) {
        self.objects.extend(other.objects);
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
    fn linecap_from_scalar() {
        assert_eq!(LineCap::from(0.0), LineCap::Butt);
        assert_eq!(LineCap::from(1.0), LineCap::Round);
        assert_eq!(LineCap::from(2.0), LineCap::Square);
        assert_eq!(LineCap::from(99.0), LineCap::Round);
    }

    #[test]
    fn linejoin_from_scalar() {
        assert_eq!(LineJoin::from(0.0), LineJoin::Miter);
        assert_eq!(LineJoin::from(1.0), LineJoin::Round);
        assert_eq!(LineJoin::from(2.0), LineJoin::Bevel);
        assert_eq!(LineJoin::from(99.0), LineJoin::Round);
    }

    #[test]
    fn test_vec2_angle_to() {
        let a = Vec2::new(1.0, 0.0);
        let b = Vec2::new(0.0, 1.0);
        let ta = a.angle_to(b);
        assert!((ta - std::f64::consts::FRAC_PI_2).abs() < EPSILON);

        let ta2 = b.angle_to(a);
        assert!((ta2 + std::f64::consts::FRAC_PI_2).abs() < EPSILON);
    }

    #[test]
    fn test_vec2_angle_to_straight() {
        let a = Vec2::new(1.0, 0.0);
        let ta = a.angle_to(a);
        assert!(ta.abs() < EPSILON);
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
        let p = t.apply(Point::new(1.0, 1.0));
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
        p1.merge(p2);
        assert_eq!(p1.objects.len(), 2);
    }
}
