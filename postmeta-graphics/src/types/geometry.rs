//! Geometric primitives: scalars, points, and vectors.

use std::fmt;
use std::ops;

use crate::math;

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

/// Convert a [`Vec2`] to a point (treating it as a displacement from the origin).
impl From<Vec2> for Point {
    fn from(v: Vec2) -> Self {
        Self { x: v.x, y: v.y }
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
    fn point_from_vec2() {
        let v = Vec2::new(3.0, 4.0);
        let p = Point::from(v);
        assert_eq!(p.x, 3.0);
        assert_eq!(p.y, 4.0);
    }
}
