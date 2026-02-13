//! Affine transform operations for `MetaPost` types.
//!
//! `MetaPost` provides these transform primitives:
//! - `shifted (dx, dy)` — translate
//! - `rotated angle` — rotate by degrees
//! - `scaled s` — uniform scale
//! - `xscaled s` — scale x only
//! - `yscaled s` — scale y only
//! - `slanted s` — horizontal shear
//! - `zscaled (a, b)` — complex multiplication (rotate + scale)
//! - `transformed T` — apply an arbitrary 6-component transform
//!
//! The [`Transformable`] trait provides a uniform interface for applying
//! transforms to all graphics types.

use crate::pen::convex_hull;
use crate::types::{
    FillObject, GraphicsObject, Knot, KnotDirection, Path, Pen, Picture, Point, Scalar,
    StrokeObject, TextObject, Transform, Vec2, NEAR_ZERO,
};

// ---------------------------------------------------------------------------
// Transformable trait
// ---------------------------------------------------------------------------

/// A type that can be transformed by an affine [`Transform`].
pub trait Transformable {
    /// Apply a transform, returning the transformed value.
    #[must_use]
    fn transformed(&self, t: &Transform) -> Self;
}

// ---------------------------------------------------------------------------
// Trait implementations
// ---------------------------------------------------------------------------

impl Transformable for Point {
    #[inline]
    fn transformed(&self, t: &Transform) -> Self {
        t.apply(*self)
    }
}

impl Transformable for Vec2 {
    /// Transform a vector (direction). Translation is ignored — only the
    /// linear part of the affine is applied.
    #[inline]
    fn transformed(&self, t: &Transform) -> Self {
        Self::new(
            t.txx.mul_add(self.x, t.txy * self.y),
            t.tyx.mul_add(self.x, t.tyy * self.y),
        )
    }
}

impl Transformable for KnotDirection {
    fn transformed(&self, t: &Transform) -> Self {
        match *self {
            Self::Explicit(p) => Self::Explicit(p.transformed(t)),
            Self::Given(angle) => {
                // Transform the direction vector, recompute the angle
                let v = Vec2::new(angle.cos(), angle.sin());
                let tv = v.transformed(t);
                let len = tv.length();
                if len < NEAR_ZERO {
                    // Degenerate transform collapsed the direction
                    Self::Curl(1.0)
                } else {
                    Self::Given(tv.y.atan2(tv.x))
                }
            }
            // Curl and Open are not affected by transforms
            other => other,
        }
    }
}

impl Transformable for Knot {
    fn transformed(&self, t: &Transform) -> Self {
        Self {
            point: self.point.transformed(t),
            left: self.left.transformed(t),
            right: self.right.transformed(t),
            left_tension: self.left_tension,
            right_tension: self.right_tension,
        }
    }
}

impl Transformable for Path {
    fn transformed(&self, t: &Transform) -> Self {
        let knots = self.knots.iter().map(|k| k.transformed(t)).collect();
        Self::from_knots(knots, self.is_cyclic)
    }
}

impl Transformable for Pen {
    fn transformed(&self, t: &Transform) -> Self {
        match self {
            Self::Elliptical(pen_t) => {
                // Compose: pen transform applied first, then the outer transform.
                Self::Elliptical(pen_t.then(t))
            }
            Self::Polygonal(vertices) => {
                let new_verts: Vec<Point> = vertices.iter().map(|v| v.transformed(t)).collect();
                // Re-run convex hull to maintain CCW invariant (a reflection
                // reverses winding order, for example).
                Self::Polygonal(convex_hull(&new_verts))
            }
        }
    }
}

impl Transformable for Transform {
    /// Compose: `self` applied first, then `t`.
    ///
    /// Equivalent to `self.then(t)`.
    #[inline]
    fn transformed(&self, t: &Transform) -> Self {
        self.then(t)
    }
}

impl Transformable for GraphicsObject {
    fn transformed(&self, t: &Transform) -> Self {
        match self {
            Self::Fill(fill) => Self::Fill(FillObject {
                path: fill.path.transformed(t),
                color: fill.color,
                pen: fill.pen.as_ref().map(|p| p.transformed(t)),
                line_join: fill.line_join,
                miter_limit: fill.miter_limit,
            }),
            Self::Stroke(stroke) => Self::Stroke(StrokeObject {
                path: stroke.path.transformed(t),
                pen: stroke.pen.transformed(t),
                color: stroke.color,
                dash: stroke.dash.clone().map(|mut d| {
                    // Scale dash pattern by sqrt of determinant magnitude
                    let scale = determinant(t).abs().sqrt();
                    for v in &mut d.dashes {
                        *v *= scale;
                    }
                    d.offset *= scale;
                    d
                }),
                line_cap: stroke.line_cap,
                line_join: stroke.line_join,
                miter_limit: stroke.miter_limit,
            }),
            Self::Text(text) => Self::Text(TextObject {
                text: text.text.clone(),
                font_name: text.font_name.clone(),
                font_size: text.font_size,
                color: text.color,
                transform: text.transform.transformed(t),
            }),
            Self::ClipStart(path) => Self::ClipStart(path.transformed(t)),
            Self::ClipEnd => Self::ClipEnd,
            Self::SetBoundsStart(path) => Self::SetBoundsStart(path.transformed(t)),
            Self::SetBoundsEnd => Self::SetBoundsEnd,
        }
    }
}

impl Transformable for Picture {
    fn transformed(&self, t: &Transform) -> Self {
        Self {
            objects: self.objects.iter().map(|obj| obj.transformed(t)).collect(),
        }
    }
}

// ---------------------------------------------------------------------------
// Standard transform constructors
// ---------------------------------------------------------------------------

/// Create a translation transform.
#[must_use]
pub const fn shifted(dx: Scalar, dy: Scalar) -> Transform {
    Transform {
        tx: dx,
        ty: dy,
        ..Transform::IDENTITY
    }
}

/// Create a rotation transform (angle in degrees).
#[must_use]
pub fn rotated(degrees: Scalar) -> Transform {
    let rad = degrees.to_radians();
    let c = rad.cos();
    let s = rad.sin();
    Transform {
        tx: 0.0,
        ty: 0.0,
        txx: c,
        txy: -s,
        tyx: s,
        tyy: c,
    }
}

/// Create a uniform scaling transform.
#[must_use]
pub const fn scaled(factor: Scalar) -> Transform {
    Transform {
        tx: 0.0,
        ty: 0.0,
        txx: factor,
        txy: 0.0,
        tyx: 0.0,
        tyy: factor,
    }
}

/// Create an x-only scaling transform.
#[must_use]
pub const fn xscaled(factor: Scalar) -> Transform {
    Transform {
        txx: factor,
        ..Transform::IDENTITY
    }
}

/// Create a y-only scaling transform.
#[must_use]
pub const fn yscaled(factor: Scalar) -> Transform {
    Transform {
        tyy: factor,
        ..Transform::IDENTITY
    }
}

/// Create a horizontal shear (slant) transform.
#[must_use]
pub const fn slanted(factor: Scalar) -> Transform {
    Transform {
        txy: factor,
        ..Transform::IDENTITY
    }
}

/// Create a complex-multiplication transform: `zscaled (a, b)`.
///
/// This simultaneously rotates and scales: the point (1, 0) maps to (a, b).
#[must_use]
pub fn zscaled(a: Scalar, b: Scalar) -> Transform {
    Transform {
        tx: 0.0,
        ty: 0.0,
        txx: a,
        txy: -b,
        tyx: b,
        tyy: a,
    }
}

// ---------------------------------------------------------------------------
// Transform utilities
// ---------------------------------------------------------------------------

/// Compute the inverse of a transform, if it exists.
///
/// Returns `None` if the transform is singular (determinant is zero).
#[must_use]
pub fn inverse(t: &Transform) -> Option<Transform> {
    let det = determinant(t);
    if det.abs() < NEAR_ZERO {
        return None;
    }
    let inv_det = 1.0 / det;
    Some(Transform {
        txx: t.tyy * inv_det,
        txy: -t.txy * inv_det,
        tyx: -t.tyx * inv_det,
        tyy: t.txx * inv_det,
        tx: t.txy.mul_add(t.ty, -(t.tyy * t.tx)) * inv_det,
        ty: t.tyx.mul_add(t.tx, -(t.txx * t.ty)) * inv_det,
    })
}

/// Determinant of a transform.
#[must_use]
pub fn determinant(t: &Transform) -> Scalar {
    t.txx.mul_add(t.tyy, -(t.txy * t.tyx))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::EPSILON;

    #[test]
    fn test_shifted() {
        let t = shifted(3.0, 4.0);
        let p = Point::ZERO.transformed(&t);
        assert!((p.x - 3.0).abs() < EPSILON);
        assert!((p.y - 4.0).abs() < EPSILON);
    }

    #[test]
    fn test_rotated_90() {
        let t = rotated(90.0);
        let p = Point::new(1.0, 0.0).transformed(&t);
        assert!(p.x.abs() < EPSILON);
        assert!((p.y - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_rotated_180() {
        let t = rotated(180.0);
        let p = Point::new(1.0, 0.0).transformed(&t);
        assert!((p.x + 1.0).abs() < EPSILON);
        assert!(p.y.abs() < EPSILON);
    }

    #[test]
    fn test_scaled() {
        let t = scaled(3.0);
        let p = Point::new(2.0, 5.0).transformed(&t);
        assert!((p.x - 6.0).abs() < EPSILON);
        assert!((p.y - 15.0).abs() < EPSILON);
    }

    #[test]
    fn test_xscaled() {
        let t = xscaled(2.0);
        let p = Point::new(3.0, 4.0).transformed(&t);
        assert!((p.x - 6.0).abs() < EPSILON);
        assert!((p.y - 4.0).abs() < EPSILON);
    }

    #[test]
    fn test_yscaled() {
        let t = yscaled(2.0);
        let p = Point::new(3.0, 4.0).transformed(&t);
        assert!((p.x - 3.0).abs() < EPSILON);
        assert!((p.y - 8.0).abs() < EPSILON);
    }

    #[test]
    fn test_slanted() {
        let t = slanted(1.0);
        let p = Point::new(0.0, 1.0).transformed(&t);
        // x' = 0 + 1*1 = 1, y' = 1
        assert!((p.x - 1.0).abs() < EPSILON);
        assert!((p.y - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_zscaled() {
        // zscaled (0, 1) is a 90-degree rotation
        let t = zscaled(0.0, 1.0);
        let p = Point::new(1.0, 0.0).transformed(&t);
        assert!(p.x.abs() < EPSILON);
        assert!((p.y - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_zscaled_scale_and_rotate() {
        // zscaled (1, 1) = scale by sqrt(2) and rotate 45 degrees
        let t = zscaled(1.0, 1.0);
        let p = Point::new(1.0, 0.0).transformed(&t);
        assert!((p.x - 1.0).abs() < EPSILON);
        assert!((p.y - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_compose_shift_then_rotate() {
        let s = shifted(1.0, 0.0);
        let r = rotated(90.0);
        let c = s.then(&r);
        // (0,0) → shifted → (1,0) → rotated 90 → (0,1)
        let p = Point::ZERO.transformed(&c);
        assert!(p.x.abs() < EPSILON);
        assert!((p.y - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_compose_rotate_then_shift() {
        let r = rotated(90.0);
        let s = shifted(1.0, 0.0);
        let c = r.then(&s);
        // (1,0) → rotated 90 → (0,1) → shifted → (1,1)
        let p = Point::new(1.0, 0.0).transformed(&c);
        assert!((p.x - 1.0).abs() < EPSILON);
        assert!((p.y - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_inverse_identity() {
        let inv = inverse(&Transform::IDENTITY).unwrap();
        let p = Point::new(5.0, 7.0).transformed(&inv);
        assert!((p.x - 5.0).abs() < EPSILON);
        assert!((p.y - 7.0).abs() < EPSILON);
    }

    #[test]
    fn test_inverse_shift() {
        let t = shifted(3.0, 4.0);
        let inv = inverse(&t).unwrap();
        let p = Point::new(3.0, 4.0).transformed(&inv);
        assert!(p.x.abs() < EPSILON);
        assert!(p.y.abs() < EPSILON);
    }

    #[test]
    fn test_inverse_scale() {
        let t = scaled(2.0);
        let inv = inverse(&t).unwrap();
        let p = Point::new(6.0, 8.0).transformed(&inv);
        assert!((p.x - 3.0).abs() < EPSILON);
        assert!((p.y - 4.0).abs() < EPSILON);
    }

    #[test]
    fn test_inverse_roundtrip() {
        let t = rotated(30.0).then(&shifted(5.0, -3.0));
        let inv = inverse(&t).unwrap();
        let original = Point::new(7.0, 11.0);
        let transformed = original.transformed(&t);
        let back = transformed.transformed(&inv);
        assert!((back.x - original.x).abs() < 1e-10);
        assert!((back.y - original.y).abs() < 1e-10);
    }

    #[test]
    fn test_inverse_singular() {
        // Zero transform is singular
        let t = scaled(0.0);
        assert!(inverse(&t).is_none());
    }

    #[test]
    fn test_determinant() {
        assert!((determinant(&Transform::IDENTITY) - 1.0).abs() < EPSILON);
        assert!((determinant(&scaled(3.0)) - 9.0).abs() < EPSILON);
        assert!((determinant(&rotated(45.0)) - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_transform_path() {
        let path = Path::from_knots(
            vec![
                Knot::with_controls(Point::ZERO, Point::ZERO, Point::new(1.0, 0.0)),
                Knot::with_controls(
                    Point::new(3.0, 0.0),
                    Point::new(2.0, 0.0),
                    Point::new(3.0, 0.0),
                ),
            ],
            false,
        );
        let t = shifted(10.0, 20.0);
        let tp = path.transformed(&t);
        assert!((tp.knots[0].point.x - 10.0).abs() < EPSILON);
        assert!((tp.knots[0].point.y - 20.0).abs() < EPSILON);
        assert!((tp.knots[1].point.x - 13.0).abs() < EPSILON);
    }

    #[test]
    fn test_transform_pen_elliptical() {
        let pen = Pen::circle(2.0);
        let t = scaled(3.0);
        let tp = pen.transformed(&t);
        match tp {
            Pen::Elliptical(t2) => {
                // Circle of diameter 2 scaled by 3 = circle of diameter 6 (radius 3)
                assert!((t2.txx - 3.0).abs() < EPSILON);
                assert!((t2.tyy - 3.0).abs() < EPSILON);
            }
            Pen::Polygonal(_) => panic!("expected elliptical"),
        }
    }

    #[test]
    fn test_transform_vec_ignores_translation() {
        let t = shifted(100.0, 200.0);
        let v = Vec2::new(1.0, 0.0).transformed(&t);
        assert!((v.x - 1.0).abs() < EPSILON);
        assert!(v.y.abs() < EPSILON);
    }

    #[test]
    fn test_knot_direction_given_degenerate() {
        // A degenerate transform that collapses a direction should produce Curl(1.0)
        let t = Transform {
            txx: 0.0,
            txy: 0.0,
            tyx: 0.0,
            tyy: 0.0,
            tx: 5.0,
            ty: 5.0,
        };
        let dir = KnotDirection::Given(1.0);
        let result = dir.transformed(&t);
        assert!(matches!(result, KnotDirection::Curl(c) if (c - 1.0).abs() < EPSILON));
    }
}
