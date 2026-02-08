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

use kurbo::{Point, Vec2};

use crate::types::{
    Color, FillObject, GraphicsObject, Knot, KnotDirection, Path, Pen, Picture, Scalar,
    StrokeObject, TextObject, Transform,
};

// ---------------------------------------------------------------------------
// Standard transform constructors
// ---------------------------------------------------------------------------

/// Create a translation transform.
pub const fn shifted(dx: Scalar, dy: Scalar) -> Transform {
    Transform {
        tx: dx,
        ty: dy,
        ..Transform::IDENTITY
    }
}

/// Create a rotation transform (angle in degrees).
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
pub const fn xscaled(factor: Scalar) -> Transform {
    Transform {
        txx: factor,
        ..Transform::IDENTITY
    }
}

/// Create a y-only scaling transform.
pub const fn yscaled(factor: Scalar) -> Transform {
    Transform {
        tyy: factor,
        ..Transform::IDENTITY
    }
}

/// Create a horizontal shear (slant) transform.
pub const fn slanted(factor: Scalar) -> Transform {
    Transform {
        txy: factor,
        ..Transform::IDENTITY
    }
}

/// Create a complex-multiplication transform: `zscaled (a, b)`.
///
/// This simultaneously rotates and scales: the point (1, 0) maps to (a, b).
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
// Transform composition
// ---------------------------------------------------------------------------

/// Compose two transforms: apply `first`, then `second`.
pub fn compose(first: &Transform, second: &Transform) -> Transform {
    let a = first.to_affine();
    let b = second.to_affine();
    Transform::from_affine(b * a)
}

/// Compute the inverse of a transform, if it exists.
///
/// Returns `None` if the transform is singular (determinant is zero).
pub fn inverse(t: &Transform) -> Option<Transform> {
    let det = t.txx.mul_add(t.tyy, -(t.txy * t.tyx));
    if det.abs() < 1e-30 {
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
pub fn determinant(t: &Transform) -> Scalar {
    t.txx.mul_add(t.tyy, -(t.txy * t.tyx))
}

// ---------------------------------------------------------------------------
// Applying transforms to MetaPost objects
// ---------------------------------------------------------------------------

/// Apply a transform to a point.
#[inline]
pub fn transform_point(t: &Transform, p: Point) -> Point {
    t.apply_to_point(p)
}

/// Apply a transform to a vector (direction — ignores translation).
#[inline]
pub fn transform_vec(t: &Transform, v: Vec2) -> Vec2 {
    Vec2::new(
        t.txx.mul_add(v.x, t.txy * v.y),
        t.tyx.mul_add(v.x, t.tyy * v.y),
    )
}

/// Apply a transform to a `KnotDirection`.
fn transform_knot_direction(t: &Transform, dir: &KnotDirection) -> KnotDirection {
    match *dir {
        KnotDirection::Explicit(p) => KnotDirection::Explicit(transform_point(t, p)),
        KnotDirection::Given(angle) => {
            // Transform the direction vector, recompute the angle
            let v = Vec2::new(angle.cos(), angle.sin());
            let tv = transform_vec(t, v);
            KnotDirection::Given(tv.y.atan2(tv.x))
        }
        // Curl and Open are not affected by transforms
        other => other,
    }
}

/// Apply a transform to a knot.
pub fn transform_knot(t: &Transform, knot: &Knot) -> Knot {
    Knot {
        point: transform_point(t, knot.point),
        left: transform_knot_direction(t, &knot.left),
        right: transform_knot_direction(t, &knot.right),
        left_tension: knot.left_tension,
        right_tension: knot.right_tension,
    }
}

/// Apply a transform to a path.
pub fn transform_path(t: &Transform, path: &Path) -> Path {
    let knots = path.knots.iter().map(|k| transform_knot(t, k)).collect();
    Path::from_knots(knots, path.is_cyclic)
}

/// Apply a transform to a pen.
pub fn transform_pen(t: &Transform, pen: &Pen) -> Pen {
    match pen {
        Pen::Elliptical(affine) => {
            // Compose: the pen transform is applied after the affine
            Pen::Elliptical(t.to_affine() * *affine)
        }
        Pen::Polygonal(vertices) => {
            let new_verts: Vec<Point> = vertices.iter().map(|&v| transform_point(t, v)).collect();
            // TODO: re-run convex hull after transform
            Pen::Polygonal(new_verts)
        }
    }
}

/// Apply a transform to a color (colors are unaffected by spatial transforms).
pub const fn transform_color(_t: &Transform, c: Color) -> Color {
    c
}

/// Apply a transform to a `GraphicsObject`.
pub fn transform_object(t: &Transform, obj: &GraphicsObject) -> GraphicsObject {
    match obj {
        GraphicsObject::Fill(fill) => GraphicsObject::Fill(FillObject {
            path: transform_path(t, &fill.path),
            color: fill.color,
            pen: fill.pen.as_ref().map(|p| transform_pen(t, p)),
            line_join: fill.line_join,
            miter_limit: fill.miter_limit,
        }),
        GraphicsObject::Stroke(stroke) => GraphicsObject::Stroke(StrokeObject {
            path: transform_path(t, &stroke.path),
            pen: transform_pen(t, &stroke.pen),
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
        GraphicsObject::Text(text) => GraphicsObject::Text(TextObject {
            text: text.text.clone(),
            font_name: text.font_name.clone(),
            font_size: text.font_size,
            color: text.color,
            transform: compose(&text.transform, t),
        }),
        GraphicsObject::ClipStart(path) => GraphicsObject::ClipStart(transform_path(t, path)),
        GraphicsObject::ClipEnd => GraphicsObject::ClipEnd,
        GraphicsObject::SetBoundsStart(path) => {
            GraphicsObject::SetBoundsStart(transform_path(t, path))
        }
        GraphicsObject::SetBoundsEnd => GraphicsObject::SetBoundsEnd,
    }
}

/// Apply a transform to an entire picture.
pub fn transform_picture(t: &Transform, pic: &Picture) -> Picture {
    Picture {
        objects: pic
            .objects
            .iter()
            .map(|obj| transform_object(t, obj))
            .collect(),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
#[allow(clippy::float_cmp)]
mod tests {
    use super::*;
    use crate::types::EPSILON;

    #[test]
    fn test_shifted() {
        let t = shifted(3.0, 4.0);
        let p = transform_point(&t, Point::ZERO);
        assert!((p.x - 3.0).abs() < EPSILON);
        assert!((p.y - 4.0).abs() < EPSILON);
    }

    #[test]
    fn test_rotated_90() {
        let t = rotated(90.0);
        let p = transform_point(&t, Point::new(1.0, 0.0));
        assert!(p.x.abs() < EPSILON);
        assert!((p.y - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_rotated_180() {
        let t = rotated(180.0);
        let p = transform_point(&t, Point::new(1.0, 0.0));
        assert!((p.x + 1.0).abs() < EPSILON);
        assert!(p.y.abs() < EPSILON);
    }

    #[test]
    fn test_scaled() {
        let t = scaled(3.0);
        let p = transform_point(&t, Point::new(2.0, 5.0));
        assert!((p.x - 6.0).abs() < EPSILON);
        assert!((p.y - 15.0).abs() < EPSILON);
    }

    #[test]
    fn test_xscaled() {
        let t = xscaled(2.0);
        let p = transform_point(&t, Point::new(3.0, 4.0));
        assert!((p.x - 6.0).abs() < EPSILON);
        assert!((p.y - 4.0).abs() < EPSILON);
    }

    #[test]
    fn test_yscaled() {
        let t = yscaled(2.0);
        let p = transform_point(&t, Point::new(3.0, 4.0));
        assert!((p.x - 3.0).abs() < EPSILON);
        assert!((p.y - 8.0).abs() < EPSILON);
    }

    #[test]
    fn test_slanted() {
        let t = slanted(1.0);
        let p = transform_point(&t, Point::new(0.0, 1.0));
        // x' = 0 + 1*1 = 1, y' = 1
        assert!((p.x - 1.0).abs() < EPSILON);
        assert!((p.y - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_zscaled() {
        // zscaled (0, 1) is a 90-degree rotation
        let t = zscaled(0.0, 1.0);
        let p = transform_point(&t, Point::new(1.0, 0.0));
        assert!(p.x.abs() < EPSILON);
        assert!((p.y - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_zscaled_scale_and_rotate() {
        // zscaled (1, 1) = scale by sqrt(2) and rotate 45 degrees
        let t = zscaled(1.0, 1.0);
        let p = transform_point(&t, Point::new(1.0, 0.0));
        assert!((p.x - 1.0).abs() < EPSILON);
        assert!((p.y - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_compose_shift_then_rotate() {
        let s = shifted(1.0, 0.0);
        let r = rotated(90.0);
        let c = compose(&s, &r);
        // (0,0) → shifted → (1,0) → rotated 90 → (0,1)
        let p = transform_point(&c, Point::ZERO);
        assert!(p.x.abs() < EPSILON);
        assert!((p.y - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_compose_rotate_then_shift() {
        let r = rotated(90.0);
        let s = shifted(1.0, 0.0);
        let c = compose(&r, &s);
        // (1,0) → rotated 90 → (0,1) → shifted → (1,1)
        let p = transform_point(&c, Point::new(1.0, 0.0));
        assert!((p.x - 1.0).abs() < EPSILON);
        assert!((p.y - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_inverse_identity() {
        let inv = inverse(&Transform::IDENTITY).unwrap();
        let p = transform_point(&inv, Point::new(5.0, 7.0));
        assert!((p.x - 5.0).abs() < EPSILON);
        assert!((p.y - 7.0).abs() < EPSILON);
    }

    #[test]
    fn test_inverse_shift() {
        let t = shifted(3.0, 4.0);
        let inv = inverse(&t).unwrap();
        let p = transform_point(&inv, Point::new(3.0, 4.0));
        assert!(p.x.abs() < EPSILON);
        assert!(p.y.abs() < EPSILON);
    }

    #[test]
    fn test_inverse_scale() {
        let t = scaled(2.0);
        let inv = inverse(&t).unwrap();
        let p = transform_point(&inv, Point::new(6.0, 8.0));
        assert!((p.x - 3.0).abs() < EPSILON);
        assert!((p.y - 4.0).abs() < EPSILON);
    }

    #[test]
    fn test_inverse_roundtrip() {
        let t = compose(&rotated(30.0), &shifted(5.0, -3.0));
        let inv = inverse(&t).unwrap();
        let original = Point::new(7.0, 11.0);
        let transformed = transform_point(&t, original);
        let back = transform_point(&inv, transformed);
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
        let tp = transform_path(&t, &path);
        assert!((tp.knots[0].point.x - 10.0).abs() < EPSILON);
        assert!((tp.knots[0].point.y - 20.0).abs() < EPSILON);
        assert!((tp.knots[1].point.x - 13.0).abs() < EPSILON);
    }

    #[test]
    fn test_transform_pen_elliptical() {
        let pen = Pen::circle(2.0);
        let t = scaled(3.0);
        let tp = transform_pen(&t, &pen);
        match tp {
            Pen::Elliptical(a) => {
                // Circle of diameter 2 scaled by 3 = circle of diameter 6 (radius 3)
                let c = a.as_coeffs();
                assert!((c[0] - 3.0).abs() < EPSILON);
                assert!((c[3] - 3.0).abs() < EPSILON);
            }
            Pen::Polygonal(_) => panic!("expected elliptical"),
        }
    }

    #[test]
    fn test_transform_vec_ignores_translation() {
        let t = shifted(100.0, 200.0);
        let v = transform_vec(&t, Vec2::new(1.0, 0.0));
        assert!((v.x - 1.0).abs() < EPSILON);
        assert!(v.y.abs() < EPSILON);
    }
}
