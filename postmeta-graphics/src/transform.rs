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

use crate::path::{BezierPath, SegmentControls};
use crate::pen::{Pen, convex_hull};
use crate::types::{
    FillObject, GraphicsObject, Knot, KnotDirection, NEAR_ZERO, Picture, Point, Scalar,
    StrokeObject, TextObject, Vec2,
};

// ---------------------------------------------------------------------------
// Transform
// ---------------------------------------------------------------------------

/// A transform with named components.
///
/// Maps point (x, y) to (tx + txx*x + txy*y, ty + tyx*x + tyy*y)
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

    /// Create a translation transform.
    #[must_use]
    pub const fn shifted(dx: Scalar, dy: Scalar) -> Self {
        Self {
            tx: dx,
            ty: dy,
            ..Self::IDENTITY
        }
    }

    /// Create a rotation transform (angle in degrees).
    #[must_use]
    pub fn rotated(degrees: Scalar) -> Self {
        let (s, c) = degrees.to_radians().sin_cos();
        Self {
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
    pub const fn scaled(factor: Scalar) -> Self {
        Self {
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
    pub const fn xscaled(factor: Scalar) -> Self {
        Self {
            txx: factor,
            ..Self::IDENTITY
        }
    }

    /// Create a y-only scaling transform.
    #[must_use]
    pub const fn yscaled(factor: Scalar) -> Self {
        Self {
            tyy: factor,
            ..Self::IDENTITY
        }
    }

    /// Create a horizontal shear (slant) transform.
    #[must_use]
    pub const fn slanted(factor: Scalar) -> Self {
        Self {
            txy: factor,
            ..Self::IDENTITY
        }
    }

    /// Create a complex-multiplication transform: `zscaled (a, b)`.
    ///
    /// This simultaneously rotates and scales: the point (1, 0) maps to (a, b).
    #[must_use]
    pub fn zscaled(a: Scalar, b: Scalar) -> Self {
        Self {
            tx: 0.0,
            ty: 0.0,
            txx: a,
            txy: -b,
            tyx: b,
            tyy: a,
        }
    }

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

    /// Determinant of the linear part of this transform.
    #[must_use]
    pub fn det(&self) -> Scalar {
        self.txx.mul_add(self.tyy, -(self.txy * self.tyx))
    }
}

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
    fn transformed(&self, t: &Transform) -> Self {
        Point::new(
            t.txy.mul_add(self.y, t.txx.mul_add(self.x, t.tx)),
            t.tyy.mul_add(self.y, t.tyx.mul_add(self.x, t.ty)),
        )
    }
}

impl Transformable for Vec2 {
    /// Transform a vector (direction). Translation is ignored — only the
    /// linear part of the affine is applied.
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

impl Transformable for BezierPath {
    fn transformed(&self, t: &Transform) -> Self {
        let points = self
            .knot_points()
            .iter()
            .map(|p| p.transformed(t))
            .collect();
        let controls = (0..self.num_segments())
            .map(|i| {
                let c = self.segment_controls(i);
                SegmentControls {
                    post: c.post.transformed(t),
                    pre: c.pre.transformed(t),
                }
            })
            .collect();
        Self::from_parts(points, controls, self.is_cyclic())
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
                    // Scale dash lengths by the "average linear scale factor" of
                    // the transform. For a uniform scale s the determinant is s²,
                    // so sqrt(|det|) = |s|, which is the correct 1-D length
                    // scale.
                    // For non-uniform transforms this is an approximation
                    // (the exact scale depends on direction) but it matches
                    // MetaPost's approach and is adequate for dash patterns.
                    let scale = t.det().abs().sqrt();
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
                metrics: text.metrics,
                color: text.color,
                transform: text.transform.then(t),
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
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::EPSILON;

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
        let p = Point::new(1.0, 1.0).transformed(&t);
        assert!((p.x - 12.0).abs() < EPSILON);
        assert!((p.y - 23.0).abs() < EPSILON);
    }

    #[test]
    fn test_shifted() {
        let t = Transform::shifted(3.0, 4.0);
        let p = Point::ZERO.transformed(&t);
        assert!((p.x - 3.0).abs() < EPSILON);
        assert!((p.y - 4.0).abs() < EPSILON);
    }

    #[test]
    fn test_rotated_90() {
        let t = Transform::rotated(90.0);
        let p = Point::new(1.0, 0.0).transformed(&t);
        assert!(p.x.abs() < EPSILON);
        assert!((p.y - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_rotated_180() {
        let t = Transform::rotated(180.0);
        let p = Point::new(1.0, 0.0).transformed(&t);
        assert!((p.x + 1.0).abs() < EPSILON);
        assert!(p.y.abs() < EPSILON);
    }

    #[test]
    fn test_scaled() {
        let t = Transform::scaled(3.0);
        let p = Point::new(2.0, 5.0).transformed(&t);
        assert!((p.x - 6.0).abs() < EPSILON);
        assert!((p.y - 15.0).abs() < EPSILON);
    }

    #[test]
    fn test_xscaled() {
        let t = Transform::xscaled(2.0);
        let p = Point::new(3.0, 4.0).transformed(&t);
        assert!((p.x - 6.0).abs() < EPSILON);
        assert!((p.y - 4.0).abs() < EPSILON);
    }

    #[test]
    fn test_yscaled() {
        let t = Transform::yscaled(2.0);
        let p = Point::new(3.0, 4.0).transformed(&t);
        assert!((p.x - 3.0).abs() < EPSILON);
        assert!((p.y - 8.0).abs() < EPSILON);
    }

    #[test]
    fn test_slanted() {
        let t = Transform::slanted(1.0);
        let p = Point::new(0.0, 1.0).transformed(&t);
        // x' = 0 + 1*1 = 1, y' = 1
        assert!((p.x - 1.0).abs() < EPSILON);
        assert!((p.y - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_zscaled() {
        // zscaled (0, 1) is a 90-degree rotation
        let t = Transform::zscaled(0.0, 1.0);
        let p = Point::new(1.0, 0.0).transformed(&t);
        assert!(p.x.abs() < EPSILON);
        assert!((p.y - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_zscaled_scale_and_rotate() {
        // zscaled (1, 1) = scale by sqrt(2) and rotate 45 degrees
        let t = Transform::zscaled(1.0, 1.0);
        let p = Point::new(1.0, 0.0).transformed(&t);
        assert!((p.x - 1.0).abs() < EPSILON);
        assert!((p.y - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_compose_shift_then_rotate() {
        let s = Transform::shifted(1.0, 0.0);
        let r = Transform::rotated(90.0);
        let c = s.then(&r);
        // (0,0) → shifted → (1,0) → rotated 90 → (0,1)
        let p = Point::ZERO.transformed(&c);
        assert!(p.x.abs() < EPSILON);
        assert!((p.y - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_compose_rotate_then_shift() {
        let r = Transform::rotated(90.0);
        let s = Transform::shifted(1.0, 0.0);
        let c = r.then(&s);
        // (1,0) → rotated 90 → (0,1) → shifted → (1,1)
        let p = Point::new(1.0, 0.0).transformed(&c);
        assert!((p.x - 1.0).abs() < EPSILON);
        assert!((p.y - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_det() {
        assert!((Transform::IDENTITY.det() - 1.0).abs() < EPSILON);
        assert!((Transform::scaled(3.0).det() - 9.0).abs() < EPSILON);
        assert!((Transform::rotated(45.0).det() - 1.0).abs() < EPSILON);
    }

    #[test]
    fn test_transform_bezier_path() {
        let path = BezierPath::from_parts(
            vec![Point::ZERO, Point::new(3.0, 0.0)],
            vec![SegmentControls {
                post: Point::new(1.0, 0.0),
                pre: Point::new(2.0, 0.0),
            }],
            false,
        );
        let t = Transform::shifted(10.0, 20.0);
        let tp = path.transformed(&t);
        assert!((tp.knot_point(0).x - 10.0).abs() < EPSILON);
        assert!((tp.knot_point(0).y - 20.0).abs() < EPSILON);
        assert!((tp.knot_point(1).x - 13.0).abs() < EPSILON);
    }

    #[test]
    fn test_transform_pen_elliptical() {
        let pen = Pen::circle(2.0);
        let t = Transform::scaled(3.0);
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
        let t = Transform::shifted(100.0, 200.0);
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

    // -----------------------------------------------------------------------
    // BezierPath transform tests
    // -----------------------------------------------------------------------

    /// Helper: build a simple open `BezierPath` with two knot points and one segment.
    fn sample_bezier_path() -> BezierPath {
        let points = vec![Point::new(0.0, 0.0), Point::new(10.0, 0.0)];
        let controls = vec![SegmentControls {
            post: Point::new(3.0, 4.0),
            pre: Point::new(7.0, 4.0),
        }];
        BezierPath::from_parts(points, controls, false)
    }

    /// Helper: build a cyclic `BezierPath` (triangle) with three knot points.
    fn sample_cyclic_bezier_path() -> BezierPath {
        let points = vec![
            Point::new(0.0, 0.0),
            Point::new(10.0, 0.0),
            Point::new(5.0, 10.0),
        ];
        let controls = vec![
            SegmentControls {
                post: Point::new(3.0, 0.0),
                pre: Point::new(7.0, 0.0),
            },
            SegmentControls {
                post: Point::new(10.0, 3.0),
                pre: Point::new(8.0, 7.0),
            },
            SegmentControls {
                post: Point::new(3.0, 8.0),
                pre: Point::new(0.0, 3.0),
            },
        ];
        BezierPath::from_parts(points, controls, true)
    }

    #[test]
    fn test_bezier_path_shift() {
        let path = sample_bezier_path();
        let t = Transform::shifted(5.0, 10.0);
        let tp = path.transformed(&t);

        // Knot points shifted
        assert!((tp.knot_point(0).x - 5.0).abs() < EPSILON);
        assert!((tp.knot_point(0).y - 10.0).abs() < EPSILON);
        assert!((tp.knot_point(1).x - 15.0).abs() < EPSILON);
        assert!((tp.knot_point(1).y - 10.0).abs() < EPSILON);

        // Control points shifted
        let c = tp.segment_controls(0);
        assert!((c.post.x - 8.0).abs() < EPSILON);
        assert!((c.post.y - 14.0).abs() < EPSILON);
        assert!((c.pre.x - 12.0).abs() < EPSILON);
        assert!((c.pre.y - 14.0).abs() < EPSILON);
    }

    #[test]
    fn test_bezier_path_rotation() {
        let path = sample_bezier_path();
        let t = Transform::rotated(90.0);
        let tp = path.transformed(&t);

        // (0,0) rotated 90 -> (0,0)
        assert!(tp.knot_point(0).x.abs() < EPSILON);
        assert!(tp.knot_point(0).y.abs() < EPSILON);
        // (10,0) rotated 90 -> (0,10)
        assert!(tp.knot_point(1).x.abs() < EPSILON);
        assert!((tp.knot_point(1).y - 10.0).abs() < EPSILON);

        // (3,4) rotated 90 -> (-4,3)
        let c = tp.segment_controls(0);
        assert!((c.post.x + 4.0).abs() < EPSILON);
        assert!((c.post.y - 3.0).abs() < EPSILON);
        // (7,4) rotated 90 -> (-4,7)
        assert!((c.pre.x + 4.0).abs() < EPSILON);
        assert!((c.pre.y - 7.0).abs() < EPSILON);
    }

    #[test]
    fn test_bezier_path_preserves_segment_count_and_cyclic() {
        let open_path = sample_bezier_path();
        let cyclic_path = sample_cyclic_bezier_path();
        let t = Transform::scaled(2.0);

        let tp_open = open_path.transformed(&t);
        assert_eq!(tp_open.num_segments(), open_path.num_segments());
        assert_eq!(tp_open.num_knots(), open_path.num_knots());
        assert!(!tp_open.is_cyclic());

        let tp_cyclic = cyclic_path.transformed(&t);
        assert_eq!(tp_cyclic.num_segments(), cyclic_path.num_segments());
        assert_eq!(tp_cyclic.num_knots(), cyclic_path.num_knots());
        assert!(tp_cyclic.is_cyclic());
    }

    #[test]
    fn test_bezier_path_cyclic_shift() {
        let path = sample_cyclic_bezier_path();
        let t = Transform::shifted(1.0, 2.0);
        let tp = path.transformed(&t);

        // All three knot points shifted
        assert!((tp.knot_point(0).x - 1.0).abs() < EPSILON);
        assert!((tp.knot_point(0).y - 2.0).abs() < EPSILON);
        assert!((tp.knot_point(1).x - 11.0).abs() < EPSILON);
        assert!((tp.knot_point(1).y - 2.0).abs() < EPSILON);
        assert!((tp.knot_point(2).x - 6.0).abs() < EPSILON);
        assert!((tp.knot_point(2).y - 12.0).abs() < EPSILON);

        // All three segments' controls shifted
        for i in 0..3 {
            let orig = path.segment_controls(i);
            let transformed = tp.segment_controls(i);
            assert!((transformed.post.x - orig.post.x - 1.0).abs() < EPSILON);
            assert!((transformed.post.y - orig.post.y - 2.0).abs() < EPSILON);
            assert!((transformed.pre.x - orig.pre.x - 1.0).abs() < EPSILON);
            assert!((transformed.pre.y - orig.pre.y - 2.0).abs() < EPSILON);
        }
    }

    #[test]
    fn test_bezier_path_scale() {
        let path = sample_bezier_path();
        let t = Transform::scaled(3.0);
        let tp = path.transformed(&t);

        assert!((tp.knot_point(0).x - 0.0).abs() < EPSILON);
        assert!((tp.knot_point(0).y - 0.0).abs() < EPSILON);
        assert!((tp.knot_point(1).x - 30.0).abs() < EPSILON);
        assert!((tp.knot_point(1).y - 0.0).abs() < EPSILON);

        let c = tp.segment_controls(0);
        assert!((c.post.x - 9.0).abs() < EPSILON);
        assert!((c.post.y - 12.0).abs() < EPSILON);
        assert!((c.pre.x - 21.0).abs() < EPSILON);
        assert!((c.pre.y - 12.0).abs() < EPSILON);
    }
}
