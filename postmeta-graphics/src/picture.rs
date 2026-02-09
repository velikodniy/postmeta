//! Picture assembly operations for `MetaPost`.
//!
//! A picture is an ordered collection of graphical objects. The key
//! `MetaPost` primitives for building pictures are:
//!
//! - `addto <pic> contour <path>` — add a filled region
//! - `addto <pic> doublepath <path>` — add a stroked path
//! - `addto <pic> also <picture>` — merge another picture
//! - `clip <pic> to <path>` — clip to a region
//! - `setbounds <pic> to <path>` — set an artificial bounding box

use crate::types::{
    Color, DashPattern, FillObject, GraphicsObject, LineCap, LineJoin, Path, Pen, Picture, Point,
    Scalar, StrokeObject,
};

// ---------------------------------------------------------------------------
// addto operations
// ---------------------------------------------------------------------------

/// Add a filled contour to a picture.
///
/// The path must be cyclic. Corresponds to `addto <pic> contour <path>`.
pub fn addto_contour(
    pic: &mut Picture,
    path: Path,
    color: Color,
    pen: Option<Pen>,
    line_join: LineJoin,
    miter_limit: Scalar,
) {
    debug_assert!(path.is_cyclic, "addto contour requires a cyclic path");
    pic.push(GraphicsObject::Fill(FillObject {
        path,
        color,
        pen,
        line_join,
        miter_limit,
    }));
}

/// Add a stroked path to a picture.
///
/// Corresponds to `addto <pic> doublepath <path>`.
#[expect(
    clippy::too_many_arguments,
    reason = "mirrors MetaPost addto..doublepath with all stroke attributes"
)]
pub fn addto_doublepath(
    pic: &mut Picture,
    path: Path,
    pen: Pen,
    color: Color,
    dash: Option<DashPattern>,
    line_cap: LineCap,
    line_join: LineJoin,
    miter_limit: Scalar,
) {
    pic.push(GraphicsObject::Stroke(StrokeObject {
        path,
        pen,
        color,
        dash,
        line_cap,
        line_join,
        miter_limit,
    }));
}

/// Merge another picture into this one.
///
/// Corresponds to `addto <pic> also <other>`.
pub fn addto_also(pic: &mut Picture, other: &Picture) {
    pic.merge(other);
}

// ---------------------------------------------------------------------------
// clip and setbounds
// ---------------------------------------------------------------------------

/// Clip a picture to a cyclic path.
///
/// Wraps all existing objects in `ClipStart`/`ClipEnd` brackets.
pub fn clip(pic: &mut Picture, clip_path: Path) {
    debug_assert!(clip_path.is_cyclic, "clip requires a cyclic path");

    let existing = std::mem::take(&mut pic.objects);
    pic.push(GraphicsObject::ClipStart(clip_path));
    pic.objects.extend(existing);
    pic.push(GraphicsObject::ClipEnd);
}

/// Set an artificial bounding box on a picture.
///
/// Wraps all existing objects in `SetBoundsStart`/`SetBoundsEnd` brackets.
pub fn setbounds(pic: &mut Picture, bounds_path: Path) {
    debug_assert!(bounds_path.is_cyclic, "setbounds requires a cyclic path");

    let existing = std::mem::take(&mut pic.objects);
    pic.push(GraphicsObject::SetBoundsStart(bounds_path));
    pic.objects.extend(existing);
    pic.push(GraphicsObject::SetBoundsEnd);
}

// ---------------------------------------------------------------------------
// Bounding box computation
// ---------------------------------------------------------------------------

/// Axis-aligned bounding box.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct BoundingBox {
    pub min_x: Scalar,
    pub min_y: Scalar,
    pub max_x: Scalar,
    pub max_y: Scalar,
}

impl BoundingBox {
    /// An empty (inverted) bounding box.
    pub const EMPTY: Self = Self {
        min_x: Scalar::INFINITY,
        min_y: Scalar::INFINITY,
        max_x: Scalar::NEG_INFINITY,
        max_y: Scalar::NEG_INFINITY,
    };

    /// Check if this bounding box is valid (non-empty).
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.min_x <= self.max_x && self.min_y <= self.max_y
    }

    /// Width.
    #[must_use]
    pub fn width(&self) -> Scalar {
        if self.is_valid() {
            self.max_x - self.min_x
        } else {
            0.0
        }
    }

    /// Height.
    #[must_use]
    pub fn height(&self) -> Scalar {
        if self.is_valid() {
            self.max_y - self.min_y
        } else {
            0.0
        }
    }

    /// Lower-left corner.
    #[must_use]
    pub const fn llcorner(&self) -> Point {
        Point::new(self.min_x, self.min_y)
    }

    /// Lower-right corner.
    #[must_use]
    pub const fn lrcorner(&self) -> Point {
        Point::new(self.max_x, self.min_y)
    }

    /// Upper-left corner.
    #[must_use]
    pub const fn ulcorner(&self) -> Point {
        Point::new(self.min_x, self.max_y)
    }

    /// Upper-right corner.
    #[must_use]
    pub const fn urcorner(&self) -> Point {
        Point::new(self.max_x, self.max_y)
    }

    /// Expand to include a point.
    pub const fn include_point(&mut self, p: Point) {
        self.min_x = self.min_x.min(p.x);
        self.min_y = self.min_y.min(p.y);
        self.max_x = self.max_x.max(p.x);
        self.max_y = self.max_y.max(p.y);
    }

    /// Expand to include another bounding box.
    pub fn union(&mut self, other: &Self) {
        if other.is_valid() {
            self.min_x = self.min_x.min(other.min_x);
            self.min_y = self.min_y.min(other.min_y);
            self.max_x = self.max_x.max(other.max_x);
            self.max_y = self.max_y.max(other.max_y);
        }
    }
}

impl Default for BoundingBox {
    fn default() -> Self {
        Self::EMPTY
    }
}

/// Compute the bounding box of a path (control-point hull).
///
/// This is a conservative estimate using the convex hull of all control
/// points, not the tight bound. This matches `MetaPost`'s behavior.
#[must_use]
pub fn path_bbox(path: &Path) -> BoundingBox {
    let mut bb = BoundingBox::EMPTY;
    for knot in &path.knots {
        bb.include_point(knot.point);
        if let crate::types::KnotDirection::Explicit(cp) = knot.left {
            bb.include_point(cp);
        }
        if let crate::types::KnotDirection::Explicit(cp) = knot.right {
            bb.include_point(cp);
        }
    }
    bb
}

/// Compute the bounding box of a picture.
///
/// When `true_corners` is false, `SetBounds` regions override the
/// computed bbox. When true, they are ignored.
#[must_use]
pub fn picture_bbox(pic: &Picture, true_corners: bool) -> BoundingBox {
    let mut bb = BoundingBox::EMPTY;
    let mut bounds_stack: Vec<BoundingBox> = Vec::new();

    for obj in &pic.objects {
        match obj {
            GraphicsObject::Fill(fill) => {
                let pbb = path_bbox(&fill.path);
                bb.union(&pbb);
            }
            GraphicsObject::Stroke(stroke) => {
                let mut pbb = path_bbox(&stroke.path);
                // Expand by pen extent (rough estimate)
                let pen_extent = pen_max_extent(&stroke.pen);
                pbb.min_x -= pen_extent;
                pbb.min_y -= pen_extent;
                pbb.max_x += pen_extent;
                pbb.max_y += pen_extent;
                bb.union(&pbb);
            }
            GraphicsObject::Text(text) => {
                // Approximate: include the transform origin
                let origin = text.transform.apply_to_point(Point::ZERO);
                bb.include_point(origin);
            }
            GraphicsObject::SetBoundsStart(path) if !true_corners => {
                bounds_stack.push(bb);
                bb = path_bbox(path);
            }
            GraphicsObject::SetBoundsEnd if !true_corners => {
                if let Some(prev) = bounds_stack.pop() {
                    let current = bb;
                    bb = prev;
                    bb.union(&current);
                }
            }
            GraphicsObject::ClipStart(_)
            | GraphicsObject::ClipEnd
            | GraphicsObject::SetBoundsStart(_)
            | GraphicsObject::SetBoundsEnd => {}
        }
    }

    bb
}

/// Rough estimate of the maximum pen extent (half-width).
fn pen_max_extent(pen: &Pen) -> Scalar {
    match pen {
        Pen::Elliptical(t) => {
            // Max of the two basis vector lengths (columns of the 2×2 matrix)
            let len1 = t.txx.hypot(t.tyx);
            let len2 = t.txy.hypot(t.tyy);
            len1.max(len2)
        }
        Pen::Polygonal(verts) => verts
            .iter()
            .map(|v| v.to_vec2().length())
            .fold(0.0, Scalar::max),
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
    use crate::types::{Knot, KnotDirection, EPSILON};

    fn make_unit_square() -> Path {
        // A cyclic square path with explicit controls (straight lines)
        let pts = [
            Point::new(0.0, 0.0),
            Point::new(10.0, 0.0),
            Point::new(10.0, 10.0),
            Point::new(0.0, 10.0),
        ];
        let knots = (0..4)
            .map(|i| {
                let j = (i + 1) % 4;
                let prev = (i + 3) % 4;
                let right_cp = Point::new(
                    pts[i].x + (pts[j].x - pts[i].x) / 3.0,
                    pts[i].y + (pts[j].y - pts[i].y) / 3.0,
                );
                let left_cp = Point::new(
                    pts[prev].x + 2.0 * (pts[i].x - pts[prev].x) / 3.0,
                    pts[prev].y + 2.0 * (pts[i].y - pts[prev].y) / 3.0,
                );
                Knot::with_controls(pts[i], left_cp, right_cp)
            })
            .collect();
        Path::from_knots(knots, true)
    }

    #[test]
    fn test_addto_contour() {
        let mut pic = Picture::new();
        let path = make_unit_square();
        addto_contour(&mut pic, path, Color::BLACK, None, LineJoin::Round, 10.0);
        assert_eq!(pic.objects.len(), 1);
        assert!(matches!(pic.objects[0], GraphicsObject::Fill(_)));
    }

    #[test]
    fn test_addto_doublepath() {
        let mut pic = Picture::new();
        let mut k0 = Knot::new(Point::ZERO);
        k0.right = KnotDirection::Explicit(Point::new(3.0, 0.0));
        k0.left = KnotDirection::Explicit(Point::ZERO);
        let mut k1 = Knot::new(Point::new(10.0, 0.0));
        k1.left = KnotDirection::Explicit(Point::new(7.0, 0.0));
        k1.right = KnotDirection::Explicit(Point::new(10.0, 0.0));
        let path = Path::from_knots(vec![k0, k1], false);

        addto_doublepath(
            &mut pic,
            path,
            Pen::circle(1.0),
            Color::BLACK,
            None,
            LineCap::Round,
            LineJoin::Round,
            10.0,
        );
        assert_eq!(pic.objects.len(), 1);
        assert!(matches!(pic.objects[0], GraphicsObject::Stroke(_)));
    }

    #[test]
    fn test_addto_also() {
        let mut pic1 = Picture::new();
        pic1.push(GraphicsObject::ClipEnd);

        let mut pic2 = Picture::new();
        pic2.push(GraphicsObject::SetBoundsEnd);

        addto_also(&mut pic1, &pic2);
        assert_eq!(pic1.objects.len(), 2);
    }

    #[test]
    fn test_clip() {
        let mut pic = Picture::new();
        pic.push(GraphicsObject::ClipEnd); // dummy content

        let clip_path = make_unit_square();
        clip(&mut pic, clip_path);

        assert_eq!(pic.objects.len(), 3);
        assert!(matches!(pic.objects[0], GraphicsObject::ClipStart(_)));
        assert!(matches!(pic.objects[1], GraphicsObject::ClipEnd));
        assert!(matches!(pic.objects[2], GraphicsObject::ClipEnd));
    }

    #[test]
    fn test_setbounds() {
        let mut pic = Picture::new();
        pic.push(GraphicsObject::ClipEnd); // dummy content

        let bounds = make_unit_square();
        setbounds(&mut pic, bounds);

        assert_eq!(pic.objects.len(), 3);
        assert!(matches!(pic.objects[0], GraphicsObject::SetBoundsStart(_)));
        assert!(matches!(pic.objects[2], GraphicsObject::SetBoundsEnd));
    }

    #[test]
    fn test_bounding_box_empty() {
        let bb = BoundingBox::EMPTY;
        assert!(!bb.is_valid());
        assert_eq!(bb.width(), 0.0);
        assert_eq!(bb.height(), 0.0);
    }

    #[test]
    fn test_bounding_box_include_point() {
        let mut bb = BoundingBox::EMPTY;
        bb.include_point(Point::new(1.0, 2.0));
        bb.include_point(Point::new(5.0, 8.0));
        assert!(bb.is_valid());
        assert!((bb.min_x - 1.0).abs() < EPSILON);
        assert!((bb.min_y - 2.0).abs() < EPSILON);
        assert!((bb.max_x - 5.0).abs() < EPSILON);
        assert!((bb.max_y - 8.0).abs() < EPSILON);
    }

    #[test]
    fn test_path_bbox() {
        let path = make_unit_square();
        let bb = path_bbox(&path);
        assert!(bb.is_valid());
        assert!(bb.min_x < 0.1);
        assert!(bb.min_y < 0.1);
        assert!(bb.max_x > 9.9);
        assert!(bb.max_y > 9.9);
    }

    #[test]
    fn test_picture_bbox() {
        let mut pic = Picture::new();
        let path = make_unit_square();
        addto_contour(&mut pic, path, Color::BLACK, None, LineJoin::Round, 10.0);

        let bb = picture_bbox(&pic, true);
        assert!(bb.is_valid());
        assert!(bb.width() > 9.0);
        assert!(bb.height() > 9.0);
    }

    #[test]
    fn test_bounding_box_corners() {
        let bb = BoundingBox {
            min_x: 1.0,
            min_y: 2.0,
            max_x: 5.0,
            max_y: 8.0,
        };
        assert_eq!(bb.llcorner(), Point::new(1.0, 2.0));
        assert_eq!(bb.lrcorner(), Point::new(5.0, 2.0));
        assert_eq!(bb.ulcorner(), Point::new(1.0, 8.0));
        assert_eq!(bb.urcorner(), Point::new(5.0, 8.0));
    }

    #[test]
    fn test_bounding_box_union() {
        let mut bb1 = BoundingBox {
            min_x: 0.0,
            min_y: 0.0,
            max_x: 5.0,
            max_y: 5.0,
        };
        let bb2 = BoundingBox {
            min_x: 3.0,
            min_y: 3.0,
            max_x: 10.0,
            max_y: 10.0,
        };
        bb1.union(&bb2);
        assert!((bb1.min_x).abs() < EPSILON);
        assert!((bb1.max_x - 10.0).abs() < EPSILON);
    }
}
