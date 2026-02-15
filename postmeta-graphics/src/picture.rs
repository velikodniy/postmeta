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

use crate::path::Path;
use crate::types::{FillObject, GraphicsObject, Picture, StrokeObject};

// ---------------------------------------------------------------------------
// addto operations
// ---------------------------------------------------------------------------

/// Add a filled contour to a picture.
///
/// The path must be cyclic. Corresponds to `addto <pic> contour <path>`.
pub fn addto_contour(pic: &mut Picture, fill: FillObject) {
    debug_assert!(fill.path.is_cyclic, "addto contour requires a cyclic path");
    pic.push(GraphicsObject::Fill(fill));
}

/// Add a stroked path to a picture.
///
/// Corresponds to `addto <pic> doublepath <path>`.
pub fn addto_doublepath(pic: &mut Picture, stroke: StrokeObject) {
    pic.push(GraphicsObject::Stroke(stroke));
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
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::path::Path;
    use crate::types::{Color, Knot, KnotDirection, LineCap, LineJoin, Pen, Point};

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
        addto_contour(
            &mut pic,
            FillObject {
                path,
                color: Color::BLACK,
                pen: None,
                line_join: LineJoin::Round,
                miter_limit: 10.0,
            },
        );
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
            StrokeObject {
                path,
                pen: Pen::circle(1.0),
                color: Color::BLACK,
                dash: None,
                line_cap: LineCap::Round,
                line_join: LineJoin::Round,
                miter_limit: 10.0,
            },
        );
        assert_eq!(pic.objects.len(), 1);
        assert!(matches!(pic.objects[0], GraphicsObject::Stroke(_)));
    }

    #[test]
    fn test_merge() {
        let mut pic1 = Picture::new();
        pic1.push(GraphicsObject::ClipEnd);

        let mut pic2 = Picture::new();
        pic2.push(GraphicsObject::SetBoundsEnd);

        pic1.merge(pic2);
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
}
