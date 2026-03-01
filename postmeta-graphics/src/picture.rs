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
// Picture assembly methods
// ---------------------------------------------------------------------------

impl Picture {
    /// Add a filled contour to the picture.
    ///
    /// The path must be cyclic. Corresponds to `addto <pic> contour <path>`.
    pub fn add_fill(&mut self, fill: FillObject) {
        debug_assert!(fill.path.is_cyclic, "addto contour requires a cyclic path");
        self.push(GraphicsObject::Fill(fill));
    }

    /// Add a stroked path to the picture.
    ///
    /// Corresponds to `addto <pic> doublepath <path>`.
    pub fn add_stroke(&mut self, stroke: StrokeObject) {
        self.push(GraphicsObject::Stroke(stroke));
    }

    /// Clip the picture to a cyclic path.
    ///
    /// Wraps all existing objects in `ClipStart`/`ClipEnd` brackets.
    pub fn clip(&mut self, clip_path: Path) {
        debug_assert!(clip_path.is_cyclic, "clip requires a cyclic path");

        let existing = std::mem::take(&mut self.objects);
        self.push(GraphicsObject::ClipStart(clip_path));
        self.objects.extend(existing);
        self.push(GraphicsObject::ClipEnd);
    }

    /// Set an artificial bounding box on the picture.
    ///
    /// Wraps all existing objects in `SetBoundsStart`/`SetBoundsEnd` brackets.
    pub fn set_bounds(&mut self, bounds_path: Path) {
        debug_assert!(bounds_path.is_cyclic, "setbounds requires a cyclic path");

        let existing = std::mem::take(&mut self.objects);
        self.push(GraphicsObject::SetBoundsStart(bounds_path));
        self.objects.extend(existing);
        self.push(GraphicsObject::SetBoundsEnd);
    }
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
    fn test_add_fill() {
        let mut pic = Picture::new();
        let path = make_unit_square();
        pic.add_fill(FillObject {
            path,
            color: Color::BLACK,
            pen: None,
            line_join: LineJoin::Round,
            miter_limit: 10.0,
        });
        assert_eq!(pic.objects.len(), 1);
        assert!(matches!(pic.objects[0], GraphicsObject::Fill(_)));
    }

    #[test]
    fn test_add_stroke() {
        let mut pic = Picture::new();
        let mut k0 = Knot::new(Point::ZERO);
        k0.right = KnotDirection::Explicit(Point::new(3.0, 0.0));
        k0.left = KnotDirection::Explicit(Point::ZERO);
        let mut k1 = Knot::new(Point::new(10.0, 0.0));
        k1.left = KnotDirection::Explicit(Point::new(7.0, 0.0));
        k1.right = KnotDirection::Explicit(Point::new(10.0, 0.0));
        let path = Path::from_knots(vec![k0, k1], false);

        pic.add_stroke(StrokeObject {
            path,
            pen: Pen::circle(1.0),
            color: Color::BLACK,
            dash: None,
            line_cap: LineCap::Round,
            line_join: LineJoin::Round,
            miter_limit: 10.0,
        });
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
        pic.clip(clip_path);

        assert_eq!(pic.objects.len(), 3);
        assert!(matches!(pic.objects[0], GraphicsObject::ClipStart(_)));
        assert!(matches!(pic.objects[1], GraphicsObject::ClipEnd));
        assert!(matches!(pic.objects[2], GraphicsObject::ClipEnd));
    }

    #[test]
    fn test_set_bounds() {
        let mut pic = Picture::new();
        pic.push(GraphicsObject::ClipEnd); // dummy content

        let bounds = make_unit_square();
        pic.set_bounds(bounds);

        assert_eq!(pic.objects.len(), 3);
        assert!(matches!(pic.objects[0], GraphicsObject::SetBoundsStart(_)));
        assert!(matches!(pic.objects[2], GraphicsObject::SetBoundsEnd));
    }
}
