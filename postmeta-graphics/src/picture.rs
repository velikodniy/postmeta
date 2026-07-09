//! Picture assembly operations for `MetaPost`
//!
//! A picture is an ordered collection of graphical objects.
//! The key `MetaPost` primitives for building pictures are:
//!
//! - `addto <pic> contour <path>` — add a filled region
//! - `addto <pic> doublepath <path>` — add a stroked path
//! - `addto <pic> also <picture>` — merge another picture
//! - `clip <pic> to <path>` — clip to a region
//! - `setbounds <pic> to <path>` — set an artificial bounding box

use crate::path::SharedPath;
use crate::types::{FillObject, GraphicsObject, StrokeObject};

// ---------------------------------------------------------------------------
// Picture
// ---------------------------------------------------------------------------

/// An ordered collection of graphical objects
///
/// The fields are crate-private: external consumers build pictures through [`Picture::push`]/[`Picture::add_fill`]/[`Picture::add_stroke`]/[`Picture::clip`]/[`Picture::set_bounds`] and read them through the accessor methods, so the storage layout can evolve without breaking them.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Picture {
    pub(crate) objects: Vec<GraphicsObject>,
    pub(crate) clip_path: Option<SharedPath>,
    pub(crate) bounds_path: Option<SharedPath>,
}

impl Picture {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            objects: Vec::new(),
            clip_path: None,
            bounds_path: None,
        }
    }

    pub fn push(&mut self, obj: GraphicsObject) {
        self.objects.push(obj);
    }

    /// The objects in this picture, in paint order
    #[must_use]
    pub fn objects(&self) -> &[GraphicsObject] {
        &self.objects
    }

    /// Iterate over the objects in paint order
    pub fn iter(&self) -> std::slice::Iter<'_, GraphicsObject> {
        self.objects.iter()
    }

    /// The first object, if any
    #[must_use]
    pub fn first(&self) -> Option<&GraphicsObject> {
        self.objects.first()
    }

    /// Number of objects in the picture
    #[must_use]
    pub fn len(&self) -> usize {
        self.objects.len()
    }

    /// Whether the picture contains no objects
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.objects.is_empty()
    }

    /// The clip path applied to this picture's objects, if any
    #[must_use]
    pub const fn clip_path(&self) -> Option<&SharedPath> {
        self.clip_path.as_ref()
    }

    /// The artificial bounding path set by `setbounds`, if any
    #[must_use]
    pub const fn bounds_path(&self) -> Option<&SharedPath> {
        self.bounds_path.as_ref()
    }

    /// Append all objects from another picture
    pub fn merge(&mut self, other: Self) {
        self.objects.extend(other.objects);
    }

    /// Add a filled contour to the picture (`addto <pic> contour <path>`), path must be cyclic
    pub fn add_fill(&mut self, fill: FillObject) {
        debug_assert!(
            fill.path.is_cyclic(),
            "addto contour requires a cyclic path"
        );
        self.push(GraphicsObject::Fill(fill));
    }

    /// Add a stroked path to the picture
    ///
    /// Corresponds to `addto <pic> doublepath <path>`.
    pub fn add_stroke(&mut self, stroke: StrokeObject) {
        self.push(GraphicsObject::Stroke(stroke));
    }

    /// Clip the picture to a cyclic path
    ///
    /// Wraps all existing objects in a nested picture with a `clip_path`.
    pub fn clip(&mut self, clip_path: impl Into<SharedPath>) {
        let clip_path = clip_path.into();
        debug_assert!(clip_path.is_cyclic(), "clip requires a cyclic path");

        let existing = std::mem::take(&mut self.objects);
        let nested = Self {
            objects: existing,
            clip_path: Some(clip_path),
            bounds_path: None,
        };
        self.push(GraphicsObject::Picture(nested));
    }

    /// Set an artificial bounding box on the picture
    ///
    /// Wraps all existing objects in a nested picture with a `bounds_path`.
    pub fn set_bounds(&mut self, bounds_path: impl Into<SharedPath>) {
        let bounds_path = bounds_path.into();
        debug_assert!(bounds_path.is_cyclic(), "setbounds requires a cyclic path");

        let existing = std::mem::take(&mut self.objects);
        let nested = Self {
            objects: existing,
            clip_path: None,
            bounds_path: Some(bounds_path),
        };
        self.push(GraphicsObject::Picture(nested));
    }
}

impl<'a> IntoIterator for &'a Picture {
    type Item = &'a GraphicsObject;
    type IntoIter = std::slice::Iter<'a, GraphicsObject>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_helpers;
    use crate::types::{Color, LineCap, LineJoin, Pen};

    #[test]
    fn test_add_fill() {
        let mut pic = Picture::new();
        let path = test_helpers::square();
        pic.add_fill(FillObject {
            path: std::sync::Arc::new(path),
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
        let path = test_helpers::line();

        pic.add_stroke(StrokeObject {
            path: std::sync::Arc::new(path),
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
        pic1.push(GraphicsObject::Picture(Picture::new()));

        let mut pic2 = Picture::new();
        pic2.push(GraphicsObject::Picture(Picture::new()));

        pic1.merge(pic2);
        assert_eq!(pic1.objects.len(), 2);
    }

    #[test]
    fn test_clip() {
        let mut pic = Picture::new();
        pic.push(GraphicsObject::Picture(Picture::new())); // dummy content

        let clip_path = test_helpers::square();
        pic.clip(std::sync::Arc::new(clip_path));

        assert_eq!(pic.objects.len(), 1);
        if let GraphicsObject::Picture(nested) = &pic.objects[0] {
            assert!(nested.clip_path.is_some());
        } else {
            panic!("Expected Picture");
        }
    }

    #[test]
    fn test_set_bounds() {
        let mut pic = Picture::new();
        pic.push(GraphicsObject::Picture(Picture::new())); // dummy content

        let bounds = test_helpers::square();
        pic.set_bounds(std::sync::Arc::new(bounds));

        assert_eq!(pic.objects.len(), 1);
        if let GraphicsObject::Picture(nested) = &pic.objects[0] {
            assert!(nested.bounds_path.is_some());
        } else {
            panic!("Expected Picture");
        }
    }
}
