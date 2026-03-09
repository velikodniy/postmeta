//! Shared test helpers for constructing common `BezierPath` shapes.

use crate::path::{BezierPath, SegmentControls};
use crate::types::Point;

/// Build an open line `BezierPath` from (0,0) to (10,0).
pub fn line() -> BezierPath {
    BezierPath::from_parts(
        vec![Point::ZERO, Point::new(10.0, 0.0)],
        vec![SegmentControls {
            post: Point::new(10.0 / 3.0, 0.0),
            pre: Point::new(20.0 / 3.0, 0.0),
        }],
        false,
    )
}

/// Build a cyclic triangle `BezierPath` with straight-line controls.
pub fn triangle() -> BezierPath {
    let pts = [
        Point::new(0.0, 0.0),
        Point::new(10.0, 0.0),
        Point::new(5.0, 10.0),
    ];
    let controls = (0..3)
        .map(|i| {
            let j = (i + 1) % 3;
            SegmentControls {
                post: pts[i].lerp(pts[j], 1.0 / 3.0),
                pre: pts[i].lerp(pts[j], 2.0 / 3.0),
            }
        })
        .collect();
    BezierPath::from_parts(pts.to_vec(), controls, true)
}

/// Build a 10x10 cyclic square `BezierPath` with straight-line controls.
pub fn square() -> BezierPath {
    let pts = [
        Point::new(0.0, 0.0),
        Point::new(10.0, 0.0),
        Point::new(10.0, 10.0),
        Point::new(0.0, 10.0),
    ];
    let controls = (0..4)
        .map(|i| {
            let j = (i + 1) % 4;
            SegmentControls {
                post: pts[i].lerp(pts[j], 1.0 / 3.0),
                pre: pts[i].lerp(pts[j], 2.0 / 3.0),
            }
        })
        .collect();
    BezierPath::from_parts(pts.to_vec(), controls, true)
}
