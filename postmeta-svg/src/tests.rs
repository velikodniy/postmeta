use std::sync::Arc;

use postmeta_graphics::path::Path;
use postmeta_graphics::types::{
    Color, DashPattern, FillObject, GraphicsObject, Knot, KnotDirection, LineCap, LineJoin, Pen,
    Picture, Point, StrokeObject, TextMetrics, TextObject, Transform,
};

use crate::objects::{render_fill, render_stroke};
use crate::path::path_to_d;
use crate::renderer::find_matching_end;
use crate::util::{color_to_svg, dash_to_svg, fmt_scalar, pen_stroke_width};
use crate::{RenderOptions, render_to_string};

/// Make a resolved line from (0,0) to (10,0).
fn make_line() -> Path {
    let mut k0 = Knot::new(Point::ZERO);
    k0.right = KnotDirection::Explicit(Point::new(10.0 / 3.0, 0.0));
    k0.left = KnotDirection::Explicit(Point::ZERO);
    let mut k1 = Knot::new(Point::new(10.0, 0.0));
    k1.left = KnotDirection::Explicit(Point::new(20.0 / 3.0, 0.0));
    k1.right = KnotDirection::Explicit(Point::new(10.0, 0.0));
    Path::from_knots(vec![k0, k1], false)
}

/// Make a resolved square 0,0 -> 10,0 -> 10,10 -> 0,10 -> cycle.
fn make_square() -> Path {
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
fn test_path_to_d_empty() {
    let path = Path::new();
    assert_eq!(path_to_d(&path, 4), "");
}

#[test]
fn test_path_to_d_line() {
    let path = make_line();
    let d = path_to_d(&path, 2);
    assert!(d.starts_with('M'));
    assert!(d.contains('C'));
    assert!(!d.contains('Z'));
    assert!(d.starts_with("M0.00,0.00"), "unexpected start: {d}");
}

#[test]
fn test_path_to_d_y_negation() {
    let mut k0 = Knot::new(Point::new(5.0, 10.0));
    k0.right = KnotDirection::Explicit(Point::new(5.0, 10.0));
    k0.left = KnotDirection::Explicit(Point::new(5.0, 10.0));
    let path = Path::from_knots(vec![k0], false);
    let d = path_to_d(&path, 1);
    assert!(d.contains("5.0,-10.0"), "Y should be negated: {d}");
}

#[test]
fn test_path_to_d_cyclic() {
    let path = make_square();
    let d = path_to_d(&path, 2);
    assert!(d.starts_with('M'));
    assert!(d.ends_with('Z'));
}

#[test]
fn test_color_to_svg_black() {
    assert_eq!(color_to_svg(Color::BLACK), "black");
}

#[test]
fn test_color_to_svg_white() {
    assert_eq!(color_to_svg(Color::WHITE), "white");
}

#[test]
fn test_color_to_svg_red() {
    assert_eq!(color_to_svg(Color::new(1.0, 0.0, 0.0)), "#ff0000");
}

#[test]
fn test_color_to_svg_half_gray() {
    let c = color_to_svg(Color::new(0.5, 0.5, 0.5));
    assert_eq!(c, "#808080");
}

#[test]
fn test_pen_stroke_width_circle() {
    let pen = Pen::circle(2.0);
    let width = pen_stroke_width(&pen);
    assert!((width - 2.0).abs() < 0.01, "width = {width}");
}

#[test]
fn test_pen_stroke_width_nullpen() {
    let pen = Pen::Elliptical(Transform::ZERO);
    let width = pen_stroke_width(&pen);
    assert!(width.abs() < 0.001);
}

#[test]
fn test_fmt_scalar_trailing_zeros() {
    assert_eq!(fmt_scalar(1.0, 4), "1");
    assert_eq!(fmt_scalar(1.5, 4), "1.5");
    assert_eq!(fmt_scalar(1.25, 4), "1.25");
}

#[test]
fn test_dash_to_svg() {
    let dash = DashPattern {
        dashes: vec![5.0, 3.0],
        offset: 0.0,
    };
    assert_eq!(dash_to_svg(&dash, 1), "5.0,3.0");
}

#[test]
fn test_render_fill_produces_svg_path() {
    let fill = FillObject {
        path: make_square(),
        color: Color::new(1.0, 0.0, 0.0),
        pen: None,
        line_join: LineJoin::Round,
        miter_limit: 10.0,
    };
    let el = render_fill(&fill, &RenderOptions::default());
    let s = el.to_string();
    assert!(s.contains("fill=\"#ff0000\""), "missing fill: {s}");
    assert!(s.contains("stroke=\"none\""), "missing stroke=none: {s}");
    assert!(s.contains(" d=\"M"), "missing d attr: {s}");
}

#[test]
fn test_render_stroke_produces_svg_path() {
    let stroke = StrokeObject {
        path: make_line(),
        pen: Pen::circle(1.0),
        color: Color::BLACK,
        dash: None,
        line_cap: LineCap::Round,
        line_join: LineJoin::Round,
        miter_limit: 10.0,
    };
    let el = render_stroke(&stroke, &RenderOptions::default());
    let s = el.to_string();
    assert!(s.contains("fill=\"none\""), "missing fill=none: {s}");
    assert!(s.contains("stroke=\"black\""), "missing stroke: {s}");
    assert!(s.contains("stroke-width="), "missing stroke-width: {s}");
    assert!(
        s.contains("stroke-linecap=\"round\""),
        "missing linecap: {s}"
    );
}

#[test]
fn test_render_stroke_with_dash() {
    let stroke = StrokeObject {
        path: make_line(),
        pen: Pen::circle(1.0),
        color: Color::BLACK,
        dash: Some(DashPattern {
            dashes: vec![3.0, 2.0],
            offset: 1.0,
        }),
        line_cap: LineCap::Butt,
        line_join: LineJoin::Miter,
        miter_limit: 10.0,
    };
    let el = render_stroke(&stroke, &RenderOptions::default());
    let s = el.to_string();
    assert!(s.contains("stroke-dasharray="), "missing dasharray: {s}");
    assert!(s.contains("stroke-dashoffset="), "missing dashoffset: {s}");
}

#[test]
fn test_render_empty_picture() {
    let pic = Picture::new();
    let svg = render_to_string(&pic);
    assert!(svg.contains("<svg"));
    assert!(svg.contains("viewBox="));
}

#[test]
fn test_render_filled_square() {
    let mut pic = Picture::new();
    pic.add_fill(FillObject {
        path: make_square(),
        color: Color::new(0.0, 0.0, 1.0),
        pen: None,
        line_join: LineJoin::Round,
        miter_limit: 10.0,
    });
    let svg = render_to_string(&pic);
    assert!(svg.contains("fill=\"#0000ff\""), "missing blue fill: {svg}");
    assert!(
        !svg.contains("scale(1,-1)"),
        "should not have global Y flip: {svg}"
    );
}

#[test]
fn test_render_stroked_line() {
    let mut pic = Picture::new();
    pic.add_stroke(StrokeObject {
        path: make_line(),
        pen: Pen::circle(1.0),
        color: Color::BLACK,
        dash: None,
        line_cap: LineCap::Round,
        line_join: LineJoin::Round,
        miter_limit: 10.0,
    });
    let svg = render_to_string(&pic);
    assert!(svg.contains("stroke=\"black\""), "missing stroke: {svg}");
    assert!(svg.contains("stroke-width="), "missing stroke-width: {svg}");
}

#[test]
fn test_render_with_clip() {
    let mut pic = Picture::new();
    pic.push(GraphicsObject::ClipStart(make_square()));
    pic.push(GraphicsObject::Fill(FillObject {
        path: make_square(),
        color: Color::new(1.0, 0.0, 0.0),
        pen: None,
        line_join: LineJoin::Round,
        miter_limit: 10.0,
    }));
    pic.push(GraphicsObject::ClipEnd);

    let svg = render_to_string(&pic);
    assert!(svg.contains("<clipPath"), "missing clipPath def: {svg}");
    assert!(
        svg.contains("clip-path=\"url(#c0)\""),
        "missing clip ref: {svg}"
    );
}

#[test]
fn test_render_text() {
    let mut pic = Picture::new();
    pic.push(GraphicsObject::Text(TextObject {
        text: Arc::from("Hello"),
        font_name: Arc::from("CMR10"),
        font_size: 10.0,
        metrics: TextMetrics::default(),
        color: Color::BLACK,
        transform: Transform {
            tx: 50.0,
            ty: 25.0,
            ..Transform::IDENTITY
        },
    }));
    let svg = render_to_string(&pic);
    assert!(svg.contains("Hello"), "missing text content: {svg}");
    assert!(svg.contains("font-family=\"CMR10\""), "missing font: {svg}");
    assert!(svg.contains("-25"), "Y should be negated in text: {svg}");
}

#[test]
fn test_find_matching_end_nested() {
    let objects = vec![
        GraphicsObject::ClipStart(Path::new()),
        GraphicsObject::ClipStart(Path::new()),
        GraphicsObject::ClipEnd,
        GraphicsObject::ClipEnd,
    ];
    assert_eq!(find_matching_end(&objects, 0, true), 3);
    assert_eq!(find_matching_end(&objects, 1, true), 2);
}

#[test]
fn test_viewbox_uses_bbox() {
    let mut pic = Picture::new();
    pic.add_fill(FillObject {
        path: make_square(),
        color: Color::BLACK,
        pen: None,
        line_join: LineJoin::Round,
        miter_limit: 10.0,
    });
    let svg = render_to_string(&pic);
    assert!(svg.contains("viewBox="), "missing viewBox: {svg}");
    assert!(svg.contains("pt\""), "missing pt units: {svg}");
}
