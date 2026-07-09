use postmeta_graphics::types::{FillObject, StrokeObject, TextObject};
use svg::node::element::Text as SvgText;

use crate::options::RenderOptions;
use crate::path::path_to_d;
use crate::util::{
    color_to_svg, dash_to_svg, fmt_scalar, linecap_to_svg, linejoin_to_svg, pen_stroke_width,
};

/// Render a filled contour to an SVG `<path>` element
pub fn render_fill(fill: &FillObject, opts: &RenderOptions) -> svg::node::element::Path {
    let d = path_to_d(&fill.path, opts.precision);
    let mut el = svg::node::element::Path::new()
        .set("d", d)
        .set("fill", color_to_svg(fill.color));

    if let Some(ref pen) = fill.pen {
        let width = pen_stroke_width(pen);
        el = el
            .set("stroke", color_to_svg(fill.color))
            .set("stroke-width", fmt_scalar(width, opts.precision))
            .set("stroke-linejoin", linejoin_to_svg(fill.line_join))
            .set(
                "stroke-miterlimit",
                fmt_scalar(fill.miter_limit, opts.precision),
            );
    } else {
        el = el.set("stroke", "none");
    }

    el
}

/// Render a stroked path to an SVG `<path>` element
pub fn render_stroke(stroke: &StrokeObject, opts: &RenderOptions) -> svg::node::element::Path {
    let d = path_to_d(&stroke.path, opts.precision);
    let width = pen_stroke_width(&stroke.pen);

    let mut el = svg::node::element::Path::new()
        .set("d", d)
        .set("fill", "none")
        .set("stroke", color_to_svg(stroke.color))
        .set("stroke-width", fmt_scalar(width, opts.precision))
        .set("stroke-linecap", linecap_to_svg(stroke.line_cap))
        .set("stroke-linejoin", linejoin_to_svg(stroke.line_join))
        .set(
            "stroke-miterlimit",
            fmt_scalar(stroke.miter_limit, opts.precision),
        );

    if let Some(ref dash) = stroke.dash {
        el = el
            .set("stroke-dasharray", dash_to_svg(dash, opts.precision))
            .set("stroke-dashoffset", fmt_scalar(dash.offset, opts.precision));
    }

    el
}

/// Render a text label as a raw SVG `<text>` element
///
/// The `MetaPost` Y-up to SVG Y-down flip is applied by conjugating the transform via `svg_text_matrix`.
pub fn render_text_raw(text: &TextObject, opts: &RenderOptions) -> SvgText {
    let matrix = crate::util::svg_text_matrix(&text.transform, opts.precision);

    SvgText::new(text.text.as_ref())
        .set("transform", matrix)
        .set("font-family", text.font_name.as_ref())
        .set("font-size", fmt_scalar(text.font_size, opts.precision))
        .set("fill", color_to_svg(text.color))
}
