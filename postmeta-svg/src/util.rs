//! Formatting helpers for the SVG backend, and the single home of the Y-axis flip
//!
//! `MetaPost` is Y-up and SVG is Y-down; the backend converts by negating Y per coordinate via [`flip_y`], never with a global `scale(1,-1)` or viewBox trick.
//! Path data and viewBox origins negate Y directly; text transforms are conjugated with `S = diag(1, -1)` (see [`svg_text_matrix`]).

use postmeta_graphics::types::{
    Color, DashPattern, LineCap, LineJoin, Pen, Scalar, Transform, Vec2,
};

/// Negate a Y coordinate or Y-coupled matrix term (`MetaPost` Y-up to SVG Y-down); every Y flip in the backend goes through here
#[must_use]
pub const fn flip_y(y: Scalar) -> Scalar {
    -y
}

/// SVG `transform` attribute for a text object's `MetaPost` transform
///
/// The Y-flip conjugates the matrix (`M_svg = S * M_mp * S` with `S = diag(1, -1)`): off-diagonal terms and the Y translation are negated, the diagonal is unchanged.
#[must_use]
pub fn svg_text_matrix(t: &Transform, precision: usize) -> String {
    format!(
        "matrix({},{},{},{},{},{})",
        fmt_scalar(t.txx, precision),
        fmt_scalar(flip_y(t.tyx), precision),
        fmt_scalar(flip_y(t.txy), precision),
        fmt_scalar(t.tyy, precision),
        fmt_scalar(t.tx, precision),
        fmt_scalar(flip_y(t.ty), precision),
    )
}

/// Convert a [`Color`] to an SVG color string
#[expect(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "color components are clamped to [0, 255]"
)]
pub fn color_to_svg(c: Color) -> String {
    let r = (c.r.clamp(0.0, 1.0) * 255.0).round() as u8;
    let g = (c.g.clamp(0.0, 1.0) * 255.0).round() as u8;
    let b = (c.b.clamp(0.0, 1.0) * 255.0).round() as u8;
    if r == 0 && g == 0 && b == 0 {
        "black".to_owned()
    } else if r == 255 && g == 255 && b == 255 {
        "white".to_owned()
    } else {
        format!("#{r:02x}{g:02x}{b:02x}")
    }
}

/// Extract a stroke width from a pen
///
/// Elliptical pens yield the geometric mean of the two axis lengths, which is the diameter for a circular pen.
/// Polygonal pens approximate with twice the maximum vertex distance from the origin.
pub fn pen_stroke_width(pen: &Pen) -> Scalar {
    match pen {
        Pen::Elliptical(t) => {
            let len1 = t.txx.hypot(t.tyx);
            let len2 = t.txy.hypot(t.tyy);
            2.0 * (len1 * len2).sqrt()
        }
        Pen::Polygonal(vertices) => {
            let max_r = vertices
                .iter()
                .map(|v| Vec2::from(*v).length())
                .fold(0.0, Scalar::max);
            2.0 * max_r
        }
    }
}

pub const fn linecap_to_svg(cap: LineCap) -> &'static str {
    match cap {
        LineCap::Butt => "butt",
        LineCap::Round => "round",
        LineCap::Square => "square",
    }
}

pub const fn linejoin_to_svg(join: LineJoin) -> &'static str {
    match join {
        LineJoin::Miter => "miter",
        LineJoin::Round => "round",
        LineJoin::Bevel => "bevel",
    }
}

pub fn dash_to_svg(dash: &DashPattern, precision: usize) -> String {
    dash.dashes
        .iter()
        .map(|v| format!("{v:.precision$}"))
        .collect::<Vec<_>>()
        .join(",")
}

/// Format a scalar to the given precision, stripping trailing zeros
pub fn fmt_scalar(v: Scalar, precision: usize) -> String {
    let s = format!("{v:.precision$}");
    if s.contains('.') {
        let trimmed = s.trim_end_matches('0').trim_end_matches('.');
        trimmed.to_owned()
    } else {
        s
    }
}
