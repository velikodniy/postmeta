use postmeta_graphics::types::{Color, DashPattern, LineCap, LineJoin, Pen, Scalar, Vec2};

/// Convert a [`Color`] to an SVG color string.
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

/// Extract stroke width from a pen.
///
/// For elliptical pens, returns the geometric mean of the two axis lengths
/// (which equals the diameter for a circular pen). For polygonal pens,
/// returns the maximum vertex distance from the origin (approximation).
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

/// Format a scalar to the given precision, stripping trailing zeros.
pub fn fmt_scalar(v: Scalar, precision: usize) -> String {
    let s = format!("{v:.precision$}");
    if s.contains('.') {
        let trimmed = s.trim_end_matches('0').trim_end_matches('.');
        trimmed.to_owned()
    } else {
        s
    }
}
