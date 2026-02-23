//! SVG renderer for `PostMeta` pictures.
//!
//! Converts a [`Picture`] into an SVG [`Document`] using the `svg` crate.
//!
//! Key design points:
//! - `MetaPost` coordinates have Y pointing **up**; SVG has Y pointing **down**.
//!   All Y coordinates are negated at render time so that no global transform
//!   or `viewBox` trick is needed. Text renders right-side up naturally.
//! - Path data is built as raw `d` strings to preserve `f64` precision
//!   (the `svg` crate's `Data` builder uses `f32`).
//! - Clip regions produce `<defs><clipPath>...</clipPath></defs>` plus
//!   `<g clip-path="url(#...)">` groups.
//! - `SetBounds` regions are transparent in SVG (they only affect
//!   bounding-box computation at the `MetaPost` level).

use postmeta_graphics::path::Path;
use svg::Document;
use svg::node::element::{ClipPath, Definitions, Group, Text as SvgText};

use postmeta_graphics::bbox::{BoundingBox, picture_bbox};
use postmeta_graphics::types::{
    Color, DashPattern, FillObject, GraphicsObject, KnotDirection, LineCap, LineJoin, Pen, Picture,
    Scalar, StrokeObject, TextObject, Vec2,
};

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Render a [`Picture`] to an SVG [`Document`].
///
/// The resulting document has a `viewBox` derived from the picture's
/// bounding box (with a small margin) and uses PostScript points as units.
#[must_use]
pub fn render(picture: &Picture) -> Document {
    render_with_options(picture, &RenderOptions::default())
}

/// Render a [`Picture`] to an SVG string.
#[must_use]
pub fn render_to_string(picture: &Picture) -> String {
    render(picture).to_string()
}

/// Options controlling SVG output.
#[derive(Debug, Clone)]
pub struct RenderOptions {
    /// Extra margin around the bounding box (in bp). Default: 1.0.
    pub margin: Scalar,
    /// Number of decimal places for coordinates. Default: 4.
    pub precision: usize,
    /// Whether to use `truecorners` for bounding-box computation.
    /// When false, `setbounds` regions override the computed bbox.
    pub true_corners: bool,
}

impl Default for RenderOptions {
    fn default() -> Self {
        Self {
            margin: 1.0,
            precision: 4,
            true_corners: false,
        }
    }
}

/// Render a [`Picture`] to an SVG [`Document`] with custom options.
#[must_use]
pub fn render_with_options(picture: &Picture, opts: &RenderOptions) -> Document {
    let bb = picture_bbox(picture, opts.true_corners);
    let mut state = RenderState::new(opts);
    let content = state.render_objects(&picture.objects);

    build_document(&bb, opts, content, &state.defs)
}

// ---------------------------------------------------------------------------
// Render state (tracks clip IDs and defs)
// ---------------------------------------------------------------------------

struct RenderState<'a> {
    opts: &'a RenderOptions,
    /// Accumulated `<defs>` content (clip paths).
    defs: Vec<ClipPath>,
    /// Counter for generating unique clip-path IDs.
    clip_counter: usize,
}

impl<'a> RenderState<'a> {
    const fn new(opts: &'a RenderOptions) -> Self {
        Self {
            opts,
            defs: Vec::new(),
            clip_counter: 0,
        }
    }

    fn next_clip_id(&mut self) -> String {
        let id = format!("c{}", self.clip_counter);
        self.clip_counter += 1;
        id
    }

    /// Render a slice of [`GraphicsObject`]s into a [`Group`].
    ///
    /// Handles `ClipStart`/`ClipEnd` and `SetBoundsStart`/`SetBoundsEnd`
    /// bracketing by recursing into nested groups.
    fn render_objects(&mut self, objects: &[GraphicsObject]) -> Group {
        let mut group = Group::new();
        let mut i = 0;

        while i < objects.len() {
            match &objects[i] {
                GraphicsObject::Fill(fill) => {
                    group = group.add(render_fill(fill, self.opts));
                    i += 1;
                }
                GraphicsObject::Stroke(stroke) => {
                    group = group.add(render_stroke(stroke, self.opts));
                    i += 1;
                }
                GraphicsObject::Text(text) => {
                    group = group.add(render_text(text, self.opts));
                    i += 1;
                }
                GraphicsObject::ClipStart(clip_path) => {
                    // Find matching ClipEnd
                    let end = find_matching_end(objects, i, true);
                    let inner = &objects[i + 1..end];

                    let clip_id = self.next_clip_id();
                    let clip_data = path_to_d(clip_path, self.opts.precision);
                    let clip_def = ClipPath::new()
                        .set("id", clip_id.as_str())
                        .add(svg::node::element::Path::new().set("d", clip_data));
                    self.defs.push(clip_def);

                    let inner_group = self.render_objects(inner);
                    let clipped = Group::new()
                        .set("clip-path", format!("url(#{clip_id})"))
                        .add(inner_group);
                    group = group.add(clipped);

                    i = end + 1;
                }
                GraphicsObject::ClipEnd => {
                    // Should not appear outside of a matched pair; skip.
                    i += 1;
                }
                GraphicsObject::SetBoundsStart(_) => {
                    // SetBounds is transparent in SVG output — just render contents.
                    let end = find_matching_end(objects, i, false);
                    let inner = &objects[i + 1..end];
                    let inner_group = self.render_objects(inner);
                    group = group.add(inner_group);
                    i = end + 1;
                }
                GraphicsObject::SetBoundsEnd => {
                    i += 1;
                }
            }
        }

        group
    }
}

// ---------------------------------------------------------------------------
// Individual object renderers
// ---------------------------------------------------------------------------

/// Render a filled contour to an SVG `<path>` element.
fn render_fill(fill: &FillObject, opts: &RenderOptions) -> svg::node::element::Path {
    let d = path_to_d(&fill.path, opts.precision);
    let mut el = svg::node::element::Path::new()
        .set("d", d)
        .set("fill", color_to_svg(fill.color));

    // If there is a pen, this is a "filldraw" — also stroke the outline.
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

/// Render a stroked path to an SVG `<path>` element.
fn render_stroke(stroke: &StrokeObject, opts: &RenderOptions) -> svg::node::element::Path {
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

/// Render a text label to an SVG `<text>` element.
///
/// Y coordinates are negated to convert from `MetaPost` (Y-up) to SVG
/// (Y-down). The transform matrix is adjusted accordingly.
fn render_text(text: &TextObject, opts: &RenderOptions) -> SvgText {
    let t = &text.transform;
    // MetaPost transform: (x,y) → (txx·x + txy·y + tx, tyx·x + tyy·y + ty)
    // SVG matrix(a,b,c,d,e,f): (x,y) → (a·x + c·y + e, b·x + d·y + f)
    //
    // To convert a MetaPost rotation/scale to SVG (Y-flipped) coordinates,
    // conjugate the 2×2 part by the Y-flip matrix S = diag(1,-1):
    //   M_svg = S · M_mp · S = [txx, -txy; -tyx, tyy]
    // Translation: (tx, -ty).
    let matrix = format!(
        "matrix({},{},{},{},{},{})",
        fmt_scalar(t.txx, opts.precision),
        fmt_scalar(-t.tyx, opts.precision),
        fmt_scalar(-t.txy, opts.precision),
        fmt_scalar(t.tyy, opts.precision),
        fmt_scalar(t.tx, opts.precision),
        fmt_scalar(-t.ty, opts.precision),
    );

    SvgText::new(text.text.as_ref())
        .set("transform", matrix)
        .set("font-family", text.font_name.as_ref())
        .set("font-size", fmt_scalar(text.font_size, opts.precision))
        .set("fill", color_to_svg(text.color))
}

// ---------------------------------------------------------------------------
// Path → SVG "d" attribute
// ---------------------------------------------------------------------------

/// Convert a resolved [`Path`] to an SVG path data string.
///
/// Uses cubic Bezier commands (M, C, Z). All coordinates are f64 with
/// the specified precision. Y coordinates are negated to convert from
/// `MetaPost` (Y-up) to SVG (Y-down).
fn path_to_d(path: &Path, precision: usize) -> String {
    if path.knots.is_empty() {
        return String::new();
    }

    let mut d = String::with_capacity(path.knots.len() * 40);
    let p0 = path.knots[0].point;
    d.push('M');
    write_point(&mut d, p0.x, -p0.y, precision);

    let n = path.num_segments();
    for i in 0..n {
        let j = (i + 1) % path.knots.len();
        let k0 = &path.knots[i];
        let k1 = &path.knots[j];

        let cp1 = match k0.right {
            KnotDirection::Explicit(p) => p,
            _ => k0.point,
        };
        let cp2 = match k1.left {
            KnotDirection::Explicit(p) => p,
            _ => k1.point,
        };

        d.push('C');
        write_point(&mut d, cp1.x, -cp1.y, precision);
        d.push(' ');
        write_point(&mut d, cp2.x, -cp2.y, precision);
        d.push(' ');
        write_point(&mut d, k1.point.x, -k1.point.y, precision);
    }

    if path.is_cyclic {
        d.push('Z');
    }

    d
}

/// Write "x,y" to the string with the given precision.
///
/// Normalizes negative zero to positive zero for cleaner output.
fn write_point(d: &mut String, x: Scalar, y: Scalar, precision: usize) {
    use std::fmt::Write;
    let x = if x == 0.0 { 0.0 } else { x };
    let y = if y == 0.0 { 0.0 } else { y };
    let _ = write!(d, "{x:.precision$},{y:.precision$}");
}

// ---------------------------------------------------------------------------
// Color / pen / attribute helpers
// ---------------------------------------------------------------------------

/// Convert a [`Color`] to an SVG color string.
#[expect(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "color components are clamped to [0, 255]"
)]
fn color_to_svg(c: Color) -> String {
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
///
/// Returns `(width, is_elliptical)`.
fn pen_stroke_width(pen: &Pen) -> Scalar {
    match pen {
        Pen::Elliptical(t) => {
            // The two column vectors of the 2×2 matrix part
            let len1 = t.txx.hypot(t.tyx);
            let len2 = t.txy.hypot(t.tyy);
            // Diameter = 2 * geometric mean of semi-axes
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

const fn linecap_to_svg(cap: LineCap) -> &'static str {
    match cap {
        LineCap::Butt => "butt",
        LineCap::Round => "round",
        LineCap::Square => "square",
    }
}

const fn linejoin_to_svg(join: LineJoin) -> &'static str {
    match join {
        LineJoin::Miter => "miter",
        LineJoin::Round => "round",
        LineJoin::Bevel => "bevel",
    }
}

fn dash_to_svg(dash: &DashPattern, precision: usize) -> String {
    dash.dashes
        .iter()
        .map(|v| format!("{v:.precision$}"))
        .collect::<Vec<_>>()
        .join(",")
}

/// Format a scalar to the given precision, stripping trailing zeros.
fn fmt_scalar(v: Scalar, precision: usize) -> String {
    let s = format!("{v:.precision$}");
    // Strip trailing zeros after decimal point, but keep at least one digit.
    if s.contains('.') {
        let trimmed = s.trim_end_matches('0').trim_end_matches('.');
        trimmed.to_owned()
    } else {
        s
    }
}

// ---------------------------------------------------------------------------
// Bracket matching for ClipStart/ClipEnd and SetBoundsStart/SetBoundsEnd
// ---------------------------------------------------------------------------

/// Find the matching `ClipEnd` or `SetBoundsEnd` for a start bracket at
/// index `start`. Returns the index of the matching end bracket.
fn find_matching_end(objects: &[GraphicsObject], start: usize, is_clip: bool) -> usize {
    let mut depth = 0;
    for (offset, obj) in objects[start..].iter().enumerate() {
        match obj {
            GraphicsObject::ClipStart(_) if is_clip => depth += 1,
            GraphicsObject::ClipEnd if is_clip => {
                depth -= 1;
                if depth == 0 {
                    return start + offset;
                }
            }
            GraphicsObject::SetBoundsStart(_) if !is_clip => depth += 1,
            GraphicsObject::SetBoundsEnd if !is_clip => {
                depth -= 1;
                if depth == 0 {
                    return start + offset;
                }
            }
            _ => {}
        }
    }
    // Fallback: end of array (malformed input).
    objects.len()
}

// ---------------------------------------------------------------------------
// Document assembly
// ---------------------------------------------------------------------------

/// Build the final SVG [`Document`] from rendered content and defs.
///
/// The `viewBox` is computed by negating the Y range from the `MetaPost`
/// bounding box: SVG `min_y = -bb.max_y`, SVG `max_y = -bb.min_y`.
fn build_document(
    bb: &BoundingBox,
    opts: &RenderOptions,
    content: Group,
    clip_defs: &[ClipPath],
) -> Document {
    let m = opts.margin;

    let (vb_x, vb_y, vb_w, vb_h) = if bb.is_valid() {
        (
            bb.min_x - m,
            -bb.max_y - m, // MetaPost max_y → SVG min_y (negated)
            2.0f64.mul_add(m, bb.max_x - bb.min_x),
            2.0f64.mul_add(m, bb.max_y - bb.min_y),
        )
    } else {
        (0.0, 0.0, 100.0, 100.0)
    };

    let mut doc = Document::new()
        .set("xmlns", "http://www.w3.org/2000/svg")
        .set(
            "viewBox",
            format!(
                "{} {} {} {}",
                fmt_scalar(vb_x, opts.precision),
                fmt_scalar(vb_y, opts.precision),
                fmt_scalar(vb_w, opts.precision),
                fmt_scalar(vb_h, opts.precision),
            ),
        )
        .set("width", format!("{}pt", fmt_scalar(vb_w, opts.precision)))
        .set("height", format!("{}pt", fmt_scalar(vb_h, opts.precision)));

    if !clip_defs.is_empty() {
        let mut defs = Definitions::new();
        for clip in clip_defs {
            defs = defs.add(clip.clone());
        }
        doc = doc.add(defs);
    }

    doc.add(content)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use postmeta_graphics::picture::{addto_contour, addto_doublepath};
    use postmeta_graphics::types::{Knot, KnotDirection, Point, StrokeObject, Transform};

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

    /// Make a resolved square 0,0 → 10,0 → 10,10 → 0,10 → cycle.
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

    // -- path_to_d tests --

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
        assert!(!d.contains('Z')); // open path
        // Line is at y=0 in MetaPost → y=0 in SVG (negating 0 is still 0)
        assert!(d.starts_with("M0.00,0.00"), "unexpected start: {d}");
    }

    #[test]
    fn test_path_to_d_y_negation() {
        // A point at (5, 10) in MetaPost should become (5, -10) in SVG
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

    // -- color tests --

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

    // -- pen_stroke_attrs tests --

    #[test]
    fn test_pen_stroke_width_circle() {
        let pen = Pen::circle(2.0); // diameter 2 → radius 1
        let width = pen_stroke_width(&pen);
        // scale(1) → len1=1, len2=1 → width = 2*sqrt(1*1) = 2
        assert!((width - 2.0).abs() < 0.01, "width = {width}");
    }

    #[test]
    fn test_pen_stroke_width_nullpen() {
        let pen = Pen::Elliptical(Transform::ZERO);
        let width = pen_stroke_width(&pen);
        assert!(width.abs() < 0.001);
    }

    // -- fmt_scalar tests --

    #[test]
    fn test_fmt_scalar_trailing_zeros() {
        assert_eq!(fmt_scalar(1.0, 4), "1");
        assert_eq!(fmt_scalar(1.5, 4), "1.5");
        assert_eq!(fmt_scalar(1.25, 4), "1.25");
    }

    // -- dash tests --

    #[test]
    fn test_dash_to_svg() {
        let dash = DashPattern {
            dashes: vec![5.0, 3.0],
            offset: 0.0,
        };
        assert_eq!(dash_to_svg(&dash, 1), "5.0,3.0");
    }

    // -- render_fill / render_stroke integration --

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

    // -- full render tests --

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
        addto_contour(
            &mut pic,
            FillObject {
                path: make_square(),
                color: Color::new(0.0, 0.0, 1.0),
                pen: None,
                line_join: LineJoin::Round,
                miter_limit: 10.0,
            },
        );
        let svg = render_to_string(&pic);
        assert!(svg.contains("fill=\"#0000ff\""), "missing blue fill: {svg}");
        // No global scale(1,-1) — Y flip is per-coordinate
        assert!(
            !svg.contains("scale(1,-1)"),
            "should not have global Y flip: {svg}"
        );
    }

    #[test]
    fn test_render_stroked_line() {
        let mut pic = Picture::new();
        addto_doublepath(
            &mut pic,
            StrokeObject {
                path: make_line(),
                pen: Pen::circle(1.0),
                color: Color::BLACK,
                dash: None,
                line_cap: LineCap::Round,
                line_join: LineJoin::Round,
                miter_limit: 10.0,
            },
        );
        let svg = render_to_string(&pic);
        assert!(svg.contains("stroke=\"black\""), "missing stroke: {svg}");
        assert!(svg.contains("stroke-width="), "missing stroke-width: {svg}");
    }

    #[test]
    fn test_render_with_clip() {
        let mut pic = Picture::new();
        // Manually construct a clipped picture
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
        use postmeta_graphics::types::{TextMetrics, TextObject, Transform};
        use std::sync::Arc;

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
        // Text at ty=25 → SVG ty=-25
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
        addto_contour(
            &mut pic,
            FillObject {
                path: make_square(),
                color: Color::BLACK,
                pen: None,
                line_join: LineJoin::Round,
                miter_limit: 10.0,
            },
        );
        let svg = render_to_string(&pic);
        // The viewBox should span roughly the square's bounds with margin
        assert!(svg.contains("viewBox="), "missing viewBox: {svg}");
        // Width/height should reflect bbox
        assert!(svg.contains("pt\""), "missing pt units: {svg}");
    }
}
