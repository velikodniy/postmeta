use postmeta_graphics::bbox::BoundingBox;
use svg::Document;
use svg::node::element::{ClipPath, Definitions, Group, Symbol};

use crate::options::RenderOptions;
use crate::util::fmt_scalar;

/// Build the final SVG [`Document`] from rendered content and defs.
///
/// The `viewBox` is computed by negating the Y range from the `MetaPost`
/// bounding box: SVG `min_y = -bb.max_y`, SVG `max_y = -bb.min_y`.
pub fn build_document(
    bb: &BoundingBox,
    opts: &RenderOptions,
    content: Group,
    clip_defs: &[ClipPath],
    glyph_defs: &[Symbol],
) -> Document {
    let m = opts.margin;

    let (vb_x, vb_y, vb_w, vb_h) = if bb.is_valid() {
        (
            bb.min_x - m,
            -bb.max_y - m,
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

    if !clip_defs.is_empty() || !glyph_defs.is_empty() {
        let mut defs = Definitions::new();
        for sym in glyph_defs {
            defs = defs.add(sym.clone());
        }
        for clip in clip_defs {
            defs = defs.add(clip.clone());
        }
        doc = doc.add(defs);
    }

    doc.add(content)
}
