use std::collections::HashMap;
use std::sync::Arc;

use postmeta_fonts::FontProvider;
use postmeta_graphics::types::{GraphicsObject, TextObject};
use svg::node::element::{ClipPath, Group, Symbol, Use as SvgUse};

use crate::objects::{render_fill, render_stroke, render_text_raw};
use crate::options::{RenderOptions, TextMode};
use crate::outline::SvgOutlineSink;
use crate::path::path_to_d;
use crate::util::{color_to_svg, fmt_scalar};

pub struct SvgRenderer<'a> {
    opts: &'a RenderOptions,
    fonts: Option<&'a dyn FontProvider>,
    pub clip_defs: Vec<ClipPath>,
    clip_counter: usize,
    pub glyph_defs: Vec<Symbol>,
    glyph_map: HashMap<GlyphKey, String>,
    glyph_counter: usize,
}

#[derive(Hash, Eq, PartialEq)]
struct GlyphKey {
    font_name: Arc<str>,
    glyph_id: u16,
}

impl<'a> SvgRenderer<'a> {
    pub fn new(opts: &'a RenderOptions, fonts: Option<&'a dyn FontProvider>) -> Self {
        Self {
            opts,
            fonts,
            clip_defs: Vec::new(),
            clip_counter: 0,
            glyph_defs: Vec::new(),
            glyph_map: HashMap::new(),
            glyph_counter: 0,
        }
    }

    fn next_clip_id(&mut self) -> String {
        let id = format!("c{}", self.clip_counter);
        self.clip_counter += 1;
        id
    }

    fn ensure_glyph(&mut self, font_name: &Arc<str>, glyph_id: u16) -> Option<String> {
        let key = GlyphKey {
            font_name: Arc::clone(font_name),
            glyph_id,
        };
        if let Some(id) = self.glyph_map.get(&key) {
            return Some(id.clone());
        }

        let font = self.fonts?.font(font_name)?;
        let mut sink = SvgOutlineSink::new(self.opts.precision);
        let design_size = f64::from(font.units_per_em());
        if !font.outline(glyph_id, design_size, &mut sink) {
            return None;
        }

        let sym_id = format!("g{}", self.glyph_counter);
        self.glyph_counter += 1;

        let symbol = Symbol::new()
            .set("id", sym_id.as_str())
            .set("overflow", "visible")
            .add(svg::node::element::Path::new().set("d", sink.into_d()));
        self.glyph_defs.push(symbol);
        self.glyph_map.insert(key, sym_id.clone());
        Some(sym_id)
    }

    pub fn render_objects(&mut self, objects: &[GraphicsObject]) -> Group {
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
                    group = self.render_text_object(group, text);
                    i += 1;
                }
                GraphicsObject::ClipStart(clip_path) => {
                    let end = find_matching_end(objects, i, true);
                    let inner = &objects[i + 1..end];

                    let clip_id = self.next_clip_id();
                    let clip_data = path_to_d(clip_path, self.opts.precision);
                    let clip_def = ClipPath::new()
                        .set("id", clip_id.as_str())
                        .add(svg::node::element::Path::new().set("d", clip_data));
                    self.clip_defs.push(clip_def);

                    let inner_group = self.render_objects(inner);
                    let clipped = Group::new()
                        .set("clip-path", format!("url(#{clip_id})"))
                        .add(inner_group);
                    group = group.add(clipped);

                    i = end + 1;
                }
                GraphicsObject::SetBoundsStart(_) => {
                    let end = find_matching_end(objects, i, false);
                    let inner = &objects[i + 1..end];
                    let inner_group = self.render_objects(inner);
                    group = group.add(inner_group);
                    i = end + 1;
                }
                GraphicsObject::ClipEnd | GraphicsObject::SetBoundsEnd => {
                    i += 1;
                }
            }
        }

        group
    }

    fn render_text_object(&mut self, group: Group, text: &TextObject) -> Group {
        if self.opts.text_mode == TextMode::Paths
            && self.fonts.is_some()
            && let Some(g) = self.render_text_as_paths(text)
        {
            return group.add(g);
        }
        group.add(render_text_raw(text, self.opts))
    }

    fn render_text_as_paths(&mut self, text: &TextObject) -> Option<Group> {
        let font = self.fonts?.font(&text.font_name)?;
        let prec = self.opts.precision;

        let t = &text.transform;
        let matrix = format!(
            "matrix({},{},{},{},{},{})",
            fmt_scalar(t.txx, prec),
            fmt_scalar(-t.tyx, prec),
            fmt_scalar(-t.txy, prec),
            fmt_scalar(t.tyy, prec),
            fmt_scalar(t.tx, prec),
            fmt_scalar(-t.ty, prec),
        );

        let mut g = Group::new()
            .set("transform", matrix)
            .set("fill", color_to_svg(text.color));

        let scale = text.font_size / f64::from(font.units_per_em());
        let mut cursor_x: f64 = 0.0;
        let mut prev_glyph: Option<u16> = None;

        for ch in text.text.chars() {
            let Some(gid) = font.glyph_id(ch) else {
                continue;
            };

            if let Some(prev) = prev_glyph {
                let kern = f64::from(font.kern(prev, gid)) * scale;
                cursor_x += kern;
            }

            if let Some(sym_id) = self.ensure_glyph(&text.font_name, gid) {
                let s = fmt_scalar(scale, prec + 2);
                let ns = fmt_scalar(-scale, prec + 2);
                let use_el = SvgUse::new().set("href", format!("#{sym_id}")).set(
                    "transform",
                    format!(
                        "translate({},0) scale({s},{ns})",
                        fmt_scalar(cursor_x, prec)
                    ),
                );
                g = g.add(use_el);
            }

            if let Some(adv) = font.advance_width(gid) {
                cursor_x += f64::from(adv) * scale;
            }
            prev_glyph = Some(gid);
        }

        Some(g)
    }
}

/// Find the matching `ClipEnd` or `SetBoundsEnd` for a start bracket at
/// index `start`. Returns the index of the matching end bracket.
pub fn find_matching_end(objects: &[GraphicsObject], start: usize, is_clip: bool) -> usize {
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
    objects.len()
}
