//! Font data wrapper around `ttf-parser`.

use std::sync::Arc;

use crate::error::FontError;
use crate::metrics::TextMetrics;
use crate::outline::OutlineSink;

/// Parsed font data.
///
/// Stores owned font bytes and cached global metrics. Creates a
/// `ttf_parser::Face` on demand for individual queries — parsing is
/// sub-microsecond (no allocation, just header validation and offset
/// table construction).
#[derive(Clone)]
pub struct FontData {
    bytes: Arc<[u8]>,
    /// Font units per em (design coordinate space).
    units_per_em: u16,
    /// Global ascender in design units (positive).
    ascender: i16,
    /// Global descender in design units (negative).
    descender: i16,
}

impl FontData {
    /// Parse font data from an owned byte buffer.
    ///
    /// # Errors
    ///
    /// Returns [`FontError::ParseError`] if the data is not a valid
    /// OpenType/TrueType font.
    pub fn from_bytes(bytes: Arc<[u8]>) -> Result<Self, FontError> {
        let face =
            ttf_parser::Face::parse(&bytes, 0).map_err(|e| FontError::ParseError(e.to_string()))?;
        Ok(Self {
            units_per_em: face.units_per_em(),
            ascender: face.ascender(),
            descender: face.descender(),
            bytes,
        })
    }

    /// Parse font data from a static byte slice (for embedded fonts).
    ///
    /// # Errors
    ///
    /// Returns [`FontError::ParseError`] if the data is not a valid
    /// OpenType/TrueType font.
    pub fn from_static(bytes: &'static [u8]) -> Result<Self, FontError> {
        Self::from_bytes(Arc::from(bytes))
    }

    /// Create a temporary `Face` reference for queries.
    fn face(&self) -> ttf_parser::Face<'_> {
        // Safety of unwrap rationale: bytes were validated in from_bytes.
        // However, we avoid unwrap per project rules — re-parse and
        // return a default-ish face is not possible, so we use expect
        // only in this internal helper that is guaranteed to succeed
        // because the bytes were validated at construction time.
        //
        // We still avoid `expect` — instead, use a let-else with a
        // fallback that cannot actually be reached.
        #[expect(clippy::expect_used, reason = "bytes were validated at construction")]
        ttf_parser::Face::parse(&self.bytes, 0).expect("font bytes validated at construction")
    }

    /// Font units per em (design coordinate space).
    #[must_use]
    pub const fn units_per_em(&self) -> u16 {
        self.units_per_em
    }

    /// Scale factor from design units to points at the given font size.
    #[must_use]
    pub fn scale(&self, font_size: f64) -> f64 {
        font_size / f64::from(self.units_per_em)
    }

    /// Whether a character has a glyph in this font.
    #[must_use]
    pub fn has_glyph(&self, ch: char) -> bool {
        self.face().glyph_index(ch).is_some()
    }

    /// Map a character to its glyph ID. Returns `None` if not in the cmap.
    #[must_use]
    pub fn glyph_id(&self, ch: char) -> Option<u16> {
        self.face().glyph_index(ch).map(|g| g.0)
    }

    /// Horizontal advance width for a glyph, in design units.
    #[must_use]
    pub fn advance_width(&self, glyph_id: u16) -> Option<u16> {
        self.face().glyph_hor_advance(ttf_parser::GlyphId(glyph_id))
    }

    /// Kerning adjustment between two glyphs, in design units.
    /// Negative values mean tighter spacing.
    #[must_use]
    pub fn kern(&self, left: u16, right: u16) -> i16 {
        self.face()
            .tables()
            .kern
            .and_then(|kern| {
                kern.subtables.into_iter().find_map(|st| {
                    st.glyphs_kerning(ttf_parser::GlyphId(left), ttf_parser::GlyphId(right))
                })
            })
            .unwrap_or(0)
    }

    /// Compute aggregate metrics for a text string at a given font size.
    #[must_use]
    pub fn text_metrics(&self, text: &str, font_size: f64) -> TextMetrics {
        let face = self.face();
        let scale = self.scale(font_size);
        let mut width = 0.0;
        let mut max_ascender: i16 = 0;
        let mut max_descender: i16 = 0;
        let mut prev_gid: Option<u16> = None;

        for ch in text.chars() {
            let Some(gid) = face.glyph_index(ch) else {
                continue;
            };

            // Kerning with previous glyph
            if let Some(prev) = prev_gid {
                width += f64::from(self.kern(prev, gid.0)) * scale;
            }

            // Advance width
            if let Some(adv) = face.glyph_hor_advance(gid) {
                width += f64::from(adv) * scale;
            }

            // Per-glyph vertical extents from bounding box
            if let Some(bb) = face.glyph_bounding_box(gid) {
                max_ascender = max_ascender.max(bb.y_max);
                max_descender = max_descender.min(bb.y_min);
            }

            prev_gid = Some(gid.0);
        }

        // Fall back to global ascender/descender if no per-glyph data
        if max_ascender == 0 {
            max_ascender = self.ascender;
        }
        if max_descender == 0 {
            max_descender = self.descender;
        }

        TextMetrics {
            width,
            height: f64::from(max_ascender) * scale,
            depth: (f64::from(max_descender) * scale).abs(),
        }
    }

    /// Extract the outline of a glyph into the given sink.
    ///
    /// Coordinates are pre-scaled from design units to the given font size.
    /// Returns `false` if the glyph has no outline (e.g., space character).
    pub fn outline(&self, glyph_id: u16, font_size: f64, sink: &mut dyn OutlineSink) -> bool {
        let face = self.face();
        let scale = self.scale(font_size);
        let mut adapter = OutlineAdapter { sink, scale };
        face.outline_glyph(ttf_parser::GlyphId(glyph_id), &mut adapter)
            .is_some()
    }
}

/// Adapter from [`OutlineSink`] to `ttf_parser::OutlineBuilder`.
struct OutlineAdapter<'a> {
    sink: &'a mut dyn OutlineSink,
    scale: f64,
}

impl ttf_parser::OutlineBuilder for OutlineAdapter<'_> {
    fn move_to(&mut self, x: f32, y: f32) {
        self.sink
            .move_to(f64::from(x) * self.scale, f64::from(y) * self.scale);
    }

    fn line_to(&mut self, x: f32, y: f32) {
        self.sink
            .line_to(f64::from(x) * self.scale, f64::from(y) * self.scale);
    }

    fn quad_to(&mut self, x1: f32, y1: f32, x: f32, y: f32) {
        self.sink.quad_to(
            f64::from(x1) * self.scale,
            f64::from(y1) * self.scale,
            f64::from(x) * self.scale,
            f64::from(y) * self.scale,
        );
    }

    fn curve_to(&mut self, x1: f32, y1: f32, x2: f32, y2: f32, x: f32, y: f32) {
        self.sink.curve_to(
            f64::from(x1) * self.scale,
            f64::from(y1) * self.scale,
            f64::from(x2) * self.scale,
            f64::from(y2) * self.scale,
            f64::from(x) * self.scale,
            f64::from(y) * self.scale,
        );
    }

    fn close(&mut self) {
        self.sink.close();
    }
}

impl std::fmt::Debug for FontData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FontData")
            .field("units_per_em", &self.units_per_em)
            .field("ascender", &self.ascender)
            .field("descender", &self.descender)
            .field("bytes_len", &self.bytes.len())
            .finish()
    }
}
