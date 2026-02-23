//! Bundled font data and name alias table.
//!
//! Embeds New Computer Modern OpenType fonts via `include_bytes!` and
//! maps legacy `MetaPost`/TeX font names to the appropriate embedded font.

use crate::data::FontData;
use crate::error::FontError;

static NEWCM_REGULAR: &[u8] = include_bytes!("../fonts/NewCM10-Regular.otf");
static NEWCM_BOLD: &[u8] = include_bytes!("../fonts/NewCM10-Bold.otf");
static NEWCM_ITALIC: &[u8] = include_bytes!("../fonts/NewCM10-Italic.otf");
static NEWCM_MONO: &[u8] = include_bytes!("../fonts/NewCMMono10-Regular.otf");
static NEWCM_MATH: &[u8] = include_bytes!("../fonts/NewCMMath-Regular.otf");

/// An entry in the font alias table.
struct AliasEntry {
    /// The name as used in `MetaPost` (e.g. `"cmr10"`).
    name: &'static str,
    /// The embedded font bytes.
    bytes: &'static [u8],
}

/// Font alias table: `MetaPost` font names mapped to embedded fonts.
///
/// Names are stored lowercase. Lookup should normalize to lowercase
/// before matching.
static ALIASES: &[AliasEntry] = &[
    // Computer Modern Roman
    AliasEntry {
        name: "cmr10",
        bytes: NEWCM_REGULAR,
    },
    AliasEntry {
        name: "cmr7",
        bytes: NEWCM_REGULAR,
    },
    AliasEntry {
        name: "cmr5",
        bytes: NEWCM_REGULAR,
    },
    // Computer Modern Bold Extended
    AliasEntry {
        name: "cmbx10",
        bytes: NEWCM_BOLD,
    },
    AliasEntry {
        name: "cmbx7",
        bytes: NEWCM_BOLD,
    },
    AliasEntry {
        name: "cmbx5",
        bytes: NEWCM_BOLD,
    },
    // Computer Modern Math Italic
    AliasEntry {
        name: "cmmi10",
        bytes: NEWCM_ITALIC,
    },
    AliasEntry {
        name: "cmmi7",
        bytes: NEWCM_ITALIC,
    },
    AliasEntry {
        name: "cmmi5",
        bytes: NEWCM_ITALIC,
    },
    // Computer Modern Text Italic
    AliasEntry {
        name: "cmti10",
        bytes: NEWCM_ITALIC,
    },
    // Computer Modern Typewriter
    AliasEntry {
        name: "cmtt10",
        bytes: NEWCM_MONO,
    },
    // Computer Modern Math Symbols
    AliasEntry {
        name: "cmsy10",
        bytes: NEWCM_MATH,
    },
    AliasEntry {
        name: "cmsy7",
        bytes: NEWCM_MATH,
    },
    AliasEntry {
        name: "cmsy5",
        bytes: NEWCM_MATH,
    },
    // Computer Modern Math Extension
    AliasEntry {
        name: "cmex10",
        bytes: NEWCM_MATH,
    },
    // Canonical New Computer Modern names
    AliasEntry {
        name: "newcm10-regular",
        bytes: NEWCM_REGULAR,
    },
    AliasEntry {
        name: "newcm10-bold",
        bytes: NEWCM_BOLD,
    },
    AliasEntry {
        name: "newcm10-italic",
        bytes: NEWCM_ITALIC,
    },
    AliasEntry {
        name: "newcmmono10-regular",
        bytes: NEWCM_MONO,
    },
    AliasEntry {
        name: "newcmmath-regular",
        bytes: NEWCM_MATH,
    },
];

/// Load all embedded fonts into a name-to-[`FontData`] map.
///
/// Aliases that map to the same underlying bytes share the same
/// `Arc<[u8]>` allocation.
///
/// # Errors
///
/// Returns [`FontError::ParseError`] if any embedded font fails to parse
/// (should not happen unless the bundled files are corrupt).
pub fn load_embedded() -> Result<Vec<(String, FontData)>, FontError> {
    use std::collections::HashMap;
    use std::sync::Arc;

    // Deduplicate: parse each unique byte slice only once.
    let mut parsed: HashMap<*const u8, FontData> = HashMap::new();
    let mut result = Vec::with_capacity(ALIASES.len());

    for entry in ALIASES {
        let key = entry.bytes.as_ptr();
        let font = if let Some(existing) = parsed.get(&key) {
            existing.clone()
        } else {
            let bytes: Arc<[u8]> = Arc::from(entry.bytes);
            let font = FontData::from_bytes(bytes)?;
            parsed.insert(key, font.clone());
            font
        };
        result.push((entry.name.to_owned(), font));
    }

    Ok(result)
}

#[cfg(test)]
#[expect(clippy::expect_used, reason = "tests may panic")]
mod tests {
    use super::*;

    #[test]
    fn embedded_fonts_parse_successfully() {
        let fonts = load_embedded().expect("embedded fonts should parse");
        assert!(
            fonts.len() >= 15,
            "expected at least 15 alias entries, got {}",
            fonts.len()
        );
    }

    #[test]
    fn cmr10_has_latin_glyphs() {
        let fonts = load_embedded().expect("embedded fonts should parse");
        let (_, cmr10) = fonts.iter().find(|(n, _)| n == "cmr10").expect("cmr10");
        assert!(cmr10.has_glyph('A'), "cmr10 should have 'A'");
        assert!(cmr10.has_glyph('z'), "cmr10 should have 'z'");
        assert!(cmr10.has_glyph('0'), "cmr10 should have '0'");
    }

    #[test]
    fn metrics_are_reasonable() {
        let fonts = load_embedded().expect("embedded fonts should parse");
        let (_, font) = fonts.iter().find(|(n, _)| n == "cmr10").expect("cmr10");
        let m = font.text_metrics("Hello", 10.0);
        // Width should be positive and roughly in range 20-30pt for 5 chars at 10pt
        assert!(m.width > 10.0, "width too small: {}", m.width);
        assert!(m.width < 40.0, "width too large: {}", m.width);
        // Height (ascender) should be roughly 6-9pt
        assert!(m.height > 4.0, "height too small: {}", m.height);
        assert!(m.height < 12.0, "height too large: {}", m.height);
    }

    #[test]
    fn outline_extraction_works() {
        struct Counter {
            moves: usize,
            lines: usize,
            curves: usize,
            closes: usize,
        }

        impl crate::OutlineSink for Counter {
            fn move_to(&mut self, _x: f64, _y: f64) {
                self.moves += 1;
            }
            fn line_to(&mut self, _x: f64, _y: f64) {
                self.lines += 1;
            }
            fn quad_to(&mut self, _: f64, _: f64, _: f64, _: f64) {}
            fn curve_to(&mut self, _: f64, _: f64, _: f64, _: f64, _: f64, _: f64) {
                self.curves += 1;
            }
            fn close(&mut self) {
                self.closes += 1;
            }
        }

        let fonts = load_embedded().expect("embedded fonts should parse");
        let (_, font) = fonts.iter().find(|(n, _)| n == "cmr10").expect("cmr10");
        let gid = font.glyph_id('A').expect("'A' should have a glyph");

        let mut counter = Counter {
            moves: 0,
            lines: 0,
            curves: 0,
            closes: 0,
        };
        let has_outline = font.outline(gid, 10.0, &mut counter);
        assert!(has_outline, "'A' should have an outline");
        assert!(counter.moves > 0, "expected move_to calls");
        assert!(
            counter.lines > 0 || counter.curves > 0,
            "expected line or curve calls"
        );
        assert!(counter.closes > 0, "expected close calls");
    }
}
