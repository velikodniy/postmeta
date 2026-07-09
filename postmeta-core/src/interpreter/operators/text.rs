//! Text metrics and font-related operators

use std::sync::Arc;

use postmeta_fonts::FontProvider;
use postmeta_graphics::types::{
    Color, GraphicsObject, Picture, TextMetrics, TextObject, Transform,
};

use crate::error::InterpResult;
use crate::interpreter::helpers::value_to_string;
use crate::types::{Type, Value};

/// Evaluate the `fontsize` operator
pub(super) fn font_size(
    input: &Value,
    fonts: Option<&dyn FontProvider>,
) -> InterpResult<(Value, Type)> {
    let name = value_to_string(input)?;
    // OpenType fonts don't carry a design size; return 10pt (MetaPost convention for CMR), extracting the size when the font name encodes one (cmr7, cmr5)
    let size = extract_design_size(&name).unwrap_or(10.0);
    let _ = fonts; // available for future per-font metadata
    Ok((Value::Numeric(size), Type::Known))
}

/// Evaluate the `infont` operator, producing a one-object text picture
pub(super) fn infont(
    left: &Value,
    right: &Value,
    fonts: Option<&dyn FontProvider>,
) -> InterpResult<(Value, Type)> {
    let text = value_to_string(left)?;
    let font_name = value_to_string(right)?;
    // MetaPost uses 10pt for the design size; `plain.mp` applies `scaled defaultscale` after infont
    let font_size = 10.0;
    let metrics = compute_text_metrics(text.as_ref(), font_name.as_ref(), font_size, fonts);
    let text_obj = TextObject {
        text: Arc::from(text.as_ref()),
        font_name: Arc::from(font_name.as_ref()),
        font_size,
        metrics,
        color: Color::BLACK,
        transform: Transform::IDENTITY,
    };
    let mut pic = Picture::new();
    pic.push(GraphicsObject::Text(text_obj));
    Ok((Value::Picture(pic), Type::Picture))
}

/// Compute text metrics using the font provider if available, otherwise fall back to a rough heuristic (0.5 × `font_size` per character, 0.8/0.2 split for ascender/descender)
pub(in crate::interpreter) fn compute_text_metrics(
    text: &str,
    font_name: &str,
    font_size: f64,
    fonts: Option<&dyn FontProvider>,
) -> TextMetrics {
    if let Some(provider) = fonts {
        if let Some(font) = provider.font(font_name) {
            let fm = font.text_metrics(text, font_size);
            return TextMetrics {
                width: fm.width,
                height: fm.height,
                depth: fm.depth,
            };
        }
    }
    heuristic_text_metrics(text, font_size)
}

/// Extract the trailing numeric suffix from a CM font name (e.g. "cmr10" → 10), or `None` if it has none
fn extract_design_size(font_name: &str) -> Option<f64> {
    let suffix_start = font_name.rfind(|c: char| !c.is_ascii_digit())?;
    let suffix = &font_name[suffix_start + 1..];
    if suffix.is_empty() {
        return None;
    }
    suffix.parse().ok()
}

/// Rough text metrics when no font data is available
fn heuristic_text_metrics(text: &str, font_size: f64) -> TextMetrics {
    #[expect(
        clippy::cast_precision_loss,
        reason = "character count fits comfortably in f64"
    )]
    let char_count = text.chars().count() as f64;
    TextMetrics {
        width: 0.5 * font_size * char_count,
        height: 0.8 * font_size,
        depth: 0.2 * font_size,
    }
}
