//! SVG renderer for `PostMeta` pictures.
//!
//! Converts a [`Picture`] into an SVG [`Document`] using the `svg` crate.

mod document;
mod objects;
mod options;
mod outline;
mod path;
mod renderer;
mod util;

#[cfg(test)]
mod tests;

use postmeta_fonts::FontProvider;
use postmeta_graphics::bbox::BoundingBox;
use postmeta_graphics::types::Picture;
use svg::Document;

pub use options::{RenderOptions, TextMode};

/// Render a [`Picture`] to an SVG [`Document`].
///
/// Uses default options and no font provider (text is rendered as raw
/// `<text>` elements).
#[must_use]
pub fn render(picture: &Picture) -> Document {
    render_with_options(picture, &RenderOptions::default())
}

/// Render a [`Picture`] to an SVG string.
#[must_use]
pub fn render_to_string(picture: &Picture) -> String {
    render(picture).to_string()
}

/// Render a [`Picture`] to an SVG [`Document`] with custom options.
///
/// Backward-compatible: no font provider, text rendered as `<text>`.
#[must_use]
pub fn render_with_options(picture: &Picture, opts: &RenderOptions) -> Document {
    render_with_fonts(picture, opts, None)
}

/// Render a [`Picture`] to an SVG [`Document`] with custom options and
/// an optional font provider.
///
/// This is the primary entry point when font-aware rendering is desired.
/// Pass `None` for the font provider to get the same behavior as
/// [`render_with_options`].
#[must_use]
pub fn render_with_fonts(
    picture: &Picture,
    opts: &RenderOptions,
    fonts: Option<&dyn FontProvider>,
) -> Document {
    let bb = BoundingBox::of_picture(picture, opts.true_corners);
    let mut renderer = renderer::SvgRenderer::new(opts, fonts);
    let content = renderer.render_objects(&picture.objects);

    document::build_document(
        &bb,
        opts,
        content,
        &renderer.clip_defs,
        &renderer.glyph_defs,
    )
}
