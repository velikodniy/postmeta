//! SVG renderer for `PostMeta` pictures
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
use postmeta_graphics::bbox::{BoundingBox, Corners};
use postmeta_graphics::types::Picture;
use svg::Document;

pub use options::{RenderOptions, TextMode};

/// Render a [`Picture`] to an SVG [`Document`]
///
/// Uses default options and no font provider, so text becomes raw `<text>` elements.
#[must_use]
pub fn render(picture: &Picture) -> Document {
    render_with_options(picture, &RenderOptions::default())
}

/// Render a [`Picture`] to an SVG string
#[must_use]
pub fn render_to_string(picture: &Picture) -> String {
    render(picture).to_string()
}

/// Render a [`Picture`] to an SVG [`Document`] with custom options
///
/// No font provider is used, so text becomes raw `<text>` elements.
#[must_use]
pub fn render_with_options(picture: &Picture, opts: &RenderOptions) -> Document {
    render_with_fonts(picture, opts, None)
}

/// Render a [`Picture`] to an SVG [`Document`] with custom options and an optional font provider
///
/// This is the primary entry point for font-aware rendering; passing `None` behaves like [`render_with_options`].
#[must_use]
pub fn render_with_fonts(
    picture: &Picture,
    opts: &RenderOptions,
    fonts: Option<&dyn FontProvider>,
) -> Document {
    let corners = if opts.true_corners {
        Corners::True
    } else {
        Corners::HonorSetBounds
    };
    let bb = BoundingBox::of_picture(picture, corners);
    let mut renderer = renderer::SvgRenderer::new(opts, fonts);
    let content = renderer.render_objects(picture.objects());

    document::build_document(
        &bb,
        opts,
        content,
        &renderer.clip_defs,
        &renderer.glyph_defs,
    )
}
