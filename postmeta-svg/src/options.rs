use postmeta_graphics::types::Scalar;

/// How text is rendered in SVG output.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum TextMode {
    /// Render text as glyph outline paths (`<symbol>`/`<use>`).
    /// Produces self-contained SVG that does not depend on installed fonts.
    /// Requires a [`postmeta_fonts::FontProvider`]; falls back to
    /// [`Raw`](TextMode::Raw) per-label when the font is unavailable.
    #[default]
    Paths,
    /// Render text as `<text>` elements with `font-family` attributes.
    /// Requires the viewer to have the font installed.
    Raw,
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
    /// How text labels are rendered. Default: [`TextMode::Paths`].
    pub text_mode: TextMode,
}

impl Default for RenderOptions {
    fn default() -> Self {
        Self {
            margin: 1.0,
            precision: 4,
            true_corners: false,
            text_mode: TextMode::default(),
        }
    }
}
