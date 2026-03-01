use postmeta_fonts::OutlineSink;

/// Collects glyph outline commands into an SVG `d` attribute string.
///
/// Coordinates are in font design units (Y-up), matching the `<symbol>`
/// coordinate space. The per-glyph `<use>` element applies scaling.
pub struct SvgOutlineSink {
    d: String,
    precision: usize,
}

impl SvgOutlineSink {
    pub fn new(precision: usize) -> Self {
        Self {
            d: String::with_capacity(256),
            precision,
        }
    }

    pub fn into_d(self) -> String {
        self.d
    }
}

impl OutlineSink for SvgOutlineSink {
    fn move_to(&mut self, x: f64, y: f64) {
        use std::fmt::Write;
        let p = self.precision;
        let _ = write!(self.d, "M{x:.p$},{y:.p$}");
    }

    fn line_to(&mut self, x: f64, y: f64) {
        use std::fmt::Write;
        let p = self.precision;
        let _ = write!(self.d, "L{x:.p$},{y:.p$}");
    }

    fn quad_to(&mut self, x1: f64, y1: f64, x: f64, y: f64) {
        use std::fmt::Write;
        let p = self.precision;
        let _ = write!(self.d, "Q{x1:.p$},{y1:.p$} {x:.p$},{y:.p$}");
    }

    fn curve_to(&mut self, x1: f64, y1: f64, x2: f64, y2: f64, x: f64, y: f64) {
        use std::fmt::Write;
        let p = self.precision;
        let _ = write!(
            self.d,
            "C{x1:.p$},{y1:.p$} {x2:.p$},{y2:.p$} {x:.p$},{y:.p$}"
        );
    }

    fn close(&mut self) {
        self.d.push('Z');
    }
}
