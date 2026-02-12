//! Internal quantities for the `MetaPost` interpreter.
//!
//! Internal quantities are named numeric values that control interpreter
//! behavior (tracing, drawing parameters, etc.). They are accessed via
//! the `InternalQuantity` command and set via `:=` or `interim`.
//!
//! This corresponds to `mp.web`'s `internal` array.

use postmeta_graphics::types::Scalar;

// ---------------------------------------------------------------------------
// Well-known internal indices
// ---------------------------------------------------------------------------

/// Indices for built-in internal quantities.
///
/// User-defined internals (via `newinternal`) get indices above
/// `MAX_GIVEN_INTERNAL`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum InternalId {
    /// `tracingtitles`: show titles in the log.
    TracingTitles = 1,
    /// `tracingequations`: show each equation as solved.
    TracingEquations = 2,
    /// `tracingcapsules`: show capsule values.
    TracingCapsules = 3,
    /// `tracingchoices`: show Hobby's algorithm decisions.
    TracingChoices = 4,
    /// `tracingspecs`: show path specifications.
    TracingSpecs = 5,
    /// `tracingcommands`: show each command before execution.
    TracingCommands = 6,
    /// `tracingrestores`: show variable restores at `endgroup`.
    TracingRestores = 7,
    /// `tracingmacros`: show macro expansions.
    TracingMacros = 8,
    /// `tracingoutput`: show `shipout` details.
    TracingOutput = 9,
    /// `tracingstats`: show memory usage statistics.
    TracingStats = 10,
    /// `tracinglostchars`: warn about missing characters.
    TracingLostChars = 11,
    /// `tracingonline`: send tracing to terminal (vs log only).
    TracingOnline = 12,
    /// `year`: current year.
    Year = 13,
    /// `month`: current month (1–12).
    Month = 14,
    /// `day`: current day (1–31).
    Day = 15,
    /// `time`: minutes since midnight.
    Time = 16,
    /// `charcode`: character code for current figure.
    CharCode = 17,
    /// `charext`: character extension.
    CharExt = 18,
    /// `charwd`: character width (for TFM, largely unused).
    CharWd = 19,
    /// `charht`: character height.
    CharHt = 20,
    /// `chardp`: character depth.
    CharDp = 21,
    /// `charic`: character italic correction.
    CharIc = 22,
    /// `designsize`: TFM design size.
    DesignSize = 23,
    /// `pausing`: pause after each line shown.
    Pausing = 24,
    /// `showstopping`: stop after each `show`.
    ShowStopping = 25,
    /// `fontmaking`: produce TFM output.
    FontMaking = 26,
    /// `linejoin`: line join style (0=miter, 1=round, 2=bevel).
    LineJoin = 27,
    /// `linecap`: line cap style (0=butt, 1=round, 2=square).
    LineCap = 28,
    /// `miterlimit`: miter limit ratio.
    MiterLimit = 29,
    /// `warningcheck`: threshold for "value too large" warnings.
    WarningCheck = 30,
    /// `boundarychar`: boundary character for ligatures.
    BoundaryChar = 31,
    /// `prologues`: PostScript prologue mode.
    Prologues = 32,
    /// `truecorners`: use true bounding box corners.
    TrueCorners = 33,
}

/// Maximum index of built-in internals.
pub const MAX_GIVEN_INTERNAL: u16 = InternalId::TrueCorners as u16;

// ---------------------------------------------------------------------------
// Internal quantities storage
// ---------------------------------------------------------------------------

/// Storage for internal quantities.
///
/// Built-in internals occupy indices 1–`MAX_GIVEN_INTERNAL`.
/// User-defined internals (via `newinternal`) are appended after.
#[derive(Debug)]
pub struct Internals {
    /// Internal quantity values, 1-indexed (index 0 is unused).
    values: Vec<Scalar>,
    /// Internal quantity names, 1-indexed.
    names: Vec<String>,
}

impl Internals {
    /// Create a new internals storage with all built-in quantities.
    #[must_use]
    pub fn new() -> Self {
        let base_len = (MAX_GIVEN_INTERNAL as usize) + 1;
        let mut values = vec![0.0; base_len];
        let mut names = vec![String::new(); base_len];
        values.reserve(16);
        names.reserve(16);

        // Set defaults
        let defaults: &[(InternalId, Scalar, &str)] = &[
            (InternalId::TracingTitles, 0.0, "tracingtitles"),
            (InternalId::TracingEquations, 0.0, "tracingequations"),
            (InternalId::TracingCapsules, 0.0, "tracingcapsules"),
            (InternalId::TracingChoices, 0.0, "tracingchoices"),
            (InternalId::TracingSpecs, 0.0, "tracingspecs"),
            (InternalId::TracingCommands, 0.0, "tracingcommands"),
            (InternalId::TracingRestores, 0.0, "tracingrestores"),
            (InternalId::TracingMacros, 0.0, "tracingmacros"),
            (InternalId::TracingOutput, 0.0, "tracingoutput"),
            (InternalId::TracingStats, 0.0, "tracingstats"),
            (InternalId::TracingLostChars, 0.0, "tracinglostchars"),
            (InternalId::TracingOnline, 0.0, "tracingonline"),
            (InternalId::Year, 0.0, "year"),
            (InternalId::Month, 0.0, "month"),
            (InternalId::Day, 0.0, "day"),
            (InternalId::Time, 0.0, "time"),
            (InternalId::CharCode, 0.0, "charcode"),
            (InternalId::CharExt, 0.0, "charext"),
            (InternalId::CharWd, 0.0, "charwd"),
            (InternalId::CharHt, 0.0, "charht"),
            (InternalId::CharDp, 0.0, "chardp"),
            (InternalId::CharIc, 0.0, "charic"),
            (InternalId::DesignSize, 0.0, "designsize"),
            (InternalId::Pausing, 0.0, "pausing"),
            (InternalId::ShowStopping, 0.0, "showstopping"),
            (InternalId::FontMaking, 0.0, "fontmaking"),
            (InternalId::LineJoin, 1.0, "linejoin"), // round
            (InternalId::LineCap, 1.0, "linecap"),   // round
            (InternalId::MiterLimit, 10.0, "miterlimit"),
            (InternalId::WarningCheck, 3604.0, "warningcheck"),
            (InternalId::BoundaryChar, -1.0, "boundarychar"),
            (InternalId::Prologues, 0.0, "prologues"),
            (InternalId::TrueCorners, 0.0, "truecorners"),
        ];

        for &(id, val, name) in defaults {
            let idx = id as usize;
            if idx < values.len() {
                values[idx] = val;
                name.clone_into(&mut names[idx]);
            }
        }

        Self { values, names }
    }

    /// Get the value of an internal quantity by index.
    #[must_use]
    pub fn get(&self, index: u16) -> Scalar {
        let idx = index as usize;
        if idx < self.values.len() {
            self.values[idx]
        } else {
            0.0
        }
    }

    /// Get the value of a built-in internal quantity by enum id.
    #[must_use]
    pub fn get_id(&self, id: InternalId) -> Scalar {
        self.get(id as u16)
    }

    /// Set the value of an internal quantity by index.
    pub fn set(&mut self, index: u16, value: Scalar) {
        let idx = index as usize;
        if idx < self.values.len() {
            self.values[idx] = value;
        }
    }

    /// Set the value of a built-in internal quantity by enum id.
    pub fn set_id(&mut self, id: InternalId, value: Scalar) {
        self.set(id as u16, value);
    }

    /// Get the name of an internal quantity.
    #[must_use]
    pub fn name(&self, index: u16) -> &str {
        let idx = index as usize;
        if idx < self.names.len() {
            &self.names[idx]
        } else {
            ""
        }
    }

    /// Register a new user-defined internal quantity.
    /// Returns the index of the new quantity.
    #[must_use]
    pub fn new_internal(&mut self, name: &str) -> Option<u16> {
        let idx = self.values.len();
        let Ok(result) = u16::try_from(idx) else {
            return None;
        };
        self.values.push(0.0);
        self.names.push(name.to_owned());
        Some(result)
    }

    /// Total number of internal quantities (including slot 0).
    #[must_use]
    pub fn count(&self) -> usize {
        self.values.len()
    }
}

impl Default for Internals {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_values() {
        let int = Internals::new();
        // linecap and linejoin default to 1 (round)
        assert!((int.get(InternalId::LineCap as u16) - 1.0).abs() < f64::EPSILON);
        assert!((int.get(InternalId::LineJoin as u16) - 1.0).abs() < f64::EPSILON);
        // miterlimit defaults to 10
        assert!((int.get(InternalId::MiterLimit as u16) - 10.0).abs() < f64::EPSILON);
        // tracing defaults to 0
        assert!((int.get(InternalId::TracingChoices as u16)).abs() < f64::EPSILON);
    }

    #[test]
    fn set_and_get() {
        let mut int = Internals::new();
        int.set(InternalId::LineCap as u16, 2.0);
        assert!((int.get(InternalId::LineCap as u16) - 2.0).abs() < f64::EPSILON);
    }

    #[test]
    fn names() {
        let int = Internals::new();
        assert_eq!(int.name(InternalId::LineCap as u16), "linecap");
        assert_eq!(int.name(InternalId::TracingMacros as u16), "tracingmacros");
    }

    #[test]
    fn new_internal() {
        let mut int = Internals::new();
        let idx = int
            .new_internal("myquantity")
            .expect("first user internal should fit in u16");
        assert_eq!(idx, MAX_GIVEN_INTERNAL + 1);
        assert!((int.get(idx)).abs() < f64::EPSILON); // default 0
        assert_eq!(int.name(idx), "myquantity");
    }

    #[test]
    fn first_user_internal_index_is_contiguous() {
        let mut int = Internals::new();
        let first = int
            .new_internal("first")
            .expect("first user internal should fit in u16");
        let second = int
            .new_internal("second")
            .expect("second user internal should fit in u16");
        assert_eq!(first, MAX_GIVEN_INTERNAL + 1);
        assert_eq!(second, MAX_GIVEN_INTERNAL + 2);
    }

    #[test]
    fn out_of_bounds_returns_zero() {
        let int = Internals::new();
        assert!((int.get(9999)).abs() < f64::EPSILON);
    }
}
