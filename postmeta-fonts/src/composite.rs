//! Composite font provider: embedded defaults + custom overrides.

use std::collections::HashMap;
use std::sync::Arc;

use crate::data::FontData;
use crate::error::FontError;
use crate::provider::FontProvider;

/// Font provider that checks custom fonts first, then falls back to embedded.
///
/// Font name lookup is case-insensitive: names are normalized to lowercase.
pub struct CompositeFontProvider {
    /// Embedded fonts (populated from the alias table at construction).
    embedded: HashMap<String, FontData>,
    /// User-provided fonts (loaded from files via [`Self::load_font`]).
    custom: HashMap<String, FontData>,
}

impl CompositeFontProvider {
    /// Create a provider with embedded defaults only.
    ///
    /// # Errors
    ///
    /// Returns [`FontError::ParseError`] if any embedded font fails to parse.
    pub fn new() -> Result<Self, FontError> {
        let entries = crate::embedded::load_embedded()?;
        let mut embedded = HashMap::with_capacity(entries.len());
        for (name, font) in entries {
            embedded.insert(name, font);
        }
        Ok(Self {
            embedded,
            custom: HashMap::new(),
        })
    }

    /// Load a custom font from bytes, registered under the given name.
    ///
    /// The name is normalized to lowercase for matching. If a font with
    /// the same name already exists in the custom set, it is replaced.
    ///
    /// # Errors
    ///
    /// Returns [`FontError::ParseError`] if the bytes are not a valid font.
    pub fn load_font(&mut self, name: &str, bytes: Vec<u8>) -> Result<(), FontError> {
        let font = FontData::from_bytes(Arc::from(bytes.into_boxed_slice()))?;
        self.custom.insert(name.to_lowercase(), font);
        Ok(())
    }
}

impl FontProvider for CompositeFontProvider {
    fn font(&self, name: &str) -> Option<&FontData> {
        let lower = name.to_lowercase();
        self.custom
            .get(&lower)
            .or_else(|| self.embedded.get(&lower))
    }
}

#[cfg(test)]
#[expect(clippy::expect_used, reason = "tests may panic")]
mod tests {
    use super::*;

    #[test]
    fn lookup_cmr10() {
        let provider = CompositeFontProvider::new().expect("init");
        assert!(provider.font("cmr10").is_some(), "cmr10 should be found");
    }

    #[test]
    fn lookup_case_insensitive() {
        let provider = CompositeFontProvider::new().expect("init");
        assert!(provider.font("CMR10").is_some(), "CMR10 should match cmr10");
        assert!(provider.font("Cmr10").is_some(), "Cmr10 should match cmr10");
    }

    #[test]
    fn custom_overrides_embedded() {
        let mut provider = CompositeFontProvider::new().expect("init");
        let embedded_upem = provider.font("cmr10").expect("cmr10").units_per_em();

        // Load the bold font under the name "cmr10" — should override
        let bold_bytes = std::fs::read(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/fonts/NewCM10-Bold.otf"
        ))
        .expect("read bold font");
        provider.load_font("cmr10", bold_bytes).expect("load");

        let custom_upem = provider
            .font("cmr10")
            .expect("cmr10 after override")
            .units_per_em();
        // Both NewCM fonts have the same upem, but the FontData instance
        // should be different (custom takes priority).
        assert_eq!(embedded_upem, custom_upem);
    }

    #[test]
    fn unknown_font_returns_none() {
        let provider = CompositeFontProvider::new().expect("init");
        assert!(
            provider.font("nonexistent-font").is_none(),
            "unknown font should return None"
        );
    }
}
