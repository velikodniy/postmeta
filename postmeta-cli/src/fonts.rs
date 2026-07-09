//! Font provider construction for the CLI

use std::fs;
use std::path::PathBuf;

use postmeta_fonts::CompositeFontProvider;

/// Build a [`CompositeFontProvider`] with embedded defaults plus any `--font-dir` directories
pub fn build_font_provider(
    font_dirs: &[PathBuf],
) -> Result<CompositeFontProvider, postmeta_fonts::FontError> {
    let mut provider = CompositeFontProvider::new()?;

    for dir in font_dirs {
        let entries = match fs::read_dir(dir) {
            Ok(e) => e,
            Err(e) => {
                eprintln!("Warning: cannot read font directory {}: {e}", dir.display());
                continue;
            }
        };
        for entry in entries.flatten() {
            let path = entry.path();
            let ext = path
                .extension()
                .and_then(|e| e.to_str())
                .unwrap_or("")
                .to_lowercase();
            if ext != "otf" && ext != "ttf" {
                continue;
            }
            let name = path
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("")
                .to_owned();
            if name.is_empty() {
                continue;
            }
            match fs::read(&path) {
                Ok(bytes) => {
                    if let Err(e) = provider.load_font(&name, bytes) {
                        eprintln!("Warning: failed to load font {}: {e}", path.display());
                    }
                }
                Err(e) => {
                    eprintln!("Warning: cannot read font file {}: {e}", path.display());
                }
            }
        }
    }

    Ok(provider)
}
