//! Command-line argument parsing

use std::path::PathBuf;

use clap::Parser;

use postmeta_svg::TextMode;

#[derive(Parser)]
#[command(version, about = "PostMeta \u{2014} MetaPost reimplementation in Rust")]
pub struct Cli {
    /// Input file to run
    pub file: Option<String>,

    /// Evaluate an expression instead of reading a file
    #[arg(short = 'e', long = "eval")]
    pub eval: Option<String>,

    /// Output directory for SVG files
    #[arg(short, long, default_value = ".")]
    pub output: String,

    /// How text is rendered in SVG: "paths" (default) or "raw"
    #[arg(long, default_value = "paths", value_parser = parse_text_mode)]
    pub text_mode: TextMode,

    /// Additional directories to search for font files (.otf, .ttf)
    #[arg(long = "font-dir", value_name = "DIR")]
    pub font_dirs: Vec<PathBuf>,
}

fn parse_text_mode(s: &str) -> Result<TextMode, String> {
    match s.to_lowercase().as_str() {
        "paths" => Ok(TextMode::Paths),
        "raw" => Ok(TextMode::Raw),
        _ => Err(format!(
            "unknown text mode \"{s}\": expected \"paths\" or \"raw\""
        )),
    }
}
