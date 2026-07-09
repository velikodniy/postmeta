//! Application orchestration: run the interpreter and write SVG output

use std::env;
use std::fs;
use std::path::Path;
use std::sync::Arc;

use postmeta_core::interpreter::Interpreter;
use postmeta_fonts::FontProvider;
use postmeta_svg::{RenderOptions, render_with_fonts};

use crate::args::Cli;
use crate::fonts::build_font_provider;
use crate::fs::{OsFileSystem, read_source};

/// Run the CLI: interpret the program and write SVG output
///
/// Returns the process exit code: 0 on success, 1 on error.
pub fn run(cli: &Cli) -> u8 {
    let mut interp = Interpreter::new();

    let mut search_dirs = Vec::new();

    if let Some(ref file) = cli.file {
        let stem = Path::new(file)
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("output");
        interp.set_job_name(stem);

        if let Some(parent) = Path::new(file).parent() {
            search_dirs.push(parent.to_path_buf());
        }
    }

    if let Ok(cwd) = env::current_dir() {
        search_dirs.push(cwd);
    }

    // lib/ relative to the executable, tried at several common install layouts
    if let Ok(exe) = env::current_exe() {
        if let Some(exe_dir) = exe.parent() {
            for relative in &["../lib", "../../lib", "lib"] {
                let lib_dir = exe_dir.join(relative);
                if lib_dir.is_dir() {
                    search_dirs.push(lib_dir);
                }
            }
        }
    }

    interp.set_filesystem(Box::new(OsFileSystem::new(search_dirs)));

    let fonts: Arc<dyn FontProvider> = match build_font_provider(&cli.font_dirs) {
        Ok(provider) => Arc::new(provider),
        Err(e) => {
            eprintln!("Warning: font initialization failed: {e}");
            eprintln!("Text will be rendered as raw <text> elements.");
            let Some(source) = read_source(cli) else {
                return 1;
            };
            return run_and_output(&mut interp, &source, &cli.output, cli, None);
        }
    };

    interp.set_font_provider(Arc::clone(&fonts));

    let Some(source) = read_source(cli) else {
        return 1;
    };
    run_and_output(&mut interp, &source, &cli.output, cli, Some(&*fonts))
}

fn run_and_output(
    interp: &mut Interpreter,
    source: &str,
    output_dir: &str,
    cli: &Cli,
    fonts: Option<&dyn FontProvider>,
) -> u8 {
    let run_err = interp.run(source).err();

    // Print program diagnostics even when run() itself returned an error
    print_diagnostics(interp);

    if let Some(e) = run_err {
        eprintln!("Error: {e}");
        return 1;
    }

    write_output(interp, output_dir, cli, fonts);
    0
}

fn print_diagnostics(interp: &Interpreter) {
    for err in interp.diagnostics() {
        match err.severity {
            postmeta_core::error::Severity::Info => {
                println!("{}", err.message);
            }
            postmeta_core::error::Severity::Warning => {
                eprintln!("Warning: {}", err.message);
            }
            _ => {
                eprintln!("Error: {}", err.message);
            }
        }
    }
}

fn write_output(
    interp: &Interpreter,
    output_dir: &str,
    cli: &Cli,
    fonts: Option<&dyn FontProvider>,
) {
    let opts = RenderOptions {
        margin: 1.0,
        precision: 4,
        true_corners: interp
            .internals()
            .get(postmeta_core::internals::InternalId::TrueCorners as u16)
            > 0.0,
        text_mode: cli.text_mode,
    };

    for (i, pic) in interp.output().iter().enumerate() {
        let svg_str = render_with_fonts(pic, &opts, fonts).to_string();
        let filename = if interp.output().len() == 1 {
            format!("{}.svg", interp.job_name())
        } else {
            format!("{}.{}.svg", interp.job_name(), i + 1)
        };
        write_svg(output_dir, &filename, &svg_str);
    }

    if interp.output().is_empty() && !interp.current_picture().is_empty() {
        let svg_str = render_with_fonts(interp.current_picture(), &opts, fonts).to_string();
        let filename = format!("{}.svg", interp.job_name());
        write_svg(output_dir, &filename, &svg_str);
    }
}

fn write_svg(output_dir: &str, filename: &str, content: &str) {
    let path = Path::new(output_dir).join(filename);
    match fs::write(&path, content) {
        Ok(()) => {
            eprintln!("Wrote {}", path.display());
        }
        Err(e) => {
            eprintln!("Error writing {}: {e}", path.display());
        }
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::expect_used, clippy::unwrap_used, clippy::panic)]

    use std::fs;
    use std::time::{SystemTime, UNIX_EPOCH};

    use clap::Parser;

    use super::run;
    use crate::args::Cli;

    #[test]
    fn run_renders_trivial_source_to_svg() {
        let ts = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        let dir =
            std::env::temp_dir().join(format!("postmeta_app_run_{}_{ts}", std::process::id()));
        fs::create_dir_all(&dir).expect("create temp dir");

        let source_path = dir.join("smoke.mp");
        fs::write(
            &source_path,
            "delimiters (); addto currentpicture doublepath (0,0)..(10,10);",
        )
        .expect("write source file");

        let cli = Cli::parse_from([
            "postmeta",
            source_path.to_str().expect("utf-8 path"),
            "--output",
            dir.to_str().expect("utf-8 path"),
        ]);

        let code = run(&cli);
        assert_eq!(code, 0, "expected successful exit code");

        let svg_path = dir.join("smoke.svg");
        let svg = fs::read_to_string(&svg_path).expect("read svg output");
        assert!(svg.contains("<svg"), "expected svg root element");

        let _ = fs::remove_dir_all(&dir);
    }
}
