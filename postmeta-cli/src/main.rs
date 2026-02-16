//! `PostMeta` CLI — run `MetaPost` programs and output SVG.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process;

use clap::Parser;

use postmeta_core::filesystem::FileSystem;
use postmeta_core::interpreter::Interpreter;
use postmeta_svg::{RenderOptions, render_with_options};

#[derive(Parser)]
#[command(version, about = "PostMeta \u{2014} MetaPost reimplementation in Rust")]
struct Cli {
    /// Input file to run
    file: Option<String>,

    /// Evaluate an expression instead of reading a file
    #[arg(short = 'e', long = "eval")]
    eval: Option<String>,

    /// Output directory for SVG files
    #[arg(short, long, default_value = ".")]
    output: String,
}

/// Filesystem implementation that reads from disk.
///
/// Searches in configured directories, trying the exact name first,
/// then appending `.mp` if not found.
struct OsFileSystem {
    /// Directories to search for input files.
    search_dirs: Vec<PathBuf>,
}

impl OsFileSystem {
    const fn new(search_dirs: Vec<PathBuf>) -> Self {
        Self { search_dirs }
    }
}

impl FileSystem for OsFileSystem {
    fn read_file(&self, name: &str) -> Option<String> {
        let candidates = [name.to_owned(), format!("{name}.mp")];

        for dir in &self.search_dirs {
            for candidate in &candidates {
                let path = dir.join(candidate);
                if let Ok(contents) = fs::read_to_string(&path) {
                    return Some(contents);
                }
            }
        }
        None
    }
}

fn main() {
    let cli = Cli::parse();
    let mut interp = Interpreter::new();

    // Build search directories for input files
    let mut search_dirs = Vec::new();

    // Add the directory containing the input file
    if let Some(ref file) = cli.file {
        let stem = Path::new(file)
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("output");
        stem.clone_into(&mut interp.job_name);

        if let Some(parent) = Path::new(file).parent() {
            search_dirs.push(parent.to_path_buf());
        }
    }

    // Add current directory
    if let Ok(cwd) = env::current_dir() {
        search_dirs.push(cwd);
    }

    // Add the standard library directory (lib/ relative to the executable)
    if let Ok(exe) = env::current_exe() {
        if let Some(exe_dir) = exe.parent() {
            // Try several common locations for the standard library
            for relative in &["../lib", "../../lib", "lib"] {
                let lib_dir = exe_dir.join(relative);
                if lib_dir.is_dir() {
                    search_dirs.push(lib_dir);
                }
            }
        }
    }

    interp.set_filesystem(Box::new(OsFileSystem::new(search_dirs)));

    let source = read_source(&cli);
    run_and_output(&mut interp, &source, &cli.output);
}

fn read_source(cli: &Cli) -> String {
    if let Some(ref expr) = cli.eval {
        return expr.clone();
    }
    if let Some(ref file) = cli.file {
        match fs::read_to_string(file) {
            Ok(s) => return s,
            Err(e) => {
                eprintln!("Error reading {file}: {e}");
                process::exit(1);
            }
        }
    }
    eprintln!("No input file or expression specified");
    process::exit(1);
}

fn run_and_output(interp: &mut Interpreter, source: &str, output_dir: &str) {
    let run_err = interp.run(source).err();

    // Always print diagnostics (messages, warnings, errors from the program)
    // even if run() returned an error.
    print_diagnostics(interp);

    if let Some(e) = run_err {
        eprintln!("Error: {e}");
        process::exit(1);
    }

    write_output(interp, output_dir);
}

fn print_diagnostics(interp: &Interpreter) {
    for err in &interp.errors {
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

fn write_output(interp: &Interpreter, output_dir: &str) {
    let opts = RenderOptions {
        margin: 1.0,
        precision: 4,
        true_corners: interp
            .internals
            .get(postmeta_core::internals::InternalId::TrueCorners as u16)
            > 0.0,
    };

    for (i, pic) in interp.output().iter().enumerate() {
        let svg_str = render_with_options(pic, &opts).to_string();
        let filename = if interp.output().len() == 1 {
            format!("{}.svg", interp.job_name)
        } else {
            format!("{}.{}.svg", interp.job_name, i + 1)
        };
        write_svg(output_dir, &filename, &svg_str);
    }

    // If no pictures shipped but current picture has content, output it
    if interp.output().is_empty() && !interp.current_picture().objects.is_empty() {
        let svg_str = render_with_options(interp.current_picture(), &opts).to_string();
        let filename = format!("{}.svg", interp.job_name);
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
