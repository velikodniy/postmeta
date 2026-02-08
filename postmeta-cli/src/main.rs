//! `PostMeta` CLI — run `MetaPost` programs and output SVG.

use std::env;
use std::fs;
use std::path::Path;
use std::process;

use postmeta_core::interpreter::Interpreter;
use postmeta_svg::{render_with_options, RenderOptions};

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: postmeta <file.mp> [--output <dir>]");
        eprintln!("       postmeta -e <expression>");
        process::exit(1);
    }

    let config = parse_args(&args);
    let mut interp = Interpreter::new();

    if let Some(ref file) = config.input_file {
        let stem = Path::new(file)
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("output");
        stem.clone_into(&mut interp.job_name);
    }

    let source = read_source(&config);
    run_and_output(&mut interp, &source, &config.output_dir);
}

struct Config {
    output_dir: String,
    input_file: Option<String>,
    eval_expr: Option<String>,
}

fn parse_args(args: &[String]) -> Config {
    let mut output_dir = String::from(".");
    let mut input_file = None;
    let mut eval_expr = None;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--output" | "-o" => {
                i += 1;
                if i < args.len() {
                    output_dir.clone_from(&args[i]);
                }
            }
            "-e" | "--eval" => {
                i += 1;
                if i < args.len() {
                    eval_expr = Some(args[i].clone());
                }
            }
            "--help" | "-h" => {
                println!("PostMeta — MetaPost reimplementation in Rust");
                println!();
                println!("Usage:");
                println!("  postmeta <file.mp>           Run a MetaPost file, output SVG");
                println!("  postmeta -e <expression>     Evaluate an expression");
                println!("  postmeta -o <dir> <file.mp>  Set output directory");
                process::exit(0);
            }
            _ => {
                input_file = Some(args[i].clone());
            }
        }
        i += 1;
    }

    Config {
        output_dir,
        input_file,
        eval_expr,
    }
}

fn read_source(config: &Config) -> String {
    if let Some(ref expr) = config.eval_expr {
        return expr.clone();
    }
    if let Some(ref file) = config.input_file {
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
    if let Err(e) = interp.run(source) {
        eprintln!("Error: {e}");
        process::exit(1);
    }

    print_diagnostics(interp);
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

    for (i, pic) in interp.pictures.iter().enumerate() {
        let svg_str = render_with_options(pic, &opts).to_string();
        let filename = if interp.pictures.len() == 1 {
            format!("{}.svg", interp.job_name)
        } else {
            format!("{}.{}.svg", interp.job_name, i + 1)
        };
        write_svg(output_dir, &filename, &svg_str);
    }

    // If no pictures shipped but current picture has content, output it
    if interp.pictures.is_empty() && !interp.current_picture.objects.is_empty() {
        let svg_str = render_with_options(&interp.current_picture, &opts).to_string();
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
