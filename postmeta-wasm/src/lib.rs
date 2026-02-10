use postmeta_core::error::{InterpreterError, Severity};
use postmeta_core::filesystem::FileSystem;
use postmeta_core::internals::InternalId;
use postmeta_core::interpreter::Interpreter;
use postmeta_svg::{render_with_options, RenderOptions};
use wasm_bindgen::prelude::*;

const PLAIN_MP: &str = include_str!("../../lib/plain.mp");

struct EmbeddedFileSystem;

impl FileSystem for EmbeddedFileSystem {
    fn read_file(&self, name: &str) -> Option<String> {
        if name == "plain" || name == "plain.mp" {
            Some(PLAIN_MP.to_owned())
        } else {
            None
        }
    }
}

#[wasm_bindgen]
pub struct CompileOutput {
    svg: String,
    diagnostics: String,
    has_error: bool,
}

#[wasm_bindgen]
impl CompileOutput {
    #[wasm_bindgen(getter)]
    pub fn svg(&self) -> String {
        self.svg.clone()
    }

    #[wasm_bindgen(getter)]
    pub fn diagnostics(&self) -> String {
        self.diagnostics.clone()
    }

    #[wasm_bindgen(getter, js_name = hasError)]
    pub fn has_error(&self) -> bool {
        self.has_error
    }
}

#[wasm_bindgen]
pub fn render_metapost(source: &str) -> CompileOutput {
    compile_program(source)
}

fn compile_program(source: &str) -> CompileOutput {
    let mut interpreter = Interpreter::new();
    interpreter.set_filesystem(Box::new(EmbeddedFileSystem));

    let run_failure = interpreter.run(source).err();
    let diagnostics = collect_diagnostics(&interpreter.errors, run_failure.as_ref());
    let has_error = has_errors(&interpreter.errors) || run_failure.is_some();
    let svg = render_svg_preview(&interpreter);

    CompileOutput {
        svg,
        diagnostics,
        has_error,
    }
}

fn collect_diagnostics(
    errors: &[InterpreterError],
    run_failure: Option<&InterpreterError>,
) -> String {
    let mut lines = Vec::new();

    for err in errors {
        lines.push(format_diagnostic(err));
    }

    if let Some(err) = run_failure {
        lines.push(format!("fatal {err}"));
    }

    lines.join("\n")
}

fn has_errors(errors: &[InterpreterError]) -> bool {
    errors
        .iter()
        .any(|err| matches!(err.severity, Severity::Error | Severity::Fatal))
}

fn format_diagnostic(err: &InterpreterError) -> String {
    let label = match err.severity {
        Severity::Info => "info",
        Severity::Warning => "warning",
        Severity::Error => "error",
        Severity::Fatal => "fatal",
    };

    if let Some(span) = err.span {
        format!("{label} [{}..{}] {}", span.start, span.end, err.message)
    } else {
        format!("{label} {}", err.message)
    }
}

fn render_svg_preview(interpreter: &Interpreter) -> String {
    let picture = interpreter.pictures.last().or({
        if interpreter.current_picture.objects.is_empty() {
            None
        } else {
            Some(&interpreter.current_picture)
        }
    });

    if let Some(picture) = picture {
        let opts = RenderOptions {
            margin: 1.0,
            precision: 4,
            true_corners: interpreter.internals.get(InternalId::TrueCorners as u16) > 0.0,
        };
        render_with_options(picture, &opts).to_string()
    } else {
        String::new()
    }
}

#[cfg(test)]
mod tests {
    use super::compile_program;

    #[test]
    fn compiles_plain_macros_and_returns_svg() {
        let output = compile_program(
            "input plain; beginfig(1); draw fullcircle scaled 36; fill fullcircle scaled 8 shifted (18,0); endfig; end;",
        );

        assert!(
            !output.has_error,
            "unexpected diagnostics: {}",
            output.diagnostics
        );
        assert!(output.svg.contains("<svg"), "missing SVG root");
        assert!(output.svg.contains("path"), "missing rendered path");
    }

    #[test]
    fn reports_errors_for_invalid_source() {
        let output = compile_program("input plain; beginfig(1); draw (0,0)..; endfig; end;");

        assert!(output.has_error, "expected compile error");
        assert!(!output.diagnostics.is_empty(), "expected diagnostics");
    }
}
