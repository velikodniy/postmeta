//! Shared fixtures and the [`TestInterp`] harness for interpreter tests.

use postmeta_graphics::types::Picture;

use crate::error::{InterpreterError, Severity};
use crate::filesystem::FileSystem;
use crate::interpreter::Interpreter;

/// Filesystem fixture that serves `lib/plain.mp` from the workspace root.
pub struct PlainMpFs;

pub fn read_plain_mp() -> Option<String> {
    std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("workspace root")
            .join("lib/plain.mp"),
    )
    .ok()
}

impl FileSystem for PlainMpFs {
    fn read_file(&self, name: &str) -> Option<String> {
        if name == "plain" || name == "plain.mp" {
            read_plain_mp()
        } else {
            None
        }
    }
}

/// Thin wrapper around [`Interpreter`] that removes test boilerplate.
///
/// The inner interpreter is exposed as a public field so irregular tests
/// can still reach interpreter state directly (`t.interp.state...`).
pub struct TestInterp {
    pub interp: Interpreter,
}

impl TestInterp {
    pub fn new() -> Self {
        Self {
            interp: Interpreter::new(),
        }
    }

    /// Create an interpreter with the [`PlainMpFs`] fixture installed,
    /// so `input plain;` works.
    pub fn with_plain_mp() -> Self {
        let mut t = Self::new();
        t.interp.set_filesystem(Box::new(PlainMpFs));
        t
    }

    /// Run source through the interpreter, panicking on a hard failure.
    pub fn run(&mut self, src: &str) {
        self.interp.run(src).unwrap();
    }

    /// All `show`/`message` output (diagnostics with `Severity::Info`),
    /// in order of emission.
    pub fn shows(&self) -> Vec<&str> {
        self.interp
            .state
            .errors
            .iter()
            .filter(|e| e.severity == Severity::Info)
            .map(|e| e.message.as_str())
            .collect()
    }

    /// The first `show`/`message` output; panics if there is none.
    pub fn first_show(&self) -> &str {
        self.interp
            .state
            .errors
            .iter()
            .find(|e| e.severity == Severity::Info)
            .map_or_else(
                || {
                    panic!(
                        "expected at least one show message, got: {:?}",
                        self.interp.state.errors
                    )
                },
                |e| e.message.as_str(),
            )
    }

    /// All diagnostics with `Severity::Error`.
    pub fn errors(&self) -> Vec<&InterpreterError> {
        self.interp
            .state
            .errors
            .iter()
            .filter(|e| e.severity == Severity::Error)
            .collect()
    }

    /// Assert that no `Severity::Error` diagnostics were produced.
    pub fn assert_no_errors(&self) {
        let errors = self.errors();
        assert!(errors.is_empty(), "unexpected errors: {errors:?}");
    }

    /// Pictures shipped out via `shipout`/`endfig`.
    pub fn output(&self) -> &[Picture] {
        self.interp.output()
    }

    /// The picture currently being drawn (`currentpicture`).
    pub fn current_picture(&self) -> &Picture {
        self.interp.current_picture()
    }
}

impl Default for TestInterp {
    fn default() -> Self {
        Self::new()
    }
}
