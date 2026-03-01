use crate::command::Command;
use crate::error::ErrorKind;
use crate::input::{StoredToken, TokenList};
use crate::interpreter::ExprResultValue;
use crate::interpreter::operators::compute_text_metrics;
use crate::types::Value;

use postmeta_graphics::types::{Color, GraphicsObject, Picture, TextObject, Transform};

use super::Interpreter;

impl Interpreter {
    /// Handle `input <filename>`.
    ///
    /// Reads the named file via the filesystem trait and pushes it as a new
    /// source input level.
    pub(in crate::interpreter) fn expand_input(&mut self) {
        self.get_next(); // skip `input`

        // Get the filename from the next token
        let filename = match &self.cur.token.kind {
            crate::token::TokenKind::Symbolic(_) => {
                self.cur_symbolic_name().unwrap_or("").to_owned()
            }
            crate::token::TokenKind::StringLit(s) => s.clone(),
            _ => {
                self.report_error(ErrorKind::MissingToken, "Expected filename after `input`");
                self.get_next();
                self.expand_current();
                return;
            }
        };

        // Try to read the file
        let contents = self.state.fs.read_file(&filename);

        match contents {
            Some(source) => {
                self.state.input.push_source(&source);
            }
            None => {
                self.report_error(ErrorKind::Internal, format!("File not found: {filename}"));
            }
        }

        self.get_next();
        self.expand_current();
    }

    /// Handle `verbatimtex ... etex`.
    ///
    /// Skips all tokens (without expansion) until `etex` or end of input.
    /// In the original `MetaPost` this passes TeX preamble material to the
    /// typesetter; `PostMeta` discards it since we don't invoke TeX.
    pub(super) fn expand_verbatimtex(&mut self) {
        loop {
            self.get_next();
            match self.cur.command {
                Command::EtexMarker | Command::Stop => break,
                _ => {} // discard
            }
        }
        // Advance past etex so caller sees the next real token.
        self.get_next();
    }

    /// Handle `btex ... etex`.
    ///
    /// Collects the raw text between `btex` and `etex` (without macro
    /// expansion) and produces a picture capsule containing a `TextObject`.
    /// In the original `MetaPost` this would be shipped to TeX for typesetting;
    /// `PostMeta` treats it as plain text rendered with the default font
    /// (`cmr10` at 10pt). Producing a picture directly makes `btex...etex`
    /// results immediately transformable (e.g. `draw btex...etex shifted z`),
    /// matching real `MetaPost` behavior. The `thelabel` macro in `plain.mp`
    /// already handles picture input via its `if picture s` branch.
    pub(super) fn expand_start_tex(&mut self) {
        let mut parts: Vec<String> = Vec::new();

        // Read raw tokens (no expansion) until EtexMarker or end of input.
        loop {
            self.get_next();
            match self.cur.command {
                Command::EtexMarker | Command::Stop => break,
                _ => {
                    // Reconstruct text from token content.
                    match &self.cur.token.kind {
                        crate::token::TokenKind::Symbolic(_) => {
                            if let Some(name) = self.cur_symbolic_name() {
                                parts.push(name.to_owned());
                            }
                        }
                        crate::token::TokenKind::Numeric(v) => parts.push(v.to_string()),
                        crate::token::TokenKind::StringLit(s) => {
                            parts.push(format!("\"{s}\""));
                        }
                        crate::token::TokenKind::Capsule | crate::token::TokenKind::Eof => break,
                    }
                }
            }
        }

        let text = parts.join(" ");

        // Build a TextObject with default font settings (cmr10 at 10pt).
        let font_name = "cmr10";
        let font_size = 10.0;
        let metrics = compute_text_metrics(
            &text,
            font_name,
            font_size,
            self.state.font_provider.as_deref(),
        );
        let text_obj = TextObject {
            text: text.into(),
            font_name: font_name.into(),
            font_size,
            metrics,
            color: Color::BLACK,
            transform: Transform::IDENTITY,
        };
        let mut pic = Picture::new();
        pic.objects.push(GraphicsObject::Text(text_obj));

        // Push a picture capsule — directly transformable.
        self.back_expr_value(ExprResultValue::plain(Value::Picture(pic)));

        // Advance past the capsule and continue expansion.
        self.get_next();
        self.expand_current();
    }

    /// Handle `scantokens <string_expr>`.
    ///
    /// Evaluates the string expression and scans it as if it were source input.
    ///
    /// mp.web §13039: after `scan_primary` obtains the string, the token
    /// that terminated the primary (e.g. `;`) is pushed back via
    /// `back_input`, then the source string is pushed on top.  This
    /// ensures the terminator is read after the scantokens source is
    /// exhausted.
    ///
    /// In our architecture `back_input` uses a single slot with highest
    /// priority, so we instead push the saved token as a one-token level
    /// *below* the source (push it first, then push the source on top).
    pub(super) fn expand_scantokens(&mut self) {
        self.expand_scantokens_inner();
        self.get_next();
        self.expand_current();
    }

    /// Core logic for `scantokens`: scan the string expression and push the
    /// resulting source onto the input stack.
    fn expand_scantokens_inner(&mut self) {
        self.get_x_next(); // skip `scantokens`, expand

        // Scan the string expression
        if let Ok(result) = self.scan_primary() {
            if let Value::String(ref s) = result.exp {
                let source = s.to_string();

                // Save the token that terminated scan_primary (mp.web's
                // back_input).  Push it as a level below the source so it
                // is read after the source is exhausted.
                let mut saved = TokenList::new();
                self.store_current_token(&mut saved);
                if !saved.is_empty() {
                    self.state
                        .input
                        .push_token_list(saved, Vec::new(), "scantokens-saved");
                }

                if !source.is_empty() {
                    self.state.input.push_source(&source);
                }
            } else {
                self.report_error(ErrorKind::TypeError, "scantokens requires a string");
            }
        }
    }

    /// Handle `expandafter`.
    ///
    /// mp.web §13032: `expandafter A B` performs ONE expansion step on B,
    /// then places A in front of B's expansion result.
    ///
    /// ```text
    /// get_t_next;  p := cur_tok;  {read A}
    /// get_t_next;                 {read B}
    /// if cur_cmd < min_command then expand else back_input;
    /// back_list(p);               {push A in front}
    /// ```
    ///
    /// In our architecture each expand handler ends with
    /// `get_next(); expand_current();`, performing full expansion.
    /// For expandafter we need exactly one step, so we call a
    /// push-only variant of the handler that sets up the input stack
    /// but does **not** read the first result token.  Then we push A
    /// on top and let `get_next(); expand_current();` do the rest.
    pub(super) fn expand_expandafter(&mut self) {
        self.expand_expandafter_push_only();

        // Read the first result token and continue expanding.
        self.get_next();
        self.expand_current();
    }

    /// Convert `self.cur` to a `StoredToken`, if possible.
    fn resolved_to_stored(&self) -> Option<StoredToken> {
        match &self.cur.token.kind {
            crate::token::TokenKind::Symbolic(_) => self.cur.sym.map(StoredToken::Symbol),
            crate::token::TokenKind::Numeric(v) => Some(StoredToken::Numeric(*v)),
            crate::token::TokenKind::StringLit(s) => Some(StoredToken::StringLit(s.clone())),
            crate::token::TokenKind::Capsule | crate::token::TokenKind::Eof => None,
        }
    }

    /// Push-only variant of `expand_scantokens` for use by `expandafter`.
    ///
    /// Same as `expand_scantokens` but does NOT call `get_next();
    /// expand_current();` — the source is left on the input stack.
    fn expand_scantokens_push_only(&mut self) {
        self.expand_scantokens_inner();
    }

    /// Push-only variant of `expand_defined_macro` for use by `expandafter`.
    ///
    /// Same as `expand_defined_macro` but does NOT call `get_next();
    /// expand_current();` — the expansion is left on the input stack.
    pub(super) fn expand_defined_macro_push_only(&mut self) {
        self.expand_defined_macro_inner();
    }

    /// Push-only variant of `expand_expandafter`.
    ///
    /// Performs the full expandafter logic (read A, read B, one-step expand B,
    /// push A in front) but does NOT call `get_next(); expand_current()` at
    /// the end.  Used by `expand_one_step` for nested expandafter chains.
    fn expand_expandafter_push_only(&mut self) {
        // Read token A without expanding.
        self.get_next();
        let saved_a: TokenList = std::iter::once_with(|| self.resolved_to_stored())
            .flatten()
            .collect();

        // Read token B without expanding.
        self.get_next();

        if self.cur.command.is_expandable() {
            // Perform ONE expansion step for B.
            self.expand_one_step();
        } else {
            // B is not expandable — push it back.
            let mut saved_b = TokenList::new();
            self.store_current_token(&mut saved_b);
            if !saved_b.is_empty() {
                self.state
                    .input
                    .push_token_list(saved_b, Vec::new(), "expandafter-b");
            }
        }

        // Push A in front of whatever B produced.
        if !saved_a.is_empty() {
            self.state
                .input
                .push_token_list(saved_a, Vec::new(), "expandafter-a");
        }

        // Do NOT call get_next/expand_current — caller handles continuation.
    }

    /// Perform exactly one expansion step for the token in `self.cur`.
    ///
    /// This dispatches to a push-only variant of the appropriate handler.
    /// After this call, the expansion result is on the input stack but
    /// `self.cur` is stale — the caller must call `get_next()` to read
    /// the first result token.
    fn expand_one_step(&mut self) {
        match self.cur.command {
            Command::DefinedMacro => self.expand_defined_macro_push_only(),
            Command::ScanTokens => self.expand_scantokens_push_only(),
            Command::ExpandAfter => self.expand_expandafter_push_only(),
            Command::IfTest => {
                // For conditionals, full expansion is the only sensible
                // one-step behaviour: evaluate the condition and enter
                // the correct branch.
                self.expand_if();
                // expand_if left self.cur at the first token of the
                // branch — push it back so the caller can re-read it.
                let mut saved = TokenList::new();
                self.store_current_token(&mut saved);
                if !saved.is_empty() {
                    self.state
                        .input
                        .push_token_list(saved, Vec::new(), "expandafter-if");
                }
            }
            Command::Input => {
                self.expand_input();
                let mut saved = TokenList::new();
                self.store_current_token(&mut saved);
                if !saved.is_empty() {
                    self.state
                        .input
                        .push_token_list(saved, Vec::new(), "expandafter-input");
                }
            }
            _ => {
                // For other expandable commands (iteration, exitif,
                // repeat_loop, etc.), fall back to full expansion and
                // push the result back.
                self.expand_current();
                let mut saved = TokenList::new();
                self.store_current_token(&mut saved);
                if !saved.is_empty() {
                    self.state
                        .input
                        .push_token_list(saved, Vec::new(), "expandafter-other");
                }
            }
        }
    }
}
