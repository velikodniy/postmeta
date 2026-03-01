//! Macro expansion, conditionals, and loops.
//!
//! This module handles all expandable commands: `if`/`elseif`/`else`/`fi`,
//! `for`/`forsuffixes`/`forever`/`endfor`/`exitif`, macro definitions
//! (`def`/`vardef`/`primarydef`/`secondarydef`/`tertiarydef`), macro
//! expansion, `input`, and `scantokens`.

use crate::command::Command;
use crate::input::SharedTokenList;

use super::Interpreter;

mod conditionals;
mod input_commands;
mod loops;
mod macros;

// ---------------------------------------------------------------------------
// Conditional state
// ---------------------------------------------------------------------------

/// State of one level in the `if/elseif/else/fi` nesting stack.
#[derive(Debug, Clone, Copy)]
pub(super) enum IfState {
    /// We are currently executing the active branch.
    Active,
    /// A branch was already taken; skip remaining branches.
    Done,
    /// We are skipping tokens looking for `elseif`/`else`/`fi`.
    Skipping,
}

/// Groups all conditional and loop control state.
///
/// Extracted from `Interpreter` to reduce the top-level field count.
/// Only accessed by the expansion code in this module.
#[derive(Debug, Clone)]
pub(super) struct ForeverLoopFrame {
    /// Loop body tokens replayed by `RepeatLoop`, with the `RepeatLoop`
    /// sentinel already appended.  Stored as `Arc` so re-iterations are
    /// O(1) clones.
    pub body: SharedTokenList,
    /// Whether this is a `for`/`forsuffixes` loop (vs `forever`).
    /// When true, the loop terminates after `remaining_iterations` is exhausted.
    pub is_for_loop: bool,
    /// Remaining iteration parameter lists for `for`/`forsuffixes` loops,
    /// stored in reverse order so that `Vec::pop()` yields the next iteration.
    /// `forever` loops leave this empty (they replay unconditionally).
    pub remaining_iterations: Vec<SharedTokenList>,
}

#[derive(Debug)]
pub(super) struct ControlFlow {
    /// If-stack depth tracking for nested conditionals.
    pub if_stack: Vec<IfState>,
    /// Active `forever` loop frames (outer -> inner).
    pub forever_stack: Vec<ForeverLoopFrame>,
}

impl ControlFlow {
    pub const fn new() -> Self {
        Self {
            if_stack: Vec::new(),
            forever_stack: Vec::new(),
        }
    }
}

// ---------------------------------------------------------------------------
// Macro definitions
// ---------------------------------------------------------------------------

/// The type of a macro parameter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ParamType {
    /// `expr` — a delimited expression argument (inside parentheses).
    Expr,
    /// `suffix` — a delimited suffix argument (inside parentheses).
    Suffix,
    /// `text` — a delimited text argument (inside parentheses).
    Text,
    /// `primary` — undelimited, evaluated at primary precedence.
    Primary,
    /// `secondary` — undelimited, evaluated at secondary precedence.
    Secondary,
    /// `tertiary` — undelimited, evaluated at tertiary precedence.
    Tertiary,
    /// `expr` — undelimited expression (full expression precedence).
    UndelimitedExpr,
    /// `suffix` — undelimited suffix.
    UndelimitedSuffix,
    /// `text` — undelimited text (tokens until semicolon/endgroup).
    UndelimitedText,
    /// Expression parameter preceded by `of` delimiter (from `expr t of p`
    /// pattern in macro definitions).  During expansion the `of` token is
    /// consumed, then the argument is scanned as a primary expression
    /// (matching `MetaPost`'s behavior per mp.web §710).
    OfPrimary,
}

impl ParamType {
    /// Is this an undelimited parameter type?
    pub(super) const fn is_undelimited(self) -> bool {
        matches!(
            self,
            Self::Primary
                | Self::Secondary
                | Self::Tertiary
                | Self::UndelimitedExpr
                | Self::UndelimitedSuffix
                | Self::UndelimitedText
                | Self::OfPrimary
        )
    }
}

/// A defined macro's parameter and body information.
#[derive(Debug, Clone)]
pub(super) struct MacroInfo {
    /// Parameter types in order.
    pub(super) params: Vec<ParamType>,
    /// Delimited parameter group for each parameter.
    /// `u16::MAX` means the parameter is undelimited.
    pub(super) param_groups: Vec<u16>,
    /// The macro body as a shared token list.
    ///
    /// Stored as `Arc` so that expansion clones are O(1).  For vardefs,
    /// `begingroup`/`endgroup` tokens are pre-baked at definition time.
    pub(super) body: SharedTokenList,
    /// Whether this is a `vardef` (wraps body in begingroup/endgroup).
    pub(super) is_vardef: bool,
    /// Whether this vardef has an `@#` suffix parameter.
    /// When true, the LAST entry in `params` is `UndelimitedSuffix` and
    /// corresponds to the `@#` suffix that appears between the macro name
    /// and the argument list.
    pub(super) has_at_suffix: bool,
}

impl Interpreter {
    /// Expand any expandable tokens at the current position.
    ///
    /// After this, `self.cur` holds a non-expandable token.
    pub(super) fn expand_current(&mut self) {
        while self.cur.command.is_expandable() {
            match self.cur.command {
                Command::IfTest => self.expand_if(),
                Command::FiOrElse => self.expand_fi_or_else(),
                Command::Iteration => self.expand_iteration(),
                // ExitTest and DefinedMacro handlers do NOT advance past
                // their last token. The central loop calls get_next()
                // afterwards.
                // This prevents chain expansions inside the handler from
                // crossing input-level boundaries and consuming sentinel
                // tokens that belong to enclosing scopes (e.g. the
                // look-ahead token saved by expand_binary_macro).
                Command::ExitTest => {
                    self.expand_exitif();
                    self.get_next();
                }
                Command::RepeatLoop => self.expand_repeat_loop(),
                Command::DefinedMacro => {
                    self.expand_defined_macro_push_only();
                    self.get_next();
                }
                Command::Input => self.expand_input(),
                Command::ScanTokens => self.expand_scantokens(),
                Command::StartTex => self.expand_start_tex(),
                Command::VerbatimTex => self.expand_verbatimtex(),
                Command::ExpandAfter => self.expand_expandafter(),
                Command::Relax => self.get_next(),
                _ => break, // Other expandables not yet implemented
            }
        }
    }
}
