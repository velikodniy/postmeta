//! `MetaPost` language parser and interpreter.

pub mod command;
pub mod equation;
pub mod error;
pub mod filesystem;
pub mod input;
pub mod internals;
#[allow(
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss,
    clippy::unnecessary_wraps,
    clippy::missing_errors_doc,
    clippy::match_same_arms,
    clippy::needless_pass_by_value
)]
pub mod interpreter;
pub mod scanner;
pub mod symbols;
pub mod token;
pub mod types;
#[allow(
    clippy::cast_possible_truncation,
    clippy::missing_errors_doc,
    dead_code
)]
pub mod variables;
