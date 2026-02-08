//! `MetaPost` language parser and interpreter.

pub mod command;
pub mod equation;
pub mod error;
pub mod input;
pub mod internals;
#[allow(
    unused_imports,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss,
    clippy::unnecessary_wraps,
    clippy::unused_self,
    clippy::wildcard_imports,
    clippy::missing_errors_doc,
    clippy::match_same_arms,
    clippy::needless_pass_by_value,
    clippy::ptr_arg,
    clippy::option_map_unit_fn,
    clippy::single_match_else,
    clippy::fn_params_excessive_bools
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
