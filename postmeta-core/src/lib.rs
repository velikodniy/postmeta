//! `MetaPost` language parser and interpreter.

#![cfg_attr(
    test,
    allow(
        clippy::expect_used,
        clippy::unwrap_used,
        clippy::panic,
        clippy::single_char_pattern,
        clippy::needless_raw_string_hashes,
        clippy::manual_let_else,
        clippy::map_unwrap_or,
        clippy::uninlined_format_args,
        clippy::needless_collect,
        clippy::match_wildcard_for_single_variants,
        clippy::doc_markdown,
        clippy::approx_constant,
        clippy::cast_lossless
    )
)]

pub mod command;
pub mod equation;
pub mod error;
pub mod expr_value;
pub mod filesystem;
pub mod input;
pub mod internals;
pub mod interpreter;
pub mod scanner;
pub mod symbols;
pub mod token;
pub mod types;
pub mod variables;
