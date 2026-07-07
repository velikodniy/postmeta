//! `PostMeta` CLI — run `MetaPost` programs and output SVG.

mod app;
mod args;
mod fonts;
mod fs;

use std::process::ExitCode;

use clap::Parser;

use crate::args::Cli;

fn main() -> ExitCode {
    let cli = Cli::parse();
    ExitCode::from(app::run(&cli))
}
