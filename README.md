# PostMeta

PostMeta is a Rust reimplementation of [MetaPost](https://en.wikipedia.org/wiki/MetaPost).
It parses MetaPost source, interprets programs, and renders pictures to SVG.
The project ships as reusable crates, a CLI, a WASM module, and a browser playground.

## Run

```bash
cargo run -p postmeta-cli -- input.mp
```

The CLI writes SVG files for the figures in the input program.

```bash
cargo run -p postmeta-cli -- -e "input plain; beginfig(1); draw unitsquare scaled 100; endfig;"
```

The inline example loads `plain.mp` because `draw` and `unitsquare` are library macros.

Use `cargo run -p postmeta-cli -- --help` for flags such as `--output`, `--text-mode`, and `--font-dir`.

## Develop

Rust 1.85 or newer is required.

```bash
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
```

Visual regression tests live in [visual-tests/](visual-tests/README.md).
The browser playground setup lives in [web/README.md](web/README.md).

## Workspace

- `postmeta-core` scans, parses, and interprets MetaPost source.
- `postmeta-graphics`, `postmeta-fonts`, and `postmeta-svg` provide geometry, font metrics, and SVG rendering.
- `postmeta-cli`, `postmeta-wasm`, and `web/` expose the CLI and browser playground.
- `lib/` contains `plain.mp`, and `docs/` contains language references and design notes.

## Status

PostMeta is a work in progress and does not yet cover the full MetaPost language.
Engine primitives live in Rust, while familiar commands such as `draw`, `fill`, and `fullcircle` come from `plain.mp`.
