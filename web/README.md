# PostMeta Web Demo

Static web playground for PostMeta with a syntax-highlighted editor and live SVG preview.

## Requirements

- Deno 2+
- Rust toolchain with `wasm32-unknown-unknown` target
- `wasm-pack`
- Optional: `wasm-opt` (for extra size reduction)

Install the wasm target once:

```bash
rustup target add wasm32-unknown-unknown
```

## Commands

Run from `web/`:

- `deno task dev` — builds the WASM module and serves a dev server on port 5173
- `deno task build` — builds WASM, bundles the app, writes static output to `web/dist/`
- `deno task preview` — serves `web/dist/` for a final static check

## Notes

- The WASM adapter crate lives at `postmeta-wasm/` in the repository root.
- `plain.mp` is embedded into the WASM module via `include_str!`, so the browser build has no runtime file-system dependency.
- No WASM binaries are stored in source; they are generated during `deno task wasm` / `deno task build`.
- The release build uses size-focused Rust flags (`opt-level=z`, `codegen-units=1`, `strip`, `panic=abort`).
