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

```bash
deno task dev
```

- Builds the WASM module and starts a local dev server at port 5173.

```bash
deno task build
```

- Builds WASM, bundles the app, and writes static output to `web/dist/`.

```bash
deno task preview
```

- Serves `web/dist/` for a final static preview.

## Notes

- The WASM adapter crate lives at `postmeta-wasm/` in the repository root.
- `plain.mp` is embedded into the WASM module via `include_str!`, so the browser build has no runtime file-system dependency.
- No WASM binaries are stored in source; they are generated during `deno task wasm` / `deno task build`.
- The release build uses size-focused Rust flags (`opt-level=z`, `codegen-units=1`, `strip`, `panic=abort`).
