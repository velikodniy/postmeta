# PostMeta Design

PostMeta is a reimplementation of MetaPost in Rust, designed for use as a
library, WASM module (e.g. Typst plugin), or CLI tool.

## Architecture

```
postmeta-graphics   Core graphics primitives (Rust API, no parsing)
       ^
postmeta-svg        SVG renderer
       ^
postmeta-core       MetaPost language parser and interpreter
       ^
postmeta-cli        Command-line interface
```

### postmeta-graphics

Pure computational library. All of MetaPost's core algorithms, usable as a
standalone Rust API without any parsing.

- **types** — Shared data structures: `Path`, `Knot`, `Pen`, `Picture`,
  `Transform`, `Color`, `GraphicsObject`.
- **math** — MetaPost math primitives: `sind`, `cosd`, `mexp`, `mlog`,
  `angle`, `sqrt`, `floor`, Pythagorean addition/subtraction.
- **path** — Path operations and Hobby's spline algorithm.
- **transform** — Affine transforms on paths, pens, pictures.
- **pen** — Pen model: elliptical and polygonal pens, convex hull.
- **intersection** — Curve-curve intersection (bisection algorithm).
- **picture** — Picture assembly: fill, stroke, clip, setbounds.
- **equation** — Linear equation solver for MetaPost's `=` equations.

### postmeta-svg

Converts `Picture` to SVG using the `svg` crate.

### postmeta-core

Hand-written recursive-descent parser and tree-walking interpreter.
Implements only the ~210 engine primitives; macros like `draw`, `fill`,
`--`, `---`, etc. are defined in `plain.mp`.

The parser mirrors the original 4-level expression hierarchy:
primary → secondary → tertiary → expression.

Macro expansion happens at the token level (between scanner and parser).

A `trait FileSystem` abstracts file access for WASM compatibility.

### postmeta-cli

Reads `lib/plain.mp`, then the user file. Outputs SVG files via
`postmeta-svg`.

## Key Decisions

| Decision       | Choice                       | Rationale                          |
|----------------|------------------------------|------------------------------------|
| Arithmetic     | `f64`                        | Modern, kurbo-compatible, WASM-native |
| Curves         | `kurbo` + custom Hobby's     | Leverages proven Bezier math       |
| SVG            | `svg` crate                  | Zero-dep, WASM-compatible          |
| Parser         | Hand-written recursive descent | Context-dependent grammar, macros |
| Filesystem     | `trait FileSystem`           | WASM compatibility                 |
| TFM commands   | Skipped                      | Not relevant for graphics          |
| btex/etex      | Plain text initially         | MathML planned for later           |

## Primitives vs Standard Library

Only the ~210 engine primitives from `mp.web` are implemented in Rust.
Everything defined in `plain.mp` (draw, fill, --, fullcircle, etc.)
runs as MetaPost macros through the interpreter. This keeps the engine
minimal and faithful to the original design.
