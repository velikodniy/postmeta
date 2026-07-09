# PostMeta Design

PostMeta reimplements MetaPost in Rust, usable as a library, a WASM module (e.g. a Typst plugin), or a CLI tool.

## Workspace

Crates, bottom of the dependency chain first:

- `postmeta-graphics` — geometry types and MetaPost's core algorithms, zero external dependencies
- `postmeta-fonts` — font metrics and outlines (wraps `ttf-parser`)
- `postmeta-svg` — renders pictures to SVG via the `svg` crate
- `postmeta-core` — MetaPost language scanner, parser, and interpreter
- `postmeta-cli` — command-line tool
- `postmeta-wasm` — WASM bindings for the browser playground in `web/`

CI runs fmt, clippy (`-D warnings`), the workspace tests, and a wasm32 check.
Visual regression tests: `python3 visual-tests/run.py` (304 cases).

## postmeta-graphics

Pure computational core: points, vectors, affine transforms, knots, paths, pens, colors, pictures.
All of MetaPost's geometry is usable as a plain Rust API without any parsing.
The non-obvious parts:

- All arithmetic is `f64`; `EPSILON = 1/65536` mirrors MetaPost's fixed-point granularity, and infinity is capped at MetaPost's maximum value.
- Hobby's spline algorithm (from "Smooth, Easy to Compute Interpolating Splines", 1986, and `mp.web`) resolves direction, curl, and tension constraints to explicit Bezier control points by solving tridiagonal systems per segment.
- Bezier evaluation, splitting, and subpaths are hand-written de Casteljau.
- Path intersection is recursive bisection with bounding-box pruning, matching MetaPost's approach.
- A `Picture` is a tree: `clip` and `setbounds` wrap the current objects in a nested picture carrying the clip or bounds path.
- Bounding boxes use the control-point hull (conservative, like MetaPost) and provide the single source of AABB set algebra.
- Pens are elliptical (a transform of the unit circle) or polygonal (`makepen` takes the convex hull).
- Angles are degrees at the API boundary, radians internally.
- `Transformable` applies transforms uniformly; `Transform * Transform` composes.

## postmeta-svg

Converts a `Picture` to SVG.

- The Y axis is flipped by per-coordinate negation, not a global `scale(1,-1)`; text transforms are conjugated with `diag(1,-1)` so glyphs stay upright.
- Stroke width is extracted from the pen transform as the geometric mean of its basis vectors.
- `clip` becomes `<clipPath>`; `setbounds` renders nothing (it only affects the bounding box).

## postmeta-core

Hand-written recursive-descent parser and tree-walking interpreter.

- The scanner uses `mp.web`'s character classes; adjacent same-class characters merge into one token.
- The parser has four expression levels (primary, secondary, tertiary, expression); a top-level `=` is an equation delimiter only in statement context, a comparison everywhere else.
- Macro expansion happens at the token level, between scanner and parser; the input stack layers sources, token lists, and backed-up tokens, with bounded nesting so recursive `input` fails cleanly.
- Equations use dependency-list algebra as in `mp.web`; compound types (pair, color, transform) solve component-wise.
- Errors carry source spans.
- File access goes through the `FileSystem` trait so the core stays WASM-compatible.
- Interpreter tests are themed modules driven by the `TestInterp` helper.

## Key Decisions

| Decision        | Choice                        | Rationale                              |
|-----------------|-------------------------------|----------------------------------------|
| Arithmetic      | `f64`                         | Modern, WASM-native                    |
| Graphics deps   | Zero (own Point/Vec2)         | Full control, minimal binary size      |
| Bezier math     | Hand-written de Casteljau     | Faithful to mp.web, zero deps          |
| Spline curves   | Hobby's algorithm from mp.web | Exact MetaPost fidelity                |
| SVG output      | `svg` crate                   | Structured SVG, WASM-compatible        |
| Parser          | Recursive descent             | Context-dependent grammar, macros      |
| Filesystem      | `trait FileSystem`            | WASM compatibility                     |
| Transforms      | `Transformable` trait + `Mul` | Idiomatic Rust, clean API              |
| Units           | Degrees at API boundary       | Matching MetaPost; radians internally  |

## Primitives vs Standard Library

Only the ~210 engine primitives from `mp.web` are implemented in Rust.
Everything defined in `plain.mp` (`draw`, `fill`, `--`, `fullcircle`, ...) runs as MetaPost macros through the interpreter.
This keeps the engine minimal and faithful to the original design.

## Reference

- `docs/mp.web` — original MetaPost WEB source
- `lib/plain.mp` — standard library
- [ref-language.md](ref-language.md) — data types, paths, equations, variables
- [ref-operators.md](ref-operators.md) — all operators by category
- [ref-internals.md](ref-internals.md) — internal variables, constants, commands
- [ref-syntax.md](ref-syntax.md) — BNF grammar, tokenization rules
