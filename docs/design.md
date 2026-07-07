# PostMeta Design

PostMeta is a reimplementation of MetaPost in Rust, designed for use as a
library, WASM module (e.g. Typst plugin), or CLI tool.

## Architecture

```
postmeta-graphics   Core graphics primitives (zero dependencies)
       ^
postmeta-fonts      Font metrics/outlines (ttf-parser wrapper)
       ^
postmeta-svg        SVG renderer (depends on `svg` crate)
       ^
postmeta-core       MetaPost language parser and interpreter
       ^
postmeta-cli        Command-line interface (args/fs/fonts/app modules)
postmeta-wasm       WASM bindings (browser editor)
```

CI (`.github/workflows/ci.yml`) runs fmt, clippy (`-D warnings`), the
workspace test suite, and a wasm32 check. `visual-tests/` holds a 304-case
visual regression harness (`python3 visual-tests/run.py`).

## postmeta-graphics

Pure computational library. All of MetaPost's core algorithms, usable as a
standalone Rust API without any parsing. **Zero external dependencies** — owns
its `Point`, `Vec2`, and `Transform` types.

### Types

Fundamental data structures shared across the workspace.

- **`Point`**, **`Vec2`** — 2D point and displacement vector (`f64` components).
  Standard arithmetic ops (`Sub`, `Add`, `Mul`). `Point::lerp()` for
  interpolation.
- **`Scalar`** — alias for `f64`. `EPSILON = 1/65536` for comparisons.
  `INFINITY_VAL = 4095.99998` matching MetaPost's maximum.
- **`Color`** — RGB with components in [0, 1].
- **`LineCap`**, **`LineJoin`** — stroke styles (map 1:1 to SVG/PostScript).
- **`DashPattern`** — alternating on/off lengths with offset.
- **`KnotDirection`** — direction constraint at a path knot:
  `Explicit(Point)` | `Given(radians)` | `Curl(γ)` | `Open`.
- **`Knot`** — on-curve point + left/right direction + left/right tension.
  Methods: `left_cp()`, `right_cp()` for resolved control points.
- **`Path`** — sequence of knots, optionally cyclic.
  `num_segments()`, `length()` (MetaPost alias).
- **`Pen`** — `Elliptical(Transform)` | `Polygonal(Vec<Point>)`.
  `Pen::circle(diameter)`, `Pen::DEFAULT` (0.5bp).
- **`Transform`** — 6-component affine: (tx + txx·x + txy·y, ty + tyx·x + tyy·y).
  Supports `Mul` for composition, `inverse()`.
- **`GraphicsObject`** — Fill | Stroke | Text | Picture (nested).
- **`Picture`** — ordered collection of `GraphicsObject` plus optional
  `clip_path`/`bounds_path`, forming a tree: `clip`/`setbounds` wrap the
  existing objects in a nested picture. Fields are crate-private; consumers
  use `objects()`, `iter()`, `first()`, `clip_path()`, `bounds_path()`,
  `push()`, `add_fill()`, `add_stroke()`, `merge()`.
- **`SharedPath`** — `Arc<BezierPath>` alias; `clip`/`set_bounds` accept
  `impl Into<SharedPath>` so callers never juggle `Arc` themselves.

### Transformable Trait

```rust
pub trait Transformable {
    fn transformed(&self, t: &Transform) -> Self;
}
```

Implemented for `Point`, `Vec2`, `Knot`, `Path`, `Pen`, `GraphicsObject`,
`Picture`. Transform constructors: `shifted`, `rotated` (degrees), `scaled`,
`xscaled`, `yscaled`, `slanted`, `zscaled` (complex multiplication).

### Path Module

Path query and conversion operations.

- **`point_of(path, t)`** — evaluate point at time t (de Casteljau).
- **`direction_of(path, t)`** — tangent vector at time t.
- **`precontrol_of`**, **`postcontrol_of`** — control points at time t.
- **`subpath(path, t1, t2)`** — extract sub-path (de Casteljau splitting).
- **`reverse(path)`** — reverse knot order, swap left/right.

**`CubicSeg`** — shared 4-point cubic Bezier representation with `eval()`,
`deriv()`, `split()`, `subdivide()`, `bbox()` methods. Used by both path
operations and intersection.

#### Hobby's Spline Algorithm (`path::hobby`)

**`make_choices(path)`** — resolves all `KnotDirection` values to `Explicit`
control points. Implements John D. Hobby's algorithm from "Smooth, Easy to
Compute Interpolating Splines" (1986), following the mp.web reference:

1. Decompose path at breakpoints (knots with Given or Curl constraints).
2. Compute turning angles between consecutive chord vectors.
3. Set up tridiagonal linear system for unknown angles θ_k.
4. Boundary conditions: curl ratio for endpoints, given direction for
   constrained knots.
5. Solve via forward sweep + back-substitution (open paths) or cyclic
   tridiagonal solver with w-coefficient tracking (cyclic paths).
6. Compute control points via the Hobby velocity function.
7. "At least" tensions: clamp velocities to stay inside the bounding triangle
   formed by adjacent chords.

### Math Module

MetaPost mathematical primitives: `sind`, `cosd` (degree-based), `angle`
(returns degrees), `mexp`/`mlog` (base 2^(1/256)), `pyth_add` (++),
`pyth_sub` (+-+), `floor`, `uniform_deviate`, `normal_deviate`.

### Pen Module

- **`makepen(path)`** — cyclic path → polygonal pen (convex hull via
  Andrew's monotone chain algorithm).
- **`makepath(pen)`** — pen → cyclic path (8-knot circle approximation
  for elliptical; straight-line segments for polygonal).
- **`penoffset(pen, dir)`** — support point in given direction (inverse
  transpose method for elliptical; max dot product for polygonal).

### Intersection Module

**`intersection_times(path1, path2)`** — first intersection via recursive
bisection of cubic Bezier segments. Checks bounding-box overlap at each
level, splits both curves at midpoint (de Casteljau), recurses on the 4
sub-pairs. Converges when segment extent < 10^-6 or depth > 40.

**`all_intersection_times`** — finds all intersections with deduplication.

### Picture Module

Picture assembly matching MetaPost primitives:
- **`addto_contour`**, **`addto_doublepath`**, **`addto_also`** — add fills,
  strokes, merge pictures.
- **`clip`**, **`setbounds`** — wrap the current objects in a nested
  picture carrying `clip_path`/`bounds_path`.
- **`BoundingBox`** — axis-aligned bbox with empty sentinel (∞/−∞) and a
  full set-algebra API: `union`, `intersect`, `overlaps` (single source of
  truth for AABB semantics, also used by intersection pruning).
  Control-point hull for paths (conservative, matching MetaPost).
  Corner methods: `llcorner`, `lrcorner`, `ulcorner`, `urcorner`.
  `of_picture(pic, Corners::HonorSetBounds | Corners::True)` maps to the
  `truecorners` internal.

## postmeta-svg

Converts `Picture` to SVG using the `svg` crate.

- Y-axis flip by per-coordinate negation (`util::flip_y`) in path data and
  the viewBox — no global `scale(1,-1)`. Text transforms are conjugated
  with `S = diag(1,-1)` via `util::svg_text_matrix`.
- Fill → `<path>` with fill color.
- Stroke → `<path>` with stroke-width, cap, join, dash attributes.
  Stroke width extracted from pen transform (geometric mean of basis vectors).
- Text → `<text>` with counter-flip matrix.
- Clip → `<defs><clipPath>` + `<g clip-path="url(#...)">`.
- SetBounds → transparent (only affects bbox computation).
- Path data built as raw `d` strings (not via intermediate `BezPath`).

## postmeta-core

Hand-written recursive-descent parser and tree-walking interpreter.
Implements only the ~210 engine primitives; macros like `draw`, `fill`,
`--`, `---`, `fullcircle`, etc. are defined in `plain.mp`.

- **Scanner**: mp.web §64 character classes (21 classes). Same-class
  characters merge into tokens.
- **Parser**: 4-level expression hierarchy
  (primary → secondary → tertiary → expression), Pratt-style infix loop.
  Statement contexts pass `EqualsMode::Equation` so a top-level `=` is an
  equation delimiter; everywhere else it is the comparison operator.
- **Macro expansion**: at the token level, between scanner and parser.
  The input stack (`InputSystem`) layers sources, token lists, and
  backed-up tokens as explicit levels; `input`/`scantokens` nesting is
  bounded (64 levels) so recursive inclusion terminates with an error.
- **Command table**: `command/mod.rs` holds the `Command` enum and the op
  enums; `command/primitives.rs` holds the `PRIMITIVES` registration table.
  See [adding-primitives.md](adding-primitives.md) for the checklist.
- **Operators**: dispatchers in `interpreter/operators/mod.rs` stay
  exhaustive matches; evaluation lives in domain submodules (arithmetic,
  transforms, strings, paths, pictures, text).
- **Equation solver**: pure dependency-list algebra in `equation.rs`;
  stateful solving/assignment in `interpreter/equation.rs`. Compound types
  (pair, color, transform) solve component-wise, driven by
  `Type::components()`/`component_suffixes()` — adding a compound type
  (e.g. `cmykcolor`) starts there. Expression-level dependency tracking in
  `interpreter/dep_arith.rs` (pairs only, currently).
- **Diagnostics**: errors carry source spans (current token, falling back
  to statement start).
- **File system**: `trait FileSystem` for WASM compatibility.
- **Tests**: themed unit-test modules under `interpreter/tests/` with the
  `TestInterp` harness.

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
Everything defined in `plain.mp` (draw, fill, --, fullcircle, etc.)
runs as MetaPost macros through the interpreter. This keeps the engine
minimal and faithful to the original design.

## Reference

- `docs/mp.web` — original MetaPost WEB source (23K lines)
- `lib/plain.mp` — standard library
- [ref-language.md](ref-language.md) — Data types, paths, equations, variables
- [ref-operators.md](ref-operators.md) — All operators by category
- [ref-internals.md](ref-internals.md) — Internal variables, constants, commands
- [ref-syntax.md](ref-syntax.md) — Complete BNF grammar, tokenization rules
