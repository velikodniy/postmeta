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

## Crate APIs

### postmeta-graphics

Pure computational library. All of MetaPost's core algorithms, usable as a
standalone Rust API without any parsing. Depends on `kurbo` 0.13 (with
`libm` feature).

#### types

Core data structures used throughout the workspace.

```rust
// Scalar primitives
type Scalar = f64;
const EPSILON: Scalar;          // 1/65536
const INFINITY_VAL: Scalar;     // 4095.99998
fn index_to_scalar(i: usize) -> Scalar;
fn scalar_to_index(t: Scalar) -> usize;
fn deg_to_rad(deg: Scalar) -> Scalar;
fn rad_to_deg(rad: Scalar) -> Scalar;

// Color (RGB, components in [0,1])
struct Color { r, g, b: Scalar }
  Color::BLACK, Color::WHITE, Color::new(r, g, b)

// Line attributes
enum LineCap  { Butt=0, Round=1(default), Square=2 }
enum LineJoin { Miter=0, Round=1(default), Bevel=2 }
  // both have from_f64(v) -> Self
struct DashPattern { dashes: Vec<Scalar>, offset: Scalar }

// Path building blocks
enum KnotDirection { Explicit(Point), Given(Scalar), Curl(Scalar), Open }
struct Knot { point: Point, left/right: KnotDirection, left/right_tension: Scalar }
  Knot::new(point)                           // Open, tension 1.0
  Knot::with_controls(point, left_cp, right_cp) // Explicit
struct Path { knots: Vec<Knot>, is_cyclic: bool }
  Path::new(), Path::from_knots(knots, cyclic)
  path.num_segments(), path.length()

// Pen
enum Pen { Elliptical(kurbo::Affine), Polygonal(Vec<Point>) }
  Pen::circle(diameter), Pen::default_pen()  // 0.5bp circle

// Transform (tx + txx*x + txy*y, ty + tyx*x + tyy*y)
struct Transform { tx, ty, txx, txy, tyx, tyy: Scalar }
  Transform::IDENTITY, to_affine(), from_affine()

// Picture elements
enum GraphicsObject { Fill(..), Stroke(..), Text(..), ClipStart(Path),
                      ClipEnd, SetBoundsStart(Path), SetBoundsEnd }
struct FillObject   { path, color, pen: Option<Pen>, line_join, miter_limit }
struct StrokeObject  { path, pen, color, dash: Option<DashPattern>,
                       line_cap, line_join, miter_limit }
struct TextObject    { text: Arc<str>, font_name: Arc<str>, font_size,
                       color, transform: Transform }
struct Picture { objects: Vec<GraphicsObject> }
  Picture::new(), push(obj), merge(&other)

// Error
enum GraphicsError { UnresolvedPath{knot,side}, InvalidPen(&str) }
```

#### math

MetaPost mathematical primitives.

```rust
fn sind(degrees) -> Scalar;
fn cosd(degrees) -> Scalar;
fn angle(x, y) -> Scalar;               // degrees, (-180, 180]
fn mexp(x) -> Scalar;                   // 2^(x/256)
fn mlog(x) -> Scalar;                   // 256 * log2(x)
fn pyth_add(a, b) -> Scalar;            // sqrt(a^2 + b^2), i.e. a ++ b
fn pyth_sub(a, b) -> Scalar;            // sqrt(a^2 - b^2), i.e. a +-+ b
fn floor(x) -> Scalar;
fn uniform_deviate(x, seed: &mut u64) -> Scalar;
fn normal_deviate(seed: &mut u64) -> Scalar;
```

#### path

Path operations and Hobby's spline algorithm.

```rust
fn to_bez_path(path: &Path) -> Result<BezPath, GraphicsError>;
fn from_bez_path(bp: &BezPath, is_cyclic: bool) -> Path;
fn point_of(path, t: Scalar) -> Point;
fn direction_of(path, t: Scalar) -> Vec2;
fn precontrol_of(path, t: Scalar) -> Point;
fn postcontrol_of(path, t: Scalar) -> Point;
fn subpath(path, t1, t2: Scalar) -> Path;   // supports t1 > t2
fn reverse(path) -> Path;

// path::hobby
fn make_choices(path: &mut Path);  // resolves all KnotDirections to Explicit
```

#### transform

Affine transforms matching MetaPost primitives.

```rust
// Constructors
fn shifted(dx, dy) -> Transform;
fn rotated(degrees) -> Transform;
fn scaled(factor) -> Transform;
fn xscaled(factor) -> Transform;
fn yscaled(factor) -> Transform;
fn slanted(factor) -> Transform;
fn zscaled(a, b) -> Transform;      // complex multiplication

// Composition
fn compose(first, second: &Transform) -> Transform;
fn inverse(t: &Transform) -> Option<Transform>;
fn determinant(t: &Transform) -> Scalar;

// Application (to various types)
fn transform_point(t, p: Point) -> Point;
fn transform_vec(t, v: Vec2) -> Vec2;
fn transform_knot(t, knot: &Knot) -> Knot;
fn transform_path(t, path: &Path) -> Path;
fn transform_pen(t, pen: &Pen) -> Pen;
fn transform_color(t, c: Color) -> Color;       // no-op
fn transform_object(t, obj: &GraphicsObject) -> GraphicsObject;
fn transform_picture(t, pic: &Picture) -> Picture;
```

#### pen

Pen operations: creation, conversion, offset, convex hull.

```rust
fn pencircle(diameter: Scalar) -> Pen;
fn nullpen() -> Pen;
fn makepen(path: &Path) -> Result<Pen, GraphicsError>;  // cyclic path -> polygon
fn makepath(pen: &Pen) -> Path;                          // pen -> cyclic path
fn penoffset(pen: &Pen, dir: Vec2) -> Point;             // support point
fn convex_hull(points: &[Point]) -> Vec<Point>;
```

#### intersection

Curve-curve intersection via recursive bisection.

```rust
struct Intersection { t1: Scalar, t2: Scalar }

fn intersection_times(path1, path2: &Path) -> Option<Intersection>;
fn all_intersection_times(path1, path2: &Path) -> Vec<Intersection>;
```

#### picture

Picture assembly: fill, stroke, clip, setbounds, bounding box.

```rust
fn addto_contour(pic, path, color, pen: Option<Pen>, line_join, miter_limit);
fn addto_doublepath(pic, path, pen, color, dash, line_cap, line_join, miter_limit);
fn addto_also(target: &mut Picture, source: &Picture);
fn clip(pic: &mut Picture, clip_path: Path);
fn setbounds(pic: &mut Picture, bounds_path: Path);

struct BoundingBox { min_x, min_y, max_x, max_y: Scalar }
  BoundingBox::EMPTY, is_valid(), expand_by(point), union(other)

fn path_bbox(path: &Path) -> BoundingBox;
fn picture_bbox(pic: &Picture, true_corners: bool) -> BoundingBox;
```

### postmeta-svg

Converts `Picture` to SVG using the `svg` crate. Depends on `svg` 0.18
and `postmeta-graphics`.

```rust
fn render(picture: &Picture) -> svg::Document;
fn render_to_string(picture: &Picture) -> String;
fn render_with_options(picture: &Picture, opts: &RenderOptions) -> svg::Document;

struct RenderOptions {
    margin: Scalar,      // default 1.0bp
    precision: usize,    // default 4 decimal places
    true_corners: bool,  // default false
}
```

SVG output details:
- Y-axis flip via root `<g transform="scale(1,-1)">`
- Fill → `<path>` with fill attribute
- Stroke → `<path>` with stroke attributes (width, cap, join, dash)
- Text → `<text>` with counter-flip matrix so text reads correctly
- Clip → `<defs><clipPath>` + `<g clip-path="url(#...)">`
- SetBounds → transparent (contents rendered without wrapping)

### postmeta-core

Hand-written recursive-descent parser and tree-walking interpreter.
Implements only the ~210 engine primitives; macros like `draw`, `fill`,
`--`, `---`, etc. are defined in `plain.mp`. Depends on
`postmeta-graphics`.

```rust
// token.rs
struct Span { start: u32, end: u32 }   // byte offsets
struct Token { kind: TokenKind, span: Span }
enum TokenKind {
    Symbolic(String),    // identifiers, operators, keywords (meaning from hash lookup)
    Numeric(Scalar),     // non-negative f64
    StringLit(String),   // "..." (no escapes)
    Eof,
}

// scanner.rs
struct ScanError { message: String, span: Span }
struct Scanner<'src>
  Scanner::new(source: &str)
  scanner.next_token() -> Token
  scanner.scan_all() -> Vec<Token>
  scanner.errors() -> &[ScanError]
```

The scanner implements mp.web §64 character classes (21 classes). Same-class
characters merge into single tokens (e.g. `<=`, `:=`, `..`, `+-+`). Isolated
classes: `( ) , ;`. Period handling: `.5` → numeric, `..` → symbolic, lone
`.` → ignored.

The parser mirrors the original 4-level expression hierarchy:
primary → secondary → tertiary → expression.

Macro expansion happens at the token level (between scanner and parser).

A `trait FileSystem` abstracts file access for WASM compatibility.

### postmeta-cli

Reads `lib/plain.mp`, then the user file. Outputs SVG files via
`postmeta-svg`. Implements `OsFileSystem` for the `FileSystem` trait.

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

## Quick References (from MetaPost User's Manual)

- [ref-language.md](ref-language.md) — Data types, paths, equations, variables, macros, drawing model, scoping, control flow
- [ref-operators.md](ref-operators.md) — All operators by category with types and precedence
- [ref-internals.md](ref-internals.md) — Internal variables, constants, commands, drawing options
- [ref-syntax.md](ref-syntax.md) — Complete BNF grammar, character classes, tokenization rules
