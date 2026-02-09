# MetaPost Language Concepts

Extracted from `mpman.tex` — the MetaPost User's Manual by John Hobby.

## Data Types (10 types)

| Type | Description |
|------|-------------|
| `numeric` | f64 values. In original: fixed-point multiples of 1/65536, range < 4096. |
| `pair` | (x, y) — two numeric components |
| `path` | Piecewise cubic Bézier curve, parametric (X(t), Y(t)) |
| `transform` | Affine: (tₓ + tₓₓ·x + tₓᵧ·y, tᵧ + tᵧₓ·x + tᵧᵧ·y) |
| `color` | (r, g, b) — three components in [0,1]. Alias: `rgbcolor` |
| `cmykcolor` | (c, m, y, k) — four components |
| `string` | Character sequence. Constants in double quotes, no escapes. |
| `boolean` | `true` or `false` |
| `picture` | Collection of graphics objects |
| `pen` | Determines line thickness and calligraphic effects |

## Paths and Bézier Curves

- `..` joins points with smooth cubic splines (Hobby's algorithm)
- `--` is a macro for straight lines: `{curl 1}..{curl 1}`
- `...` is a macro for inflection-free joins: `..tension atleast 1..`
- `cycle` closes a path
- Parameterization: path with n segments has time 0..n
- Each segment is a cubic Bézier with 2 control points
- `controls` allows explicit Bézier control points

### Direction, Tension, Curl

- `{dir θ}` or `{(dx,dy)}` before/after a point sets tangent direction
- `{up}`, `{down}`, `{left}`, `{right}` are predefined directions
- `tension α` between points tightens the curve (default 1, minimum 3/4)
- `tension α and β` for asymmetric tension
- `curl c` at endpoints controls curvature (default 1 = approximately circular)

### Path Operations

| Operation | Description |
|-----------|-------------|
| `point t of p` | Point at time t |
| `direction t of p` | Tangent vector at time t |
| `precontrol t of p` | Last control point before time t |
| `postcontrol t of p` | First control point after time t |
| `subpath (t₁,t₂) of p` | Extract portion (supports t₁ > t₂) |
| `reverse p` | Reverse time parameterization |
| `arclength p` | Total arc length |
| `arctime a of p` | Time where arc length = a |
| `p intersectiontimes q` | (t₁,t₂) of first intersection |
| `length p` | Number of segments |
| `cycle p` | Boolean: is p cyclic? |

## Linear Equations

MetaPost solves systems of linear equations incrementally:
- `=` declares equality (not assignment); `a + b = 3; 2a = b + 3;`
- `:=` is assignment (destroys old value, replaces it)
- Can mix equations and assignments
- Only **linear** equations are allowed (no multiplying two unknowns)
- Pair equations work component-wise: `z1 = (0, .2in)`

### Mediation

`a[x, y]` = `x + a*(y - x)` (point a of the way from x to y)
- `1/3[z3, z6]` = one-third of the way from z3 to z6
- `whatever[z1, z3]` = unknown point on line through z1, z3
- `whatever` generates a fresh anonymous unknown each time

## Variables

- Names are sequences of tags and subscripts: `x2r`, `f.bot`, `a.b`
- The `z` convention: `z<suffix>` = `(x<suffix>, y<suffix>)`
- Period between tags is ignored: `a.b` = two tokens `a`, `b`
- Arrays via numeric subscripts: `x[i]` where i is numeric
- Declaration: `pair pp; path q[];` (use `[]` for generic subscript)
- `save t1, t2` makes variables local to current group
- `interim x := v` makes local change to internal variable

## Scoping

- `begingroup ... endgroup` creates a scope
- `beginfig(n) ... endfig` is a macro that wraps a group
- `save` makes variables local to the enclosing group
- `interim` makes internal variable changes local to the group
- Variables starting with `x`, `y`, `z` are wiped by `beginfig`

## Macros

```metapost
def name(params) = <replacement text> enddef
vardef name.suffix(params) = <body> enddef    % grouped, returns last expr
primarydef a op b = ... enddef                 % binary at primary level
secondarydef a op b = ... enddef
tertiarydef a op b = ... enddef
```

Parameter types: `expr`, `suffix`, `text`

Undelimited parameter types: `expr`, `suffix`, `text`, `primary`,
`secondary`, `tertiary`, `expr p of q`

`vardef` automatically wraps body in `begingroup...endgroup`.

The `@#` suffix parameter captures trailing suffix:
`vardef f@#(expr x) = ... @# ... enddef`

## Drawing Model

- `currentpicture` accumulates drawing operations
- `beginfig(n)` starts a new picture
- `endfig` ships out the picture as figure n

### Low-level (primitives)

```
addto <pic> contour <cyclic path> [options]    % fill
addto <pic> doublepath <path> [options]         % stroke
addto <pic> also <picture> [options]            % merge
clip <pic> to <cyclic path>
setbounds <pic> to <cyclic path>
shipout <pic>
```

### High-level (plain.mp macros)

```
fill <cyclic path> [options]            % addto currentpicture contour
draw <path> [options]                   % addto currentpicture doublepath
filldraw <cyclic path> [options]        % fill + stroke outline
unfill <cyclic path>                    % fill with background color
undraw <path>                           % draw with background color
pickup <pen>                            % set currentpen
drawarrow <path>                        % draw with arrowhead
drawdblarrow <path>                     % draw with arrowheads at both ends
```

### Options

`withcolor c`, `withpen p`, `dashed d`, `withrgbcolor c`,
`withcmykcolor c`, `withgreyscale n`, `withoutcolor`

## Pens

- `pencircle scaled d` — circular pen of diameter d
- Default pen: `pencircle scaled 0.5bp`
- `pickup pencircle scaled 4pt` — set pen for subsequent draws
- `makepen(path)` — polygonal pen from convex hull of path knots
- `makepath(pen)` — cyclic path from pen boundary
- `penoffset dir of pen` — support point in given direction

## Transforms

Six-component affine: (tₓ, tᵧ, tₓₓ, tₓᵧ, tᵧₓ, tᵧᵧ)

Apply: `p transformed T` = `(tₓ + tₓₓ·pₓ + tₓᵧ·pᵧ, tᵧ + tᵧₓ·pₓ + tᵧᵧ·pᵧ)`

Transforms apply to: pairs, paths, pictures, pens, transforms.

Can solve for transforms: `T = identity shifted (1,0) rotated 30;`

## Text and Labels

- `label.sfx("text", z)` — place text near point
- `dotlabel.sfx("text", z)` — place dot + text
- `btex <TeX commands> etex` — TeX-typeset label (picture)
- `infont` operator: `"text" infont "fontname"` → picture
- `defaultfont`, `defaultscale` control label appearance

## Picture Inspection

`for p within pic:` iterates over picture components.

Each component has: `pathpart`, `penpart`, `dashpart`, `textpart`,
`fontpart`, `colormodel`, type predicates (`filled`, `stroked`,
`textual`, `clipped`, `bounded`).

## I/O

- `input "filename"` — read and execute file
- `scantokens "string"` — parse string as MetaPost input
- `readfrom "file"` — read one line from file
- `write "string" to "file"` — write to file
- `message "string"` — print to terminal
- `show expr` — print expression value

## Control Flow

```
if <bool>: ... elseif <bool>: ... else: ... fi
for i = a upto b: ... endfor
for i = a downto b: ... endfor
for i = a step s until b: ... endfor
for i = e1, e2, e3: ... endfor          % list
forsuffixes s = s1, s2: ... endfor       % suffix list
forever: ... endfor                       % infinite (use exitif)
exitif <bool>;                            % break from loop
```
