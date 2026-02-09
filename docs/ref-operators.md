# MetaPost Operator Reference

Extracted from `mpman-app-optab.tex`. Operators marked with `†` are
plain.mp macros (not engine primitives).

## Precedence Levels

```
primary  → unary ops, of-operators, *, /, **, and, dotprod, div, infont, mod
secondary → +, -, ++, +-+, or, intersectionpoint, intersectiontimes
tertiary  → &, <, <=, <>, =, >, >=, cutafter, cutbefore
```

## Arithmetic

| Op | Left | Right | Result | Description |
|----|------|-------|--------|-------------|
| `*` | numeric | numeric/pair/color | same | Multiplication |
| `*` | pair/color | numeric | same | Multiplication |
| `/` | pair/color/numeric | numeric | same | Division |
| `**` | numeric | numeric | numeric | Exponentiation |
| `+` | numeric/pair/color | same | same | Addition |
| `-` | numeric/pair/color | same | same | Subtraction |
| `-` | — | numeric/pair/color | same | Negation (unary) |
| `++` | numeric | numeric | numeric | Pythagorean addition √(l²+r²) |
| `+-+` | numeric | numeric | numeric | Pythagorean subtraction √(l²-r²) |

## Unary Numeric→Numeric

| Op | Description |
|----|-------------|
| `abs` | Absolute value (also: Euclidean length of pair) |
| `floor` | Greatest integer ≤ argument |
| `†ceiling` | Least integer ≥ argument |
| `sqrt` | Square root |
| `sind` | Sine (degrees) |
| `cosd` | Cosine (degrees) |
| `mexp` | 2^(x/256) |
| `mlog` | 256·log₂(x) |
| `†round` | Round to nearest integer (also works on pairs) |
| `normaldeviate` | Random, mean 0, stddev 1 (nullary) |
| `uniformdeviate` | Random in [0, arg) |
| `angle` | pair→numeric: 2-arg arctangent (degrees) |
| `†dir` | numeric→pair: (cos θ, sin θ) |
| `length` | path→segment count; string→char count |
| `arclength` | path→numeric: arc length |
| `fontsize` | string→numeric: point size of font |
| `decimal` | numeric→string: decimal representation |
| `oct` | string→numeric: octal parse |
| `hex` | string→numeric: hex parse |
| `ASCII` | string→numeric: first char code |
| `char` | numeric→string: character with given code |
| `odd` | numeric→boolean |

## Path Operators

| Op | Left | Right | Result | Description |
|----|------|-------|--------|-------------|
| `point of` | numeric | path | pair | Point at time t |
| `direction of` | numeric | path | pair | Tangent at time t |
| `†directionpoint of` | pair | path | pair | Point where path has given direction |
| `directiontime of` | pair | path | numeric | Time when path has given direction |
| `precontrol of` | numeric | path | pair | Last Bézier control point ending at t |
| `postcontrol of` | numeric | path | pair | First Bézier control point starting at t |
| `subpath of` | pair | path | path | Subpath for time range (t₁,t₂) |
| `arctime of` | numeric | path | numeric | Time where arc length = value |
| `intersectiontimes` | path | path | pair | Times (t₁,t₂) at first intersection |
| `†intersectionpoint` | path | path | pair | Point of first intersection |
| `†cutbefore` | path | path | path | Left path after intersection |
| `†cutafter` | path | path | path | Left path before intersection |
| `reverse` | — | path | path | Reverse parameterization |
| `cycle` | — | path | boolean | Is path cyclic? |

## String Operators

| Op | Left | Right | Result | Description |
|----|------|-------|--------|-------------|
| `&` | string | string | string | Concatenation |
| `&` | path | path | path | Path join (end must match start) |
| `substring of` | pair | string | string | Substring by index range |
| `infont` | string | string | picture | Typeset text in font |
| `scantokens` | — | string | tokens | Parse string as MetaPost input |

## Transform Operators (secondary → transformer)

All apply to: picture, path, pair, pen, transform.

| Op | Right Arg | Description |
|----|-----------|-------------|
| `shifted` | pair | Translate |
| `rotated` | numeric | Rotate (degrees, CCW) |
| `scaled` | numeric | Uniform scale |
| `xscaled` | numeric | Scale x only |
| `yscaled` | numeric | Scale y only |
| `slanted` | numeric | Shear: (x,y)→(x+s·y, y) |
| `zscaled` | pair | Complex multiply (rotate+scale) |
| `transformed` | transform | Apply general affine |
| `†reflectedabout` | (pair,pair) | Reflect about line |
| `†rotatedaround` | (pair,numeric) | Rotate around point |

## Pen Operators

| Op | Description |
|----|-------------|
| `pencircle` | Nullary: circular pen of diameter 1 |
| `nullpen` | Nullary: empty pen |
| `makepen` | path→pen: convex hull of knots |
| `makepath` | pen→path: cyclic path of pen boundary |
| `penoffset of` | (pair,pen)→pair: support point in given direction |

## Type Testing (unary, any→boolean)

`boolean`, `cmykcolor`, `color`, `numeric`, `pair`, `path`, `pen`,
`picture`, `rgbcolor`, `string`, `transform`, `known`, `unknown`

## Picture Inspection

| Op | Description |
|----|-------------|
| `llcorner` | Lower-left of bounding box |
| `lrcorner` | Lower-right of bounding box |
| `ulcorner` | Upper-left of bounding box |
| `urcorner` | Upper-right of bounding box |
| `†center` | Center of bounding box |
| `†bbox` | Rectangular bounding box path |
| `filled` | Is arg a filled outline? |
| `stroked` | Is arg a stroked line? |
| `textual` | Is arg typeset text? |
| `clipped` | Is arg clipped? |
| `bounded` | Is arg bounded? |
| `pathpart` | Extract path from picture component |
| `penpart` | Extract pen from picture component |
| `dashpart` | Extract dash pattern from picture component |
| `textpart` | Extract text string from picture component |
| `fontpart` | Extract font name from picture component |
| `†colorpart` | Extract color from picture component |
| `colormodel` | Get color model of picture component |

## Part Extractors

| Op | From | Gets |
|----|------|------|
| `xpart` | pair/transform | x / tₓ |
| `ypart` | pair/transform | y / tᵧ |
| `xxpart` | transform | tₓₓ |
| `xypart` | transform | tₓᵧ |
| `yxpart` | transform | tᵧₓ |
| `yypart` | transform | tᵧᵧ |
| `redpart` | color | 1st component |
| `greenpart` | color | 2nd component |
| `bluepart` | color | 3rd component |
| `cyanpart` | cmykcolor | 1st component |
| `magentapart` | cmykcolor | 2nd component |
| `yellowpart` | cmykcolor | 3rd component |
| `blackpart` | cmykcolor | 4th component |
| `greypart` | numeric (grey) | single component |

## Boolean & Comparison

| Op | Description |
|----|-------------|
| `and` | primary binop: logical AND |
| `or` | secondary binop: logical OR |
| `not` | unary: logical NOT |
| `<` `<=` `=` `>=` `>` `<>` | Comparison (tertiary binops) |

## Misc

| Op | Description |
|----|-------------|
| `†whatever` | Nullary: fresh anonymous unknown numeric |
| `†abs` | Pair→numeric: Euclidean length |
| `†unitvector` | Pair→pair: normalize to length 1 |
| `†dotprod` | Pair×pair→numeric: dot product |
| `†div` | numeric×numeric→numeric: integer division |
| `†mod` | numeric×numeric→numeric: remainder |
| `†bot`/`†top`/`†lft`/`†rt` | Pen edge at coordinate |
| `†inverse` | transform→transform: invert |
| `str` | suffix→string |
| `readfrom` | string→string: read line from file |
| `glyph of` | (numeric/string, string)→picture: font glyph to contours |
