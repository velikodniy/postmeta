# MetaPost Internal Variables, Constants & Commands

Extracted from `mpman-app-refman.tex`. Items marked `†` are plain.mp
macros.

## Internal Numeric Variables

| Name | Default | Description |
|------|---------|-------------|
| `†ahangle` | 45 | Arrowhead angle (degrees) |
| `†ahlength` | 4bp | Arrowhead size |
| `†bboxmargin` | 2bp | Extra space from `bbox` |
| `charcode` | — | Current figure number |
| `day` | — | Current day of month |
| `defaultcolormodel` | 5 (rgb) | Initial color model (1=none, 3=grey, 5=rgb, 7=cmyk) |
| `†defaultpen` | — | Index for `pickup` default pen |
| `†defaultscale` | 1 | Font scale factor for labels |
| `†dotlabeldiam` | 3bp | Dot diameter for `dotlabel` |
| `hour` | — | Hour when job started |
| `hppp` | — | Horizontal points per pixel (bitmap) |
| `†labeloffset` | 3bp | Offset distance for labels |
| `linecap` | 1 | 0=butt, 1=round, 2=square |
| `linejoin` | 1 | 0=miter, 1=round, 2=bevel |
| `minute` | — | Minute when job started |
| `miterlimit` | 10 | Miter length limit |
| `month` | — | Current month |
| `pausing` | 0 | >0 to pause before each line |
| `prologues` | 0 | Font embedding mode (0–3) |
| `showstopping` | 0 | >0 to stop after `show` |
| `time` | — | Minutes past midnight |
| `tracingcapsules` | 0 | Show capsules |
| `tracingchoices` | 0 | Show path control points |
| `tracingcommands` | 0 | Show commands as executed |
| `tracingequations` | 0 | Show variables when known |
| `tracinglostchars` | 0 | Show missing font chars |
| `tracingmacros` | 0 | Show macro expansion |
| `tracingonline` | 0 | Show diagnostics on terminal |
| `tracingoutput` | 0 | Show digitized edges |
| `tracingrestores` | 0 | Show variable/internal restores |
| `tracingspecs` | 0 | Show path subdivision (polygon pen) |
| `tracingstats` | 0 | Memory usage at end of job |
| `truecorners` | 0 | >0: ignore `setbounds` for corners |
| `vppp` | — | Vertical points per pixel |
| `warningcheck` | 4096 | Warn when value exceeds this |
| `year` | — | Current year |

## Internal String Variables

| Name | Default | Description |
|------|---------|-------------|
| `jobname` | — | Base name of input file |
| `outputformat` | "eps" | Backend: "eps", "svg", "png" |
| `outputtemplate` | "%j.%c" | Output filename pattern |
| `outputfilename` | — | Last output file written |

## Predefined Variables

| Name | Type | Description |
|------|------|-------------|
| `†background` | color | Color for `unfill`/`undraw` (white) |
| `†currentpen` | pen | Last pen picked up |
| `†currentpicture` | picture | Accumulates draw/fill results |
| `†cuttings` | path | Subpath cut by last `cutbefore`/`cutafter` |
| `†defaultfont` | string | Font for label strings |
| `†extra_beginfig` | string | Commands scanned by `beginfig` |
| `†extra_endfig` | string | Commands scanned by `endfig` |

## Predefined Constants

| Name | Type | Value |
|------|------|-------|
| `†black` | color | (0,0,0) |
| `†white` | color | (1,1,1) |
| `†red` | color | (1,0,0) |
| `†green` | color | (0,1,0) |
| `†blue` | color | (0,0,1) |
| `†origin` | pair | (0,0) |
| `†up` | pair | (0,1) |
| `†down` | pair | (0,-1) |
| `†right` | pair | (1,0) |
| `†left` | pair | (-1,0) |
| `†bp` | numeric | 1 (PostScript point) |
| `†pt` | numeric | 0.99626 |
| `†in` | numeric | 72 |
| `†cm` | numeric | 28.34645 |
| `†mm` | numeric | 2.83464 |
| `†pc` | numeric | 11.95517 |
| `†cc` | numeric | 12.79213 |
| `†dd` | numeric | 1.06601 |
| `†epsilon` | numeric | 1/65536 |
| `†infinity` | numeric | 4095.99998 |
| `†fullcircle` | path | Unit-diameter circle at origin |
| `†halfcircle` | path | Upper half of fullcircle |
| `†quartercircle` | path | First quadrant of fullcircle |
| `†unitsquare` | path | (0,0)--(1,0)--(1,1)--(0,1)--cycle |
| `†identity` | transform | Identity transformation |
| `pencircle` | pen | Circular pen, diameter 1 |
| `†pensquare` | pen | Square pen, side 1 |
| `nullpen` | pen | Empty pen |
| `nullpicture` | picture | Empty picture |
| `true` | boolean | true |
| `false` | boolean | false |
| `†butt` | numeric | 0 (linecap) |
| `†rounded` | numeric | 1 (linecap/linejoin) |
| `†squared` | numeric | 2 (linecap) |
| `†mitered` | numeric | 0 (linejoin) |
| `†beveled` | numeric | 2 (linejoin) |
| `†evenly` | picture | Dash pattern for equal dashes |
| `†withdots` | picture | Dash pattern for dots |

## Commands (Engine Primitives)

| Command | Description |
|---------|-------------|
| `addto V also P` | Merge picture P into picture variable V |
| `addto V contour C opts` | Fill cyclic path C into V |
| `addto V doublepath P opts` | Stroke path P into V |
| `clip V to C` | Clip picture V to cyclic path C |
| `setbounds V to C` | Override bounding box of V |
| `shipout P` | Output picture P as a figure |
| `save t₁, t₂, ...` | Make symbols local |
| `interim x := e` | Locally change internal variable |
| `newinternal [type] t₁, ...` | Declare new internal variables |
| `show e₁, e₂, ...` | Print expression values |
| `showvariable t₁, ...` | Print variable info |
| `showtoken t₁, ...` | Print token meaning |
| `showdependencies` | Print unsolved equations |
| `message s` | Print string to terminal |
| `errmessage s` | Show error and enter interactive mode |
| `errhelp s` | Set help text for interactive mode |
| `write s to f` | Write string to file |
| `special s` | Raw PostScript output |
| `let t₁ = t₂` | Alias one token to another |
| `randomseed := n` | Set random seed |

## Drawing Options

Used with `addto` / `draw` / `fill` commands:

| Option | Description |
|--------|-------------|
| `withcolor c` | Generic color (auto-selects model) |
| `withrgbcolor c` | RGB color |
| `withcmykcolor c` | CMYK color |
| `withgreyscale n` | Greyscale (0=black, 1=white) |
| `withoutcolor` | No color output |
| `withpen p` | Apply pen |
| `dashed d` | Apply dash pattern (picture) |
| `withprescript s` | Prepend raw PostScript |
| `withpostscript s` | Append raw PostScript |

## Plain.mp Commands (Macros)

| Command | Description |
|---------|-------------|
| `†draw p` | Stroke path with current pen |
| `†fill c` | Fill cyclic path |
| `†filldraw c` | Fill and stroke cyclic path |
| `†undraw p` | Erase along path |
| `†unfill c` | Erase inside cyclic path |
| `†unfilldraw c` | Erase path and inside |
| `†drawarrow p` | Draw with arrowhead at end |
| `†drawdblarrow p` | Draw with arrowheads at both ends |
| `†cutdraw p` | Draw with butt end caps |
| `†pickup pen` | Set current pen |
| `†label.sfx(s, z)` | Place text near point |
| `†dotlabel.sfx(s, z)` | Place dot and text |
| `†labels.sfx(n₁,n₂,...)` | Label z-points by number |
| `†dotlabels.sfx(n₁,...)` | Dot-label z-points |
| `†drawoptions(opts)` | Set default drawing options |
| `†buildcycle(p₁,p₂,...)` | Construct closed path from intersecting paths |
| `†dashpattern(on/off ...)` | Create dash pattern |
| `†image(code)` | Execute code, return picture |
| `†incr(v)` / `†decr(v)` | Increment/decrement numeric variable |
| `†thelabel.sfx(s, z)` | Return label as picture |
| `†z.sfx` | Pair (x.sfx, y.sfx) |
