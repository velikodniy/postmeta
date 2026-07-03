# Adding a Primitive

PostMeta implements only MetaPost's ~210 engine primitives in Rust; everything
else (`draw`, `fill`, `--`, `fullcircle`, ...) is a macro defined in
`lib/plain.mp`. Before adding a primitive, check `docs/mp.web` or the manual
references in `docs/ref-*.md` — if the name is defined in `plain.mp`, it is NOT
a primitive and belongs there instead.

A new primitive touches a fixed, short list of places. Work through them in
order; each has a compile-time or test-time check that catches omissions.

## 1. Command classification — `postmeta-core/src/command/mod.rs`

Decide which `Command` category the primitive belongs to (unary operator,
secondary/tertiary/expression binary, statement keyword, ...). Most new
primitives reuse an existing `Command` variant plus a new modifier in the
matching op enum:

- Unary operator → add a variant to `UnaryOp` and its `impl_from_modifier!`
  invocation.
- Binary operator → `PrimaryBinaryOp` / `SecondaryBinaryOp` /
  `TertiaryBinaryOp` / `ExpressionBinaryOp`, by precedence level.
- Statement-like command → usually a new `Command` variant. Do NOT insert it
  in the middle of the enum without checking the range predicates
  (`is_expandable`, `is_secondary_op`, ...): the exhaustive-classification
  test in `command/mod.rs` fails if a variant lands in the wrong range.

## 2. Registration — `postmeta-core/src/command/primitives.rs`

Add one `Primitive { name, command, modifier }` entry to the `PRIMITIVES`
table. `primitives_have_unique_names` and `primitive_count` pin the table.

## 3. Evaluation — `postmeta-core/src/interpreter/operators/`

Add the match arm in the dispatcher in `operators/mod.rs`, implementing the
body in the domain submodule it belongs to:

| domain | file |
|---|---|
| numeric/arith ops | `operators/arithmetic.rs` |
| transform ops | `operators/transforms.rs` |
| string ops | `operators/strings.rs` |
| path/pen ops | `operators/paths.rs` |
| picture parts/tests | `operators/pictures.rs` |
| text/font ops | `operators/text.rs` |

Statement-like commands are dispatched from
`interpreter/parser/statements.rs` / `interpreter/statement.rs` instead.

If the operator participates in linear equations (produces or consumes
unknown numerics/pairs), also wire its dependency propagation in
`interpreter/dep_arith.rs` — see `mul_deps`/`transform_deps` for the pattern.

## 4. Tests — `postmeta-core/src/interpreter/tests/`

Add interpreter-level tests in the themed module that fits (`arithmetic.rs`,
`strings.rs`, `paths.rs`, ...) using the `TestInterp` helper. Cover: the happy
path, at least one type-error case, and any degenerate input (empty path,
division by zero, unknown operand).

## 5. Reference check

`docs/ref-operators.md` lists every operator with its type signature — keep
the new primitive consistent with the manual's semantics (argument types,
precedence level, result type).
