# Adding a Primitive

PostMeta implements only MetaPost's ~210 engine primitives in Rust; everything else (`draw`, `fill`, `--`, `fullcircle`, ...) is a `plain.mp` macro.
Before adding one, check `mp.web` or the manual references — if the name is defined in `plain.mp`, it is NOT a primitive and belongs there instead.

A new primitive touches a short, fixed list of places, each guarded by a compile-time or test-time check.

## 1. Classify the command

Decide which `Command` category the primitive belongs to.
Most new primitives reuse an existing `Command` variant plus a new modifier in the matching op enum:

- unary operator → new `UnaryOp` variant
- binary operator → `PrimaryBinaryOp` / `SecondaryBinaryOp` / `TertiaryBinaryOp` / `ExpressionBinaryOp`, by precedence level
- statement-like command → usually a new `Command` variant; don't insert mid-enum without checking the range predicates (`is_expandable`, `is_secondary_op`, ...) — the exhaustive-classification test fails if a variant lands in the wrong range

## 2. Register it

Add one `Primitive { name, command, modifier }` entry to the `PRIMITIVES` table.
Tests pin the table's uniqueness and count.

## 3. Implement evaluation

Add the match arm in the operator dispatcher, with the body in the domain submodule it belongs to (arithmetic, transforms, strings, paths, pictures, or text).
Statement-like commands are dispatched from the statement parser instead.
If the operator can produce or consume unknown numerics or pairs, also wire its dependency propagation (see `mul_deps`/`transform_deps` for the pattern).

## 4. Test it

Add interpreter-level tests in the themed module that fits, using `TestInterp`.
Cover the happy path, one type-error case, and any degenerate input (empty path, division by zero, unknown operand).

## 5. Check the manual

Keep argument types, precedence, and result type consistent with the manual semantics listed in the reference docs.
