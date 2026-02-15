//! Path construction parsing.
//!
//! Handles `..` path joins, `tension`/`controls` options, `{dir}` / `{curl n}`
//! brace directions, and `cycle`.

use postmeta_graphics::path::hobby;
use postmeta_graphics::types::{Knot, KnotDirection, Path, Point, Scalar};

use crate::command::Command;
use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::types::Value;

use super::Interpreter;
use super::helpers::{value_to_pair, value_to_scalar};

// ---------------------------------------------------------------------------
// Path join pending state
// ---------------------------------------------------------------------------

/// Pending left-side specification for the next knot in path construction.
///
/// When `tension t1 and t2` or `controls p1 and p2` is parsed, the second
/// value applies to the *next* knot's left side and must be carried forward.
enum PendingJoin {
    /// Pending left tension for the next knot.
    Tension(Scalar),
    /// Pending explicit left control point for the next knot.
    Control(Point),
}

impl Interpreter {
    /// Parse a path expression starting from the given left-hand value.
    pub(super) fn scan_path_construction(
        &mut self,
        left: super::ExprResultValue,
    ) -> InterpResult<super::ExprResultValue> {
        let first_expr = left.exp;
        let (mut knots, mut is_cyclic) = match first_expr {
            Value::Pair(x, y) => (vec![Knot::new(Point::new(x, y))], false),
            Value::Path(p) => (p.knots, p.is_cyclic),
            Value::Numeric(v) => {
                return Err(InterpreterError::new(
                    ErrorKind::TypeError,
                    format!("Expected pair or path in path construction, got numeric {v}"),
                ));
            }
            other => {
                return Err(InterpreterError::new(
                    ErrorKind::TypeError,
                    format!(
                        "Expected pair or path in path construction, got {}",
                        other.ty()
                    ),
                ));
            }
        };

        loop {
            // Parse optional pre-join direction {dir} or {curl n}.
            // Multiple consecutive directions can appear when macros like
            // `--` expand to `{curl 1}..{curl 1}` — the last one wins.
            let mut pre_dir = if self.cur.command == Command::LeftBrace {
                Some(self.scan_brace_direction()?)
            } else {
                None
            };
            while self.cur.command == Command::LeftBrace {
                pre_dir = Some(self.scan_brace_direction()?);
            }

            // Parse the join operator
            let join_type = if self.cur.command == Command::PathJoin {
                let modifier = self.cur.modifier;
                self.get_x_next();
                modifier
            } else if self.cur.command == Command::Ampersand {
                self.get_x_next();
                u16::MAX // special value for &
            } else {
                // A trailing `{dir}` at the end of an open path applies to the
                // incoming (left) side of the last knot, not its outgoing side.
                if let Some(dir) = pre_dir {
                    if let Some(last) = knots.last_mut() {
                        last.left = dir;
                    }
                }
                break;
            };

            // Direction before a join applies to the outgoing (right) side of
            // the current knot.
            if let Some(dir) = pre_dir {
                if let Some(last) = knots.last_mut() {
                    last.right = dir;
                }
            }

            // Parse tension/controls — returns pending left-side for next knot
            let pending = if join_type == u16::MAX {
                None
            } else {
                self.parse_join_options(&mut knots)?
            };

            // Parse optional post-join direction {dir} or {curl n}
            let post_dir = if self.cur.command == Command::LeftBrace {
                Some(self.scan_brace_direction()?)
            } else {
                None
            };

            // Check for cycle
            if self.cur.command == Command::Cycle {
                is_cyclic = true;
                if knots.is_empty() {
                    self.report_error(
                        ErrorKind::TypeError,
                        "Cannot close `cycle` on an empty path",
                    );
                    self.get_x_next();
                    break;
                }
                if let Some(dir) = post_dir {
                    knots[0].left = dir;
                }
                // Apply pending join to first knot (cycle target)
                match pending {
                    Some(PendingJoin::Tension(t)) => knots[0].left_tension = t,
                    Some(PendingJoin::Control(pt)) => {
                        knots[0].left = KnotDirection::Explicit(pt);
                    }
                    None => {}
                }
                self.get_x_next();
                break;
            }

            // Parse the next point
            let point_val = self.scan_tertiary()?.exp;

            // `&` can concatenate paths; a pair is treated as a one-knot path.
            if join_type == u16::MAX {
                let mut rhs_knots = match point_val {
                    Value::Path(rhs) => rhs.knots,
                    Value::Pair(x, y) => vec![Knot::new(Point::new(x, y))],
                    other => {
                        return Err(InterpreterError::new(
                            ErrorKind::TypeError,
                            format!(
                                "`&` requires a path or pair on the right, got {}",
                                other.ty()
                            ),
                        ));
                    }
                };

                if let Some(dir) = post_dir
                    && let Some(first) = rhs_knots.first_mut()
                {
                    first.left = dir;
                }

                Self::append_path_concat(&mut knots, rhs_knots);
                continue;
            }

            match point_val {
                // MetaPost allows `..` with a path operand in macros like
                // `buildcycle`; treat this as joining to the first knot of the
                // right path and appending the whole path.
                Value::Path(mut rhs) => {
                    if rhs.knots.is_empty() {
                        return Err(InterpreterError::new(
                            ErrorKind::TypeError,
                            "Expected non-empty path in path construction",
                        ));
                    }

                    if let Some(dir) = post_dir
                        && let Some(first) = rhs.knots.first_mut()
                    {
                        first.left = dir;
                    }

                    if let Some(first) = rhs.knots.first_mut() {
                        match pending {
                            Some(PendingJoin::Tension(t)) => first.left_tension = t,
                            Some(PendingJoin::Control(pt)) => {
                                first.left = KnotDirection::Explicit(pt);
                            }
                            None => {}
                        }
                    }

                    knots.append(&mut rhs.knots);
                }
                other => {
                    let mut knot = Self::value_to_knot(&other)?;
                    if let Some(dir) = post_dir {
                        knot.left = dir;
                    }
                    // Apply pending left-side join from tension/controls
                    match pending {
                        Some(PendingJoin::Tension(t)) => knot.left_tension = t,
                        Some(PendingJoin::Control(pt)) => knot.left = KnotDirection::Explicit(pt),
                        None => {}
                    }
                    knots.push(knot);
                }
            }
        }

        // Build the path
        let mut path_obj = Path::from_knots(knots, is_cyclic);
        hobby::make_choices(&mut path_obj);

        Ok(super::ExprResultValue::plain(Value::Path(path_obj)))
    }

    /// Concatenate path knots for `&`.
    ///
    /// If the tail point of `lhs` equals the head point of `rhs`, merge the
    /// shared knot and keep the outgoing side from `rhs`.
    fn append_path_concat(lhs: &mut Vec<Knot>, rhs: Vec<Knot>) {
        let mut rhs_iter = rhs.into_iter();
        let Some(first_rhs) = rhs_iter.next() else {
            return;
        };

        if lhs.is_empty() {
            lhs.push(first_rhs);
            lhs.extend(rhs_iter);
            return;
        }

        let li = lhs.len() - 1;
        let lp = lhs[li].point;
        let rp = first_rhs.point;
        if (lp.x - rp.x).abs() < 1e-9 && (lp.y - rp.y).abs() < 1e-9 {
            lhs[li].right = first_rhs.right;
            lhs[li].right_tension = first_rhs.right_tension;
            lhs.extend(rhs_iter);
            return;
        }

        lhs.push(first_rhs);
        lhs.extend(rhs_iter);
    }

    /// Parse tension/controls options after `..`.
    ///
    /// Returns a pending left-side specification for the *next* knot:
    /// - `Some(PendingJoin::Tension(t))` — the next knot's `left_tension`
    /// - `Some(PendingJoin::Control(pt))` — the next knot's `left` direction (explicit)
    /// - `None` — no pending state
    fn parse_join_options(&mut self, knots: &mut [Knot]) -> InterpResult<Option<PendingJoin>> {
        match self.cur.command {
            Command::Tension => {
                self.get_x_next();
                let at_least = self.cur.command == Command::AtLeast;
                if at_least {
                    self.get_x_next();
                }
                let t1 = value_to_scalar(&self.scan_primary()?.exp)?;
                let t1 = if at_least { -t1.abs() } else { t1 };

                let t2 = if self.cur.command == Command::And {
                    self.get_x_next();
                    let at_least2 = self.cur.command == Command::AtLeast;
                    if at_least2 {
                        self.get_x_next();
                    }
                    let t_val = value_to_scalar(&self.scan_primary()?.exp)?;
                    if at_least2 { -t_val.abs() } else { t_val }
                } else {
                    t1
                };

                if let Some(last) = knots.last_mut() {
                    last.right_tension = t1;
                }

                // Path syntax requires a second `..` after tension options.
                if self.cur.command != Command::PathJoin {
                    return Err(InterpreterError::new(
                        ErrorKind::UnexpectedToken,
                        "Expected `..` after tension specification",
                    ));
                }
                self.get_x_next();

                Ok(Some(PendingJoin::Tension(t2)))
            }
            Command::Controls => {
                self.get_x_next();
                let cp1 = self.scan_primary()?.exp;
                let (x1, y1) = value_to_pair(&cp1)?;

                let (x2, y2) = if self.cur.command == Command::And {
                    self.get_x_next();
                    let cp2 = self.scan_primary()?.exp;
                    value_to_pair(&cp2)?
                } else {
                    (x1, y1)
                };

                if let Some(last) = knots.last_mut() {
                    last.right = KnotDirection::Explicit(Point::new(x1, y1));
                }

                // Path syntax requires a second `..` after control options.
                if self.cur.command != Command::PathJoin {
                    return Err(InterpreterError::new(
                        ErrorKind::UnexpectedToken,
                        "Expected `..` after controls specification",
                    ));
                }
                self.get_x_next();

                Ok(Some(PendingJoin::Control(Point::new(x2, y2))))
            }
            _ => Ok(None), // No special join options
        }
    }

    /// Convert a value to a path knot.
    fn value_to_knot(val: &Value) -> InterpResult<Knot> {
        match val {
            Value::Pair(x, y) => Ok(Knot::new(Point::new(*x, *y))),
            Value::Numeric(v) => {
                // Single numeric — treat as (v, 0)? Or error?
                // In MetaPost, a numeric in path context uses z-convention
                // For now, error
                Err(InterpreterError::new(
                    ErrorKind::TypeError,
                    format!("Expected pair in path, got numeric {v}"),
                ))
            }
            _ => Err(InterpreterError::new(
                ErrorKind::TypeError,
                format!("Expected pair in path, got {}", val.ty()),
            )),
        }
    }

    /// Parse a brace-enclosed direction: `{dir}` or `{curl n}`.
    fn scan_brace_direction(&mut self) -> InterpResult<KnotDirection> {
        self.get_x_next(); // skip `{`

        if self.cur.command == Command::CurlCommand {
            // {curl <numeric>}
            self.get_x_next();
            let curl_val = value_to_scalar(&self.scan_tertiary()?.exp)?;
            if self.cur.command == Command::RightBrace {
                self.get_x_next();
            } else {
                self.report_error(
                    ErrorKind::MissingToken,
                    "Expected `}` after `curl` direction",
                );
            }
            Ok(KnotDirection::Curl(curl_val))
        } else {
            // {<expression>} — direction as pair, or numeric angle in degrees
            // (converted to internal radians).
            let dir = self.scan_expression()?.exp;
            if self.cur.command == Command::RightBrace {
                self.get_x_next();
            } else {
                self.report_error(
                    ErrorKind::MissingToken,
                    "Expected `}` after direction expression",
                );
            }
            Self::value_to_direction(&dir)
        }
    }

    /// Convert a value to a direction for path construction.
    ///
    /// Internal direction angles are stored in radians.
    /// Numeric inputs are interpreted as degrees per `MetaPost` syntax.
    fn value_to_direction(val: &Value) -> InterpResult<KnotDirection> {
        match val {
            Value::Pair(x, y) => Ok(KnotDirection::Given(y.atan2(*x))),
            Value::Numeric(v) => Ok(KnotDirection::Given(v.to_radians())),
            _ => Err(InterpreterError::new(
                ErrorKind::TypeError,
                format!("Expected direction, got {}", val.ty()),
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::variables::VarValue;

    #[test]
    fn direction_numeric_is_degrees_in_input() {
        let dir = Interpreter::value_to_direction(&Value::Numeric(90.0))
            .expect("numeric direction should parse");

        match dir {
            KnotDirection::Given(angle) => {
                assert!((angle - core::f64::consts::FRAC_PI_2).abs() < 1e-12);
            }
            _ => panic!("expected given direction"),
        }
    }

    #[test]
    fn direction_pair_is_converted_to_radians() {
        let dir = Interpreter::value_to_direction(&Value::Pair(0.0, 1.0))
            .expect("pair direction should parse");

        match dir {
            KnotDirection::Given(angle) => {
                assert!((angle - core::f64::consts::FRAC_PI_2).abs() < 1e-12);
            }
            _ => panic!("expected given direction"),
        }
    }

    #[test]
    fn endpoint_direction_applies_to_left_side() {
        let mut interp = Interpreter::new();
        interp
            .run("path p; p := (0,0){(0,1)} .. (2,0){(1,0)};")
            .expect("path construction should parse");

        let pid = interp
            .variables
            .lookup_existing("p")
            .expect("path variable p should exist");
        let path = match interp.variables.get(pid) {
            VarValue::Known(Value::Path(p)) => p,
            other => panic!("expected path variable, got {other:?}"),
        };

        let p0 = path.knots[0].point;
        let p1 = path.knots[1].point;
        let r0 = match path.knots[0].right {
            KnotDirection::Explicit(cp) => cp,
            ref other => panic!("knot 0 right is not explicit: {other:?}"),
        };
        let l1 = match path.knots[1].left {
            KnotDirection::Explicit(cp) => cp,
            ref other => panic!("knot 1 left is not explicit: {other:?}"),
        };

        // Start direction is up: outgoing tangent at p0 should be vertical.
        let t0 = r0 - p0;
        assert!(t0.y > 0.0, "expected upward start tangent, got {t0:?}");
        assert!(
            t0.x.abs() < 1e-9,
            "expected vertical start tangent, got {t0:?}"
        );

        // End direction is right: incoming tangent at p1 should be horizontal.
        let t1 = p1 - l1;
        assert!(t1.x > 0.0, "expected rightward end tangent, got {t1:?}");
        assert!(
            t1.y.abs() < 1e-9,
            "expected horizontal end tangent, got {t1:?}"
        );
    }

    #[test]
    fn tension_option_consumes_trailing_join() {
        let mut interp = Interpreter::new();
        interp
            .run("path p; p := (0,0) .. tension 2 .. (1,1) .. (2,0);")
            .expect("tension path should parse");

        let pid = interp
            .variables
            .lookup_existing("p")
            .expect("path variable p should exist");
        let path = match interp.variables.get(pid) {
            VarValue::Known(Value::Path(p)) => p,
            other => panic!("expected path variable, got {other:?}"),
        };
        assert_eq!(path.knots.len(), 3, "expected three knots");

        // Path choices should have been resolved to explicit controls.
        assert!(matches!(path.knots[0].right, KnotDirection::Explicit(_)));
        assert!(matches!(path.knots[1].left, KnotDirection::Explicit(_)));
        assert!(matches!(path.knots[1].right, KnotDirection::Explicit(_)));
        assert!(matches!(path.knots[2].left, KnotDirection::Explicit(_)));
    }

    #[test]
    fn controls_option_preserves_explicit_controls() {
        let mut interp = Interpreter::new();
        interp
            .run(
                "pair A,B,C,D; path p; \
                 A:=(0,0); B:=(-1,2); C:=(3,3); D:=(2,0); \
                 p := A .. controls B and C .. D;",
            )
            .expect("controls path should parse");

        let pid = interp
            .variables
            .lookup_existing("p")
            .expect("path variable p should exist");
        let path = match interp.variables.get(pid) {
            VarValue::Known(Value::Path(p)) => p,
            other => panic!("expected path variable, got {other:?}"),
        };

        assert_eq!(path.knots.len(), 2, "expected two knots");

        match path.knots[0].right {
            KnotDirection::Explicit(cp) => {
                assert!((cp.x + 1.0).abs() < 1e-9, "cp.x={}", cp.x);
                assert!((cp.y - 2.0).abs() < 1e-9, "cp.y={}", cp.y);
            }
            ref other => panic!("knot 0 right is not explicit: {other:?}"),
        }

        match path.knots[1].left {
            KnotDirection::Explicit(cp) => {
                assert!((cp.x - 3.0).abs() < 1e-9, "cp.x={}", cp.x);
                assert!((cp.y - 3.0).abs() < 1e-9, "cp.y={}", cp.y);
            }
            ref other => panic!("knot 1 left is not explicit: {other:?}"),
        }
    }

    #[test]
    fn ampersand_concatenates_paths() {
        let mut interp = Interpreter::new();
        interp
            .run(
                "path p,q,r;
                 p := (0,0)..(1,0);
                 q := (1,0)..(1,1);
                 r := p & q;",
            )
            .expect("path concatenation should parse");

        let rid = interp
            .variables
            .lookup_existing("r")
            .expect("path variable r should exist");
        let path = match interp.variables.get(rid) {
            VarValue::Known(Value::Path(p)) => p,
            other => panic!("expected path variable, got {other:?}"),
        };

        assert_eq!(path.knots.len(), 3, "expected merged shared knot");
        assert!(!path.is_cyclic);
        assert!(matches!(path.knots[0].right, KnotDirection::Explicit(_)));
        assert!(matches!(path.knots[1].left, KnotDirection::Explicit(_)));
        assert!(matches!(path.knots[1].right, KnotDirection::Explicit(_)));
        assert!(matches!(path.knots[2].left, KnotDirection::Explicit(_)));
    }

    #[test]
    fn ampersand_accepts_pair_rhs() {
        let mut interp = Interpreter::new();
        interp
            .run(
                "path p,q;
                 p := (0,0)..(1,0);
                 q := p & (2,0);",
            )
            .expect("path and pair concatenation should parse");

        let qid = interp
            .variables
            .lookup_existing("q")
            .expect("path variable q should exist");
        let path = match interp.variables.get(qid) {
            VarValue::Known(Value::Path(p)) => p,
            other => panic!("expected path variable, got {other:?}"),
        };

        assert_eq!(path.knots.len(), 3, "expected appended pair knot");
        assert!((path.knots[2].point.x - 2.0).abs() < 1e-9);
        assert!((path.knots[2].point.y - 0.0).abs() < 1e-9);
    }

    #[test]
    fn path_join_accepts_path_rhs() {
        let mut interp = Interpreter::new();
        interp
            .run(
                "path a,b,c;
                 a := (0,0)..(1,0);
                 b := (1,1)..(2,1);
                 c := a .. b;",
            )
            .expect("path join with path rhs should parse");

        let cid = interp
            .variables
            .lookup_existing("c")
            .expect("path variable c should exist");
        let path = match interp.variables.get(cid) {
            VarValue::Known(Value::Path(p)) => p,
            other => panic!("expected path variable, got {other:?}"),
        };

        assert_eq!(path.knots.len(), 4, "expected all rhs knots appended");
    }
}
