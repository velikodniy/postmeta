//! Path construction parsing.
//!
//! Handles `..` path joins, `tension`/`controls` options, `{dir}` / `{curl n}`
//! brace directions, and `cycle`.

use kurbo::Point;

use postmeta_graphics::math;
use postmeta_graphics::path;
use postmeta_graphics::path::hobby;
use postmeta_graphics::types::{Knot, KnotDirection, Path, Scalar};

use crate::command::Command;
use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::types::{Type, Value};

use super::helpers::{value_to_pair, value_to_scalar};
use super::Interpreter;

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
    /// Parse a path expression starting from the current point/expression.
    pub(super) fn scan_path_construction(&mut self) -> InterpResult<()> {
        let first_point = self.take_cur_exp();
        let mut knots = vec![self.value_to_knot(&first_point)?];
        let mut is_cyclic = false;

        loop {
            // Parse optional pre-join direction {dir} or {curl n}
            let pre_dir = if self.cur.command == Command::LeftBrace {
                Some(self.scan_brace_direction()?)
            } else {
                None
            };

            // Set the right direction of the last knot
            if let Some(dir) = pre_dir {
                if let Some(last) = knots.last_mut() {
                    last.right = dir;
                }
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
                break;
            };

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
            self.scan_tertiary()?;
            let point_val = self.take_cur_exp();
            let mut knot = self.value_to_knot(&point_val)?;
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

        // Build the path
        let mut path_obj = Path::from_knots(knots, is_cyclic);
        hobby::make_choices(&mut path_obj);

        self.cur_exp = Value::Path(path_obj);
        self.cur_type = Type::Path;
        Ok(())
    }

    /// Parse tension/controls options after `..`.
    ///
    /// Returns a pending left-side specification for the *next* knot:
    /// - `Some(PendingJoin::Tension(t))` — the next knot's `left_tension`
    /// - `Some(PendingJoin::Control(pt))` — the next knot's `left` direction (explicit)
    /// - `None` — no pending state
    fn parse_join_options(&mut self, knots: &mut Vec<Knot>) -> InterpResult<Option<PendingJoin>> {
        match self.cur.command {
            Command::Tension => {
                self.get_x_next();
                let at_least = self.cur.command == Command::AtLeast;
                if at_least {
                    self.get_x_next();
                }
                self.scan_primary()?;
                let t1 = value_to_scalar(&self.take_cur_exp())?;
                let t1 = if at_least { -t1.abs() } else { t1 };

                let t2 = if self.cur.command == Command::And {
                    self.get_x_next();
                    let at_least2 = self.cur.command == Command::AtLeast;
                    if at_least2 {
                        self.get_x_next();
                    }
                    self.scan_primary()?;
                    let t = value_to_scalar(&self.take_cur_exp())?;
                    if at_least2 {
                        -t.abs()
                    } else {
                        t
                    }
                } else {
                    t1
                };

                if let Some(last) = knots.last_mut() {
                    last.right_tension = t1;
                }
                Ok(Some(PendingJoin::Tension(t2)))
            }
            Command::Controls => {
                self.get_x_next();
                self.scan_primary()?;
                let cp1 = self.take_cur_exp();
                let (x1, y1) = value_to_pair(&cp1)?;

                let (x2, y2) = if self.cur.command == Command::And {
                    self.get_x_next();
                    self.scan_primary()?;
                    let cp2 = self.take_cur_exp();
                    value_to_pair(&cp2)?
                } else {
                    (x1, y1)
                };

                if let Some(last) = knots.last_mut() {
                    last.right = KnotDirection::Explicit(Point::new(x1, y1));
                }
                Ok(Some(PendingJoin::Control(Point::new(x2, y2))))
            }
            _ => Ok(None), // No special join options
        }
    }

    /// Convert a value to a path knot.
    fn value_to_knot(&self, val: &Value) -> InterpResult<Knot> {
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
            self.scan_primary()?;
            let curl_val = value_to_scalar(&self.cur_exp)?;
            if self.cur.command == Command::RightBrace {
                self.get_x_next();
            }
            Ok(KnotDirection::Curl(curl_val))
        } else {
            // {<expression>} — direction as pair or angle
            self.scan_expression()?;
            let dir = self.take_cur_exp();
            if self.cur.command == Command::RightBrace {
                self.get_x_next();
            }
            self.value_to_direction(&dir)
        }
    }

    /// Convert a value to a direction for path construction.
    fn value_to_direction(&self, val: &Value) -> InterpResult<KnotDirection> {
        match val {
            Value::Pair(x, y) => Ok(KnotDirection::Given(math::angle(*x, *y).to_radians())),
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

    #[test]
    fn direction_numeric_is_degrees_in_input() {
        let interp = Interpreter::new();
        let dir = interp
            .value_to_direction(&Value::Numeric(90.0))
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
        let interp = Interpreter::new();
        let dir = interp
            .value_to_direction(&Value::Pair(0.0, 1.0))
            .expect("pair direction should parse");

        match dir {
            KnotDirection::Given(angle) => {
                assert!((angle - core::f64::consts::FRAC_PI_2).abs() < 1e-12);
            }
            _ => panic!("expected given direction"),
        }
    }
}
