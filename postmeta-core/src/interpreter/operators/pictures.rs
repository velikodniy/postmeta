//! Picture inspection: part extraction, corners, and type predicates.

use std::sync::Arc;

use postmeta_graphics::bbox::{BoundingBox, Corners};
use postmeta_graphics::path::BezierPath;
use postmeta_graphics::transform::Transformable;
use postmeta_graphics::types::{GraphicsObject, Pen, Picture, Point};

use crate::command::UnaryOp;
use crate::error::{ErrorKind, InterpResult, InterpreterError};
use crate::interpreter::helpers::value_to_picture;
use crate::interpreter::{ExprResultValue, Interpreter, LhsBinding};
use crate::types::{Type, Value};
use crate::variables::VarValue;

impl Interpreter {
    /// Extract a part from a pair or transform.
    ///
    /// When the operand has a pair dependency list (i.e. the pair variable
    /// is not fully known), the extracted component's dependency is
    /// propagated to the returned result's `dep` and to
    /// `last_lhs_binding` so that it can participate in linear equation
    /// solving (e.g. `xpart A = 0`).
    ///
    /// For transform variables, `operand_binding` carries the variable
    /// binding from before the unary operator cleared it, allowing us to
    /// look up the sub-part `VarId` for equation solving (e.g.
    /// `xxpart T = 1`).
    #[allow(clippy::too_many_lines)]
    pub(super) fn extract_part(
        &mut self,
        input: &Value,
        part: usize,
        pair_dep: Option<(crate::equation::DepList, crate::equation::DepList)>,
        operand_binding: Option<&LhsBinding>,
    ) -> InterpResult<ExprResultValue> {
        match input {
            Value::Pair(x, y) => {
                let v = match part {
                    0 => *x,
                    1 => *y,
                    _ => {
                        return Err(InterpreterError::new(
                            ErrorKind::TypeError,
                            "Pair only has xpart and ypart",
                        ));
                    }
                };
                // Propagate the component's dependency so equations work.
                if let Some((dx, dy)) = pair_dep {
                    let dep = if part == 0 { dx } else { dy };
                    if crate::equation::is_constant(&dep) {
                        // Fully known component — no dependency to track.
                        Ok(ExprResultValue {
                            exp: Value::Numeric(v),
                            ty: Type::Known,
                            dep: Some(dep),
                            pair_dep: None,
                        })
                    } else {
                        // Extract the primary VarId from the dep for LHS binding.
                        let primary_var = dep.iter().find_map(|t| t.var_id);
                        if let Some(vid) = primary_var {
                            self.lhs_tracking.last_lhs_binding = Some(LhsBinding::Variable {
                                id: vid,
                                negated: false,
                            });
                        }
                        Ok(ExprResultValue {
                            exp: Value::Numeric(v),
                            ty: Type::Dependent,
                            dep: Some(dep),
                            pair_dep: None,
                        })
                    }
                } else {
                    Ok(ExprResultValue::numeric_known(v))
                }
            }
            Value::Transform(t) => {
                let v = match part {
                    0 => t.tx,
                    1 => t.ty,
                    2 => t.txx,
                    3 => t.txy,
                    4 => t.tyx,
                    5 => t.tyy,
                    _ => {
                        return Err(InterpreterError::new(
                            ErrorKind::TypeError,
                            "Invalid transform part",
                        ));
                    }
                };
                // If the operand was a transform variable, look up the
                // sub-part VarId so the result can participate in equation
                // solving (e.g. `xxpart T = 1`).
                if let Some(LhsBinding::Variable { id, .. }) = operand_binding {
                    if let VarValue::Transform {
                        tx,
                        ty,
                        txx,
                        txy,
                        tyx,
                        tyy,
                    } = self.state.variables.get(*id).clone()
                    {
                        let sub_id = match part {
                            0 => tx,
                            1 => ty,
                            2 => txx,
                            3 => txy,
                            4 => tyx,
                            5 => tyy,
                            _ => unreachable!(),
                        };
                        let dep = self.numeric_dep_for_var(sub_id);
                        if crate::equation::is_constant(&dep) {
                            return Ok(ExprResultValue {
                                exp: Value::Numeric(v),
                                ty: Type::Known,
                                dep: Some(dep),
                                pair_dep: None,
                            });
                        }
                        let primary_var = dep.iter().find_map(|t| t.var_id);
                        if let Some(vid) = primary_var {
                            self.lhs_tracking.last_lhs_binding = Some(LhsBinding::Variable {
                                id: vid,
                                negated: false,
                            });
                        }
                        return Ok(ExprResultValue {
                            exp: Value::Numeric(crate::equation::constant_value(&dep).unwrap_or(v)),
                            ty: Type::Dependent,
                            dep: Some(dep),
                            pair_dep: None,
                        });
                    }
                }
                Ok(ExprResultValue::numeric_known(v))
            }
            Value::Picture(pic) => {
                // For pictures, extract the transform part of the first text object.
                // Non-text objects return 0 (matching MetaPost behavior).
                let v = match pic.first() {
                    Some(GraphicsObject::Text(t)) => match part {
                        0 => t.transform.tx,
                        1 => t.transform.ty,
                        2 => t.transform.txx,
                        3 => t.transform.txy,
                        4 => t.transform.tyx,
                        5 => t.transform.tyy,
                        _ => 0.0,
                    },
                    _ => 0.0,
                };
                Ok(ExprResultValue::numeric_known(v))
            }
            _ => Err(InterpreterError::new(
                ErrorKind::TypeError,
                format!("{} has no xpart/ypart", input.ty()),
            )),
        }
    }

    /// Extract a color part, returning `(Value::Numeric, Type::Known)`.
    pub(super) fn extract_color_part(val: &Value, part: usize) -> InterpResult<(Value, Type)> {
        match val {
            Value::Color(c) => {
                let v = match part {
                    0 => c.r,
                    1 => c.g,
                    2 => c.b,
                    _ => {
                        return Err(InterpreterError::new(
                            ErrorKind::TypeError,
                            "Invalid color part",
                        ));
                    }
                };
                Ok((Value::Numeric(v), Type::Known))
            }
            Value::Picture(pic) => {
                // Extract color from the first graphical object that has color.
                let color = match pic.first() {
                    Some(GraphicsObject::Fill(f)) => Some(&f.color),
                    Some(GraphicsObject::Stroke(s)) => Some(&s.color),
                    Some(GraphicsObject::Text(t)) => Some(&t.color),
                    _ => None,
                };
                let v = color.map_or(0.0, |c| match part {
                    0 => c.r,
                    1 => c.g,
                    2 => c.b,
                    _ => 0.0,
                });
                Ok((Value::Numeric(v), Type::Known))
            }
            _ => Err(InterpreterError::new(
                ErrorKind::TypeError,
                format!("{} has no color parts", val.ty()),
            )),
        }
    }

    /// Return the color model of a picture component or color value.
    ///
    /// Returns 1 (no color), 3 (greyscale), 5 (RGB), or 7 (CMYK).
    /// Since we only support RGB, fills/strokes return 5 and text
    /// defaults to 5 as well. Objects without explicit color return 1.
    #[allow(clippy::unnecessary_wraps)]
    pub(super) fn extract_color_model(val: &Value) -> InterpResult<(Value, Type)> {
        let model = match val {
            Value::Color(_) => 5.0,
            Value::Picture(pic) => match pic.first() {
                Some(
                    GraphicsObject::Fill(_) | GraphicsObject::Stroke(_) | GraphicsObject::Text(_),
                ) => 5.0,
                _ => 1.0,
            },
            _ => 1.0,
        };
        Ok((Value::Numeric(model), Type::Known))
    }

    /// Return the grey part of a picture component or color value.
    ///
    /// Since we only support RGB, this returns 0 for everything
    /// (greyscale is not a separate color model in our implementation).
    #[allow(clippy::unnecessary_wraps)]
    pub(super) const fn extract_grey_part(val: &Value) -> InterpResult<(Value, Type)> {
        let _ = val;
        Ok((Value::Numeric(0.0), Type::Known))
    }
}

/// Evaluate a corner operator (`llcorner`, `lrcorner`, `ulcorner`, `urcorner`).
pub(super) fn corner(op: UnaryOp, input: &Value, corners: Corners) -> InterpResult<(Value, Type)> {
    let bb = match input {
        Value::Picture(pic) => BoundingBox::of_picture(pic, corners),
        Value::Path(p) => BoundingBox::of_path(p),
        Value::Pen(p) => {
            let mut bb = BoundingBox::EMPTY;
            match p {
                postmeta_graphics::types::Pen::Elliptical(t) => {
                    for pt in [
                        (Point::new(1.0, 0.0)).transformed(t),
                        (Point::new(-1.0, 0.0)).transformed(t),
                        (Point::new(0.0, 1.0)).transformed(t),
                        (Point::new(0.0, -1.0)).transformed(t),
                    ] {
                        bb.include_point(pt);
                    }
                }
                postmeta_graphics::types::Pen::Polygonal(verts) => {
                    for v in verts {
                        bb.include_point(*v);
                    }
                }
            }
            bb
        }
        _ => {
            return Err(InterpreterError::new(
                ErrorKind::TypeError,
                format!(
                    "corner operators require a picture or path, got {}",
                    input.ty()
                ),
            ));
        }
    };
    let (px, py) = match op {
        UnaryOp::LLCorner => (bb.min_x, bb.min_y),
        UnaryOp::LRCorner => (bb.max_x, bb.min_y),
        UnaryOp::ULCorner => (bb.min_x, bb.max_y),
        _ => (bb.max_x, bb.max_y),
    };
    Ok((Value::Pair(px, py), Type::PairType))
}

// Picture part extraction operators.

pub(super) fn text_part(input: &Value) -> InterpResult<(Value, Type)> {
    let pic = value_to_picture(input)?;
    let text = match pic.first() {
        Some(GraphicsObject::Text(t)) => t.text.to_string(),
        _ => String::new(),
    };
    Ok((Value::String(Arc::from(text)), Type::String))
}

pub(super) fn font_part(input: &Value) -> InterpResult<(Value, Type)> {
    let pic = value_to_picture(input)?;
    let font = match pic.first() {
        Some(GraphicsObject::Text(t)) => t.font_name.to_string(),
        _ => String::new(),
    };
    Ok((Value::String(Arc::from(font)), Type::String))
}

pub(super) fn path_part(input: &Value) -> InterpResult<(Value, Type)> {
    let pic = value_to_picture(input)?;
    let path = match pic.first() {
        Some(GraphicsObject::Fill(f)) => f.path.clone(),
        Some(GraphicsObject::Stroke(s)) => s.path.clone(),
        Some(GraphicsObject::Picture(nested)) => nested.clip_path().map_or_else(
            || {
                nested.bounds_path().map_or_else(
                    || Arc::new(BezierPath::from_parts(vec![Point::ZERO], vec![], false)),
                    Clone::clone,
                )
            },
            Clone::clone,
        ),
        _ => {
            // Default: single-knot path at origin
            Arc::new(BezierPath::from_parts(vec![Point::ZERO], vec![], false))
        }
    };
    Ok((Value::Path(path), Type::Path))
}

pub(super) fn pen_part(input: &Value) -> InterpResult<(Value, Type)> {
    let pic = value_to_picture(input)?;
    let pen = match pic.first() {
        Some(GraphicsObject::Fill(f)) => f.pen.clone().unwrap_or(Pen::null()),
        Some(GraphicsObject::Stroke(s)) => s.pen.clone(),
        _ => Pen::null(),
    };
    Ok((Value::Pen(pen), Type::Pen))
}

pub(super) fn dash_part(input: &Value) -> InterpResult<(Value, Type)> {
    let pic = value_to_picture(input)?;
    let dash_pic = match pic.first() {
        Some(GraphicsObject::Stroke(s)) => {
            // TODO: convert DashPattern back to a picture representation.
            // For now return empty picture (matches MetaPost's nullpicture).
            let _ = &s.dash;
            Picture::new()
        }
        _ => Picture::new(),
    };
    Ok((Value::Picture(dash_pic), Type::Picture))
}

// Picture type tests: check first object in the picture.

pub(super) fn is_filled(input: &Value) -> InterpResult<(Value, Type)> {
    let pic = value_to_picture(input)?;
    let result = matches!(pic.first(), Some(GraphicsObject::Fill(_)));
    Ok((Value::Boolean(result), Type::Boolean))
}

pub(super) fn is_stroked(input: &Value) -> InterpResult<(Value, Type)> {
    let pic = value_to_picture(input)?;
    let result = matches!(pic.first(), Some(GraphicsObject::Stroke(_)));
    Ok((Value::Boolean(result), Type::Boolean))
}

pub(super) fn is_textual(input: &Value) -> InterpResult<(Value, Type)> {
    let pic = value_to_picture(input)?;
    let result = matches!(pic.first(), Some(GraphicsObject::Text(_)));
    Ok((Value::Boolean(result), Type::Boolean))
}

pub(super) fn is_clipped(input: &Value) -> InterpResult<(Value, Type)> {
    let pic = value_to_picture(input)?;
    let result = match pic.first() {
        Some(GraphicsObject::Picture(nested)) => nested.clip_path().is_some(),
        _ => false,
    };
    Ok((Value::Boolean(result), Type::Boolean))
}

pub(super) fn is_bounded(input: &Value) -> InterpResult<(Value, Type)> {
    let pic = value_to_picture(input)?;
    let result = match pic.first() {
        Some(GraphicsObject::Picture(nested)) => nested.bounds_path().is_some(),
        _ => false,
    };
    Ok((Value::Boolean(result), Type::Boolean))
}
