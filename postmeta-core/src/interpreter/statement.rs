//! Statement execution.
//!
//! Implements individual statement handlers: type declarations, `addto`,
//! `clip`, `setbounds`, `shipout`, `save`, `interim`, `let`, `delimiters`,
//! `newinternal`, `show`, `message`, and `endgroup`.

use postmeta_graphics::transform::Transformable;
use postmeta_graphics::types::{
    Color, DashPattern, FillObject, GraphicsObject, LineCap, LineJoin, Pen, Picture, StrokeObject,
    Transform,
};

use crate::command::{BoundsOp, Command, MessageOp, ThingToAddOp, TypeNameOp, WithOptionOp};
use crate::error::{ErrorKind, InterpResult};
use crate::internals::InternalId;
use crate::types::{DrawingState, Type, Value};
use crate::variables::{SuffixSegment, VarValue};

use super::Interpreter;
use super::helpers::{value_to_path_owned, value_to_scalar};

enum DoublePathTarget {
    Dot { x: f64, y: f64 },
    Path(postmeta_graphics::path::Path),
}

impl Interpreter {
    pub(super) fn eat_semicolon(&mut self) {
        if self.cur.command == Command::Semicolon {
            self.get_x_next();
        }
    }

    /// Execute a type declaration (`numeric x, y;`).
    #[allow(clippy::unnecessary_wraps)]
    pub(in crate::interpreter) fn do_type_declaration(&mut self) -> InterpResult<()> {
        let Some(type_op) = TypeNameOp::from_modifier(self.cur.modifier) else {
            self.report_error(
                ErrorKind::UnexpectedToken,
                "Invalid type declaration modifier",
            );
            self.get_x_next();
            return Ok(());
        };
        self.get_x_next();

        loop {
            // Expect a variable name (possibly compound with suffixes)
            if let Some(sym_name) = self.cur_symbolic_name() {
                let mut name = sym_name.to_owned();
                let root_sym = self.cur.sym;
                let mut suffix_segs: Vec<SuffixSegment> = Vec::new();

                // Use get_next (non-expanding) to avoid expanding vardef
                // suffixes like `lft` in `pair laboff.lft`.
                self.get_next();

                // Collect suffix tokens (tag tokens, subscripts, and symbols
                // that might be macros but are suffix parts).  The scanner
                // drops `.` separators, so suffix parts appear as consecutive
                // tokens.  We use non-expanding reads to avoid triggering
                // vardef expansion on suffix names.
                loop {
                    if self.cur.command == Command::LeftBracket {
                        // Subscript array suffix `[]`
                        self.get_next();
                        if self.cur.command == Command::RightBracket {
                            suffix_segs.push(SuffixSegment::Subscript);
                            name.push_str("[]");
                            self.get_next();
                        } else {
                            // Not `[]` — push the bracket back and stop
                            self.back_input();
                            break;
                        }
                    } else if self.cur.command == Command::TagToken
                        || self.cur.command == Command::DefinedMacro
                        || self.cur.command == Command::InternalQuantity
                    {
                        // Suffix part (e.g. `l` in `path_.l`, `lft` in `laboff.lft`)
                        if let Some(sym) = self.cur.sym {
                            suffix_segs.push(SuffixSegment::Attr(sym));
                            name.push('.');
                            name.push_str(self.state.symbols.name(sym));
                        }
                        self.get_next();
                    } else {
                        break;
                    }
                }
                // Expand whatever follows the variable name.
                self.expand_current();

                // Clear the variable and all its suffixed descendants so
                // that re-declaring (e.g. `numeric t[]` inside a loop)
                // resets subscripted forms like `t[0]`, `t[1]`, etc.
                if let Some(sym) = root_sym {
                    self.state.variables.invalidate_sym_cache_entry(sym);
                }
                self.state.variables.clear_variable_and_descendants(&name);

                let var_id = self.state.variables.lookup(&name);

                // Determine the MetaPost type for the trie registration
                let mp_type = Self::type_op_to_type(type_op);

                // Set the variable to the correct type
                let val = self
                    .default_var_value_for_type(mp_type, &name)
                    .unwrap_or(VarValue::Undefined);
                self.state.variables.set(var_id, val);

                // Register in the variable type trie
                if let Some(root) = root_sym {
                    self.state.var_trie.declare(root, &suffix_segs, mp_type);
                }
            } else {
                // Non-symbolic token — skip it
                self.get_x_next();
            }

            if self.cur.command == Command::Comma {
                self.get_x_next();
                continue;
            }
            break;
        }

        self.eat_semicolon();
        Ok(())
    }

    /// Convert a `TypeNameOp` modifier to a `Type`.
    const fn type_op_to_type(type_op: TypeNameOp) -> Type {
        match type_op {
            TypeNameOp::Numeric => Type::Numeric,
            TypeNameOp::Boolean => Type::Boolean,
            TypeNameOp::String => Type::String,
            TypeNameOp::Path => Type::Path,
            TypeNameOp::Pen => Type::Pen,
            TypeNameOp::Picture => Type::Picture,
            TypeNameOp::Pair => Type::PairType,
            TypeNameOp::Color => Type::ColorType,
            TypeNameOp::Transform => Type::TransformType,
        }
    }

    /// Execute `addto` statement.
    #[allow(clippy::too_many_lines)]
    pub(in crate::interpreter) fn do_addto(&mut self) -> InterpResult<()> {
        self.get_x_next();

        // Optional target picture name. If omitted, default to currentpicture.
        let pic_name = if self.cur.command == Command::TagToken {
            self.scan_target_picture_name()
                .unwrap_or_else(|| "currentpicture".to_owned())
        } else {
            "currentpicture".to_owned()
        };

        // Expect contour / doublepath / also
        let thing = ThingToAddOp::from_modifier(self.cur.modifier);
        self.get_x_next();

        // Parse expressions and options first, then apply to the target picture.
        match thing {
            Some(ThingToAddOp::Contour) => {
                let path_val = self.scan_expression()?.exp;
                let path = value_to_path_owned(path_val)?;
                let (ds, pen_specified) = self.scan_with_options()?;

                self.state.picture_manager.with_target_picture(
                    &mut self.state.variables,
                    &pic_name,
                    |target| {
                        target.add_fill(FillObject {
                            path,
                            color: ds.color,
                            pen: if pen_specified { Some(ds.pen) } else { None },
                            line_join: ds.line_join,
                            miter_limit: ds.miter_limit,
                        });
                    },
                );
            }
            Some(ThingToAddOp::DoublePath) => {
                let path_val = self.scan_expression()?.exp;
                let (ds, _) = self.scan_with_options()?;

                let target_path = match path_val {
                    Value::Pair(x, y) => DoublePathTarget::Dot { x, y },
                    other => DoublePathTarget::Path(value_to_path_owned(other)?),
                };

                self.state.picture_manager.with_target_picture(
                    &mut self.state.variables,
                    &pic_name,
                    |target| match target_path {
                        DoublePathTarget::Dot { x, y } => {
                            // `draw <pair> withpen <pen>` draws a dot-like mark.
                            // Emulate this via the pen outline path shifted to the
                            // pair position, then filled.
                            let dot = postmeta_graphics::pen::makepath(&ds.pen);
                            let shifted = dot.transformed(&Transform::shifted(x, y));
                            target.add_fill(FillObject {
                                path: shifted,
                                color: ds.color,
                                pen: None,
                                line_join: ds.line_join,
                                miter_limit: ds.miter_limit,
                            });
                        }
                        DoublePathTarget::Path(path) => {
                            target.add_stroke(StrokeObject {
                                path,
                                pen: ds.pen,
                                color: ds.color,
                                dash: ds.dash,
                                line_cap: ds.line_cap,
                                line_join: ds.line_join,
                                miter_limit: ds.miter_limit,
                            });
                        }
                    },
                );
            }
            Some(ThingToAddOp::Also) => {
                let pic_val = self.scan_expression()?.exp;
                if let Value::Picture(p) = pic_val {
                    self.state.picture_manager.with_target_picture(
                        &mut self.state.variables,
                        &pic_name,
                        |target| target.merge(p),
                    );
                } else {
                    self.report_error(
                        ErrorKind::TypeError,
                        "`addto ... also` requires a picture expression",
                    );
                }
            }
            _ => {
                self.report_error(
                    ErrorKind::MissingToken,
                    "Expected `contour`, `doublepath`, or `also`",
                );
            }
        }

        self.eat_semicolon();
        Ok(())
    }

    /// Scan `withpen`, `withcolor`, `dashed` options.
    fn scan_with_options(&mut self) -> InterpResult<(DrawingState, bool)> {
        let mut ds = DrawingState {
            pen: Pen::default(),
            color: Color::BLACK,
            dash: None,
            line_cap: LineCap::from(self.state.internals.get_id(InternalId::LineCap)),
            line_join: LineJoin::from(self.state.internals.get_id(InternalId::LineJoin)),
            miter_limit: self.state.internals.get_id(InternalId::MiterLimit),
        };
        let mut pen_specified = false;

        while self.cur.command == Command::WithOption {
            let opt = WithOptionOp::from_modifier(self.cur.modifier);
            self.get_x_next();
            let val = self.scan_expression()?.exp;

            match opt {
                Some(WithOptionOp::WithPen) => {
                    if let Value::Pen(p) = val {
                        ds.pen = p;
                        pen_specified = true;
                    }
                }
                Some(WithOptionOp::WithColor) => {
                    if let Value::Color(c) = val {
                        ds.color = c;
                    } else if let Value::Numeric(v) = val {
                        ds.color = Color::new(v, v, v);
                    }
                }
                Some(WithOptionOp::Dashed) => {
                    if let Value::Picture(ref pic) = val {
                        ds.dash = extract_dash_pattern(pic);
                    }
                }
                _ => {}
            }
        }

        Ok((ds, pen_specified))
    }

    /// Execute `clip`/`setbounds` statement.
    pub(in crate::interpreter) fn do_bounds(&mut self) -> InterpResult<()> {
        let is_clip = BoundsOp::from_modifier(self.cur.modifier) == Some(BoundsOp::Clip);
        self.get_x_next();

        // Optional picture name before `to`. If omitted, target currentpicture.
        let pic_name = if self.cur.command == Command::TagToken {
            self.scan_target_picture_name()
                .unwrap_or_else(|| "currentpicture".to_owned())
        } else {
            "currentpicture".to_owned()
        };

        // Expect "to"
        if self.cur.command == Command::ToToken {
            self.get_x_next();
        } else {
            self.report_error(ErrorKind::MissingToken, "Expected `to` in clip/setbounds");
        }

        let val = self.scan_expression()?.exp;
        let clip_path = value_to_path_owned(val)?;

        self.state.picture_manager.with_target_picture(
            &mut self.state.variables,
            &pic_name,
            |target| {
                if is_clip {
                    target.clip(clip_path);
                } else {
                    target.set_bounds(clip_path);
                }
            },
        );

        self.eat_semicolon();
        Ok(())
    }

    /// Scan a compound picture target name used by `addto` and `clip/setbounds`.
    ///
    /// This accepts symbolic suffix chains like `pic.layer.sub` and keeps
    /// suffix names from expanding while they are being collected.
    fn scan_target_picture_name(&mut self) -> Option<String> {
        let mut name = self.cur_symbolic_name()?.to_owned();

        // Use non-expanding reads so vardef suffix names are treated as suffix
        // tokens here, mirroring type-declaration parsing behavior.
        self.get_next();
        while self.cur.command == Command::TagToken
            || self.cur.command == Command::DefinedMacro
            || self.cur.command == Command::InternalQuantity
        {
            if let Some(s) = self.cur_symbolic_name() {
                name.push('.');
                name.push_str(s);
            }
            self.get_next();
        }

        // Re-expand whatever token follows the target name so statement parsing
        // continues in normal expanded mode.
        self.expand_current();
        Some(name)
    }

    /// Execute `shipout` statement.
    pub(in crate::interpreter) fn do_shipout(&mut self) -> InterpResult<()> {
        self.state
            .picture_manager
            .sync_currentpicture_variable(&mut self.state.variables);
        self.get_x_next();
        let val = self.scan_expression()?.exp;

        let pic = match val {
            Value::Picture(p) => p,
            Value::Vacuous => self.state.picture_manager.clone_current_picture(),
            other => {
                self.report_error(
                    ErrorKind::TypeError,
                    format!("shipout requires a picture, got {}", other.ty()),
                );
                self.eat_semicolon();
                return Ok(());
            }
        };

        self.state.picture_manager.push_output(pic);

        self.eat_semicolon();
        Ok(())
    }

    /// Execute `outer` statement (no-op — skip the token list).
    ///
    /// In `MetaPost`, `outer` marks tokens so they cannot appear inside
    /// macro definitions.  We parse the comma-separated token list but
    /// do not enforce the restriction.
    ///
    /// Syntax: `outer <token> [, <token>]* ;`
    #[allow(clippy::unnecessary_wraps)]
    pub(in crate::interpreter) fn do_outer(&mut self) -> InterpResult<()> {
        // Read token names separated by commas until semicolon.
        // Use get_next (non-expanding) to avoid triggering `end`/`bye`.
        loop {
            self.get_next(); // read a token name (skip it)
            self.get_next(); // read separator (comma or semicolon)
            if self.cur.command != Command::Comma {
                break;
            }
        }
        self.eat_semicolon();
        Ok(())
    }

    /// Execute `save` statement.
    #[allow(clippy::unnecessary_wraps)]
    pub(in crate::interpreter) fn do_save(&mut self) -> InterpResult<()> {
        self.get_x_next();
        loop {
            if let Some(sym_id) = self.cur.sym {
                self.state.scope_manager.save_name(
                    sym_id,
                    &mut self.state.symbols,
                    &mut self.state.variables,
                    &mut self.state.picture_manager,
                    &mut self.state.macros,
                );
            }
            self.get_x_next();
            if self.cur.command != Command::Comma {
                break;
            }
            self.get_x_next();
        }
        self.eat_semicolon();
        Ok(())
    }

    /// Execute `interim` statement.
    pub(in crate::interpreter) fn do_interim(&mut self) -> InterpResult<()> {
        self.get_x_next();
        if self.cur.command != Command::InternalQuantity {
            self.report_error(
                ErrorKind::MissingToken,
                "Expected internal quantity after `interim`",
            );
            while self.cur.command != Command::Semicolon
                && self.cur.command != Command::Stop
                && self.cur.command != Command::EndGroup
            {
                self.get_x_next();
            }
            self.eat_semicolon();
            return Ok(());
        }

        let idx = self.cur.modifier;
        let prev = self.state.internals.get(idx);
        self.state.scope_manager.save_internal(idx, prev);
        self.get_x_next();

        if self.cur.command != Command::Assignment {
            self.report_error(
                ErrorKind::MissingToken,
                "Expected `:=` in interim statement",
            );
            while self.cur.command != Command::Semicolon
                && self.cur.command != Command::Stop
                && self.cur.command != Command::EndGroup
            {
                self.get_x_next();
            }
            self.eat_semicolon();
            return Ok(());
        }

        self.get_x_next();
        let val = value_to_scalar(&self.scan_expression()?.exp)?;
        self.state.internals.set(idx, val);

        self.eat_semicolon();
        Ok(())
    }

    /// Execute `let` statement.
    #[allow(clippy::unnecessary_wraps)]
    pub(in crate::interpreter) fn do_let(&mut self) -> InterpResult<()> {
        // LHS: get_symbol (non-expanding), like mp.web's do_let
        self.get_next();
        let lhs = self.cur.sym;
        self.get_x_next();
        if self.cur.command != Command::Equals && self.cur.command != Command::Assignment {
            self.report_error(
                ErrorKind::MissingToken,
                "Expected `=` or `:=` in let statement",
            );
            while self.cur.command != Command::Semicolon
                && self.cur.command != Command::Stop
                && self.cur.command != Command::EndGroup
            {
                self.get_x_next();
            }
            return Ok(());
        }

        // RHS: get_symbol (non-expanding) — must not expand macros
        self.get_next();
        let rhs = self.cur.sym;
        if let (Some(l), Some(r)) = (lhs, rhs) {
            let entry = self.state.symbols.get(r);
            self.state.symbols.set(l, entry);
            // Rebind macro metadata: clear stale LHS, then copy RHS if macro.
            self.state.macros.rebind(l, r);
        } else {
            self.report_error(
                ErrorKind::UnexpectedToken,
                "Expected symbolic right-hand side in let statement",
            );
        }
        self.get_x_next();
        Ok(())
    }

    /// Execute `delimiters` statement.
    ///
    /// Syntax: `delimiters <left> <right>;`
    /// Declares a pair of matching delimiters (like `(` and `)`).
    /// Each pair gets a unique modifier so the parser can match them.
    #[allow(clippy::unnecessary_wraps)]
    pub(in crate::interpreter) fn do_delimiters(&mut self) -> InterpResult<()> {
        self.get_x_next();

        // Get left delimiter symbol
        let left_sym = self.cur.sym;
        self.get_x_next();

        // Get right delimiter symbol
        let right_sym = self.cur.sym;
        self.get_x_next();

        // Allocate a unique delimiter id for this pair
        let delim_id = self.state.next_delimiter_id;
        self.state.next_delimiter_id += 1;

        // Set the symbols as delimiter commands with matching modifier
        if let Some(l) = left_sym {
            self.state.symbols.set(
                l,
                crate::symbols::SymbolEntry {
                    command: Command::LeftDelimiter,
                    modifier: delim_id,
                },
            );
        }
        if let Some(r) = right_sym {
            self.state.symbols.set(
                r,
                crate::symbols::SymbolEntry {
                    command: Command::RightDelimiter,
                    modifier: delim_id,
                },
            );
        }

        self.eat_semicolon();
        Ok(())
    }

    /// Execute `newinternal` statement.
    ///
    /// Syntax: `newinternal <name>, <name>, ...;`
    /// Declares new internal numeric quantities.
    #[allow(clippy::unnecessary_wraps)]
    pub(in crate::interpreter) fn do_new_internal(&mut self) -> InterpResult<()> {
        self.get_x_next();

        loop {
            if let Some(name) = self.cur_symbolic_name().map(str::to_owned) {
                // Register the new internal
                let Some(idx) = self.state.internals.new_internal(&name) else {
                    self.report_error(
                        ErrorKind::Overflow,
                        format!("Too many internal quantities while adding `{name}`"),
                    );
                    break;
                };

                // Set the symbol to InternalQuantity
                if let Some(sym) = self.cur.sym {
                    self.state.symbols.set(
                        sym,
                        crate::symbols::SymbolEntry {
                            command: Command::InternalQuantity,
                            modifier: idx,
                        },
                    );
                }
            }
            self.get_x_next();

            if self.cur.command == Command::Comma {
                self.get_x_next();
                continue;
            }
            break;
        }

        self.eat_semicolon();
        Ok(())
    }

    /// Execute `show` statement.
    pub(in crate::interpreter) fn do_show(&mut self) -> InterpResult<()> {
        // show_type distinguishes show/showtoken/showdependencies — used later
        let _ = self.cur.modifier;
        self.get_x_next();
        // Print the value
        let val = self.scan_expression()?.exp;
        self.report_info(format!(">> {val}"));
        self.eat_semicolon();
        Ok(())
    }

    /// Execute `message` / `errmessage` statement.
    pub(in crate::interpreter) fn do_message(&mut self) -> InterpResult<()> {
        let is_err = MessageOp::from_modifier(self.cur.modifier) == Some(MessageOp::ErrMessage);
        self.get_x_next();
        let val = self.scan_expression()?.exp;
        let msg = match &val {
            Value::String(s) => s.to_string(),
            other => format!("{other}"),
        };
        if is_err {
            self.report_error(ErrorKind::Internal, msg);
        } else {
            self.report_info(msg);
        }
        self.eat_semicolon();
        Ok(())
    }

    /// Execute mode-setting commands (`batchmode`, `nonstopmode`, etc.).
    #[allow(clippy::unnecessary_wraps)]
    pub(in crate::interpreter) fn do_mode_command(&mut self) -> InterpResult<()> {
        // Mode commands affect terminal interaction in original MetaPost.
        // PostMeta runs non-interactively, so these are accepted as no-ops.
        self.get_x_next();
        self.eat_semicolon();
        Ok(())
    }

    /// Execute `randomseed` statement.
    pub(in crate::interpreter) fn do_randomseed(&mut self) -> InterpResult<()> {
        self.get_x_next();
        if self.cur.command != Command::Assignment {
            self.report_error(ErrorKind::MissingToken, "Expected `:=` after `randomseed`");
            while self.cur.command != Command::Semicolon
                && self.cur.command != Command::Stop
                && self.cur.command != Command::EndGroup
            {
                self.get_x_next();
            }
            self.eat_semicolon();
            return Ok(());
        }

        self.get_x_next();
        let seed_val = value_to_scalar(&self.scan_expression()?.exp)?;
        if seed_val.is_finite() {
            #[expect(
                clippy::cast_sign_loss,
                reason = "negative seeds clamp to zero before conversion"
            )]
            #[expect(
                clippy::cast_possible_truncation,
                reason = "seed is an implementation-defined integer state"
            )]
            {
                self.state.random_seed = seed_val.round().max(0.0) as u64;
            }
        } else {
            self.report_error(
                ErrorKind::TypeError,
                "randomseed must be a finite numeric value",
            );
        }

        self.eat_semicolon();
        Ok(())
    }

    #[allow(clippy::unnecessary_wraps)]
    pub(in crate::interpreter) fn do_special(&mut self) -> InterpResult<()> {
        // PostScript specials are ignored by the SVG backend.
        self.get_x_next();

        // Parse and discard the payload expression if present.
        if self.cur.command != Command::Semicolon
            && self.cur.command != Command::Stop
            && self.cur.command != Command::EndGroup
        {
            self.lhs_tracking.equals_means_equation = false;
            if let Err(err) = self.scan_expression() {
                self.state.errors.push(err);
                while self.cur.command != Command::Semicolon
                    && self.cur.command != Command::Stop
                    && self.cur.command != Command::EndGroup
                {
                    self.get_x_next();
                }
            }
        }

        self.eat_semicolon();
        Ok(())
    }

    #[allow(clippy::unnecessary_wraps)]
    pub(in crate::interpreter) fn do_unimplemented_statement(
        &mut self,
        name: &str,
    ) -> InterpResult<()> {
        self.report_error(
            ErrorKind::InvalidExpression,
            format!("`{name}` is not implemented"),
        );
        self.get_x_next();
        while self.cur.command != Command::Semicolon
            && self.cur.command != Command::Stop
            && self.cur.command != Command::EndGroup
        {
            self.get_x_next();
        }
        self.eat_semicolon();
        Ok(())
    }

    /// Restore scope at `endgroup`.
    pub(super) fn do_endgroup(&mut self) {
        self.state.scope_manager.end_group(
            &mut self.state.symbols,
            &mut self.state.variables,
            &mut self.state.internals,
            &mut self.state.macros,
        );
    }
}

// ---------------------------------------------------------------------------
// Dash pattern extraction
// ---------------------------------------------------------------------------

/// Extract a [`DashPattern`] from a dash-pattern picture.
///
/// In `MetaPost`, `dashpattern(on a off b on c off d ...)` produces a
/// picture where each `_on_` segment is encoded as a horizontal stroke.
/// The x-range of each stroke gives the on-segment, and the y-coordinate
/// of every stroke equals the total pattern length (because each `_on_`
/// and `_off_` operation shifts the entire picture upward by its distance).
///
/// Returns `None` if the picture contains no strokes.
fn extract_dash_pattern(pic: &Picture) -> Option<DashPattern> {
    // Collect (xmin, xmax) of each stroke and the y-coordinate (total length).
    let mut on_segments: Vec<(f64, f64)> = Vec::new();
    let mut total_length: f64 = 0.0;

    for obj in &pic.objects {
        if let GraphicsObject::Stroke(stroke) = obj {
            let knots = &stroke.path.knots;
            if knots.is_empty() {
                continue;
            }
            // The x-range of this stroke path gives the on-segment.
            let mut xmin = f64::INFINITY;
            let mut xmax = f64::NEG_INFINITY;
            for k in knots {
                xmin = xmin.min(k.point.x);
                xmax = xmax.max(k.point.x);
            }
            // The y-coordinate is the total pattern length.
            total_length = total_length.max(knots[0].point.y);

            on_segments.push((xmin, xmax));
        }
    }

    if on_segments.is_empty() {
        return None;
    }

    // Sort by starting x position.
    on_segments.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal));

    // Build alternating on/off dashes in cyclic order starting from the first
    // on-segment. A leading gap is represented via dash offset.
    let first_start = on_segments[0].0;
    let mut dashes: Vec<f64> = Vec::with_capacity(on_segments.len() * 2);

    for (idx, (xmin, xmax)) in on_segments.iter().enumerate() {
        let on_len = (xmax - xmin).max(0.0);
        dashes.push(on_len);

        let next_start = if let Some((nx, _)) = on_segments.get(idx + 1) {
            *nx
        } else {
            total_length + first_start
        };
        let off_len = (next_start - xmax).max(0.0);
        dashes.push(off_len);
    }

    let offset = if first_start.abs() < 1e-6 {
        0.0
    } else {
        first_start
    };

    Some(DashPattern { dashes, offset })
}
