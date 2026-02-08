//! Variable storage for the `MetaPost` interpreter.
//!
//! `MetaPost` variables have a suffix-based naming system: `x`, `x1`,
//! `x.r`, `z1r` are all distinct variables. This module provides the
//! storage for variable values and their equation-system state.
//!
//! Each variable is either:
//! - **Undefined**: never mentioned
//! - **Known**: has a definite value
//! - **Independent**: free variable in the equation system
//! - **Dependent**: linear combination of independents
//! - **Compound**: a pair/color/transform with sub-parts

use std::collections::HashMap;

use postmeta_graphics::types::Scalar;

use crate::equation::{DepList, VarId};
use crate::types::{Type, Value};

// ---------------------------------------------------------------------------
// Variable state
// ---------------------------------------------------------------------------

/// The state of a numeric variable in the equation system.
#[derive(Debug, Clone)]
pub enum NumericState {
    /// Undefined (never mentioned).
    Undefined,
    /// Declared numeric but no constraints yet.
    Numeric,
    /// Known scalar value.
    Known(Scalar),
    /// Free variable with serial number.
    Independent { serial: u32 },
    /// Linear combination of independents.
    Dependent(DepList),
}

/// A stored variable value.
#[derive(Debug, Clone)]
pub enum VarValue {
    /// Undefined.
    Undefined,
    /// A fully-known value of any type.
    Known(Value),
    /// A numeric variable in some equation state.
    NumericVar(NumericState),
    /// A pair with two numeric sub-parts.
    Pair { x: VarId, y: VarId },
    /// A color with three numeric sub-parts.
    Color { r: VarId, g: VarId, b: VarId },
    /// A transform with six numeric sub-parts.
    Transform {
        tx: VarId,
        ty: VarId,
        txx: VarId,
        txy: VarId,
        tyx: VarId,
        tyy: VarId,
    },
}

impl VarValue {
    /// Get the `MetaPost` type of this variable.
    #[must_use]
    pub const fn ty(&self) -> Type {
        match self {
            Self::Undefined => Type::Undefined,
            Self::Known(v) => v.ty(),
            Self::NumericVar(state) => match state {
                NumericState::Undefined => Type::Undefined,
                NumericState::Numeric => Type::Numeric,
                NumericState::Known(_) => Type::Known,
                NumericState::Independent { .. } => Type::Independent,
                NumericState::Dependent(_) => Type::Dependent,
            },
            Self::Pair { .. } => Type::PairType,
            Self::Color { .. } => Type::ColorType,
            Self::Transform { .. } => Type::TransformType,
        }
    }
}

// ---------------------------------------------------------------------------
// Variable storage
// ---------------------------------------------------------------------------

/// Storage for all variables.
///
/// Variables are identified by `VarId`. The suffix tree structure from
/// `mp.web` is simplified: we use a flat map from string keys (like
/// `"x"`, `"x1"`, `"x.r"`) to `VarId`s, and a vec of values.
#[derive(Debug)]
pub struct Variables {
    /// `VarId` → variable value.
    values: Vec<VarValue>,
    /// Name → `VarId` mapping for root variables.
    name_to_id: HashMap<String, VarId>,
    /// Next serial number for independent variables.
    next_serial: u32,
}

impl Variables {
    /// Create empty variable storage.
    #[must_use]
    pub fn new() -> Self {
        Self {
            values: Vec::with_capacity(256),
            name_to_id: HashMap::with_capacity(256),
            next_serial: 1,
        }
    }

    /// Allocate a new variable slot and return its id.
    pub fn alloc(&mut self) -> VarId {
        let id = VarId(self.values.len() as u32);
        self.values.push(VarValue::Undefined);
        id
    }

    /// Look up or create a variable by name.
    pub fn lookup(&mut self, name: &str) -> VarId {
        if let Some(&id) = self.name_to_id.get(name) {
            return id;
        }
        let id = self.alloc();
        self.name_to_id.insert(name.to_owned(), id);
        id
    }

    /// Register a name for an existing variable id.
    ///
    /// Used when creating compound type sub-parts (e.g. `p.x`, `p.y` for a pair `p`).
    pub fn register_name(&mut self, name: &str, id: VarId) {
        self.name_to_id.insert(name.to_owned(), id);
    }

    /// Look up a variable by name without creating it.
    #[must_use]
    pub fn lookup_existing(&self, name: &str) -> Option<VarId> {
        self.name_to_id.get(name).copied()
    }

    /// Get a variable's value.
    #[must_use]
    pub fn get(&self, id: VarId) -> &VarValue {
        let idx = id.0 as usize;
        if idx < self.values.len() {
            &self.values[idx]
        } else {
            &VarValue::Undefined
        }
    }

    /// Set a variable's value.
    pub fn set(&mut self, id: VarId, value: VarValue) {
        let idx = id.0 as usize;
        if idx < self.values.len() {
            self.values[idx] = value;
        }
    }

    /// Set a variable to a known value.
    pub fn set_known(&mut self, id: VarId, value: Value) {
        self.set(id, VarValue::Known(value));
    }

    /// Set a variable to a known numeric value.
    pub fn set_numeric(&mut self, id: VarId, value: Scalar) {
        self.set(id, VarValue::NumericVar(NumericState::Known(value)));
    }

    /// Make a variable independent, assigning a new serial number.
    pub fn make_independent(&mut self, id: VarId) -> u32 {
        let serial = self.next_serial;
        self.next_serial += 1;
        self.set(
            id,
            VarValue::NumericVar(NumericState::Independent { serial }),
        );
        serial
    }

    /// Make a variable dependent with the given dependency list.
    pub fn make_dependent(&mut self, id: VarId, dep: DepList) {
        self.set(id, VarValue::NumericVar(NumericState::Dependent(dep)));
    }

    /// Make a variable known with a scalar value.
    pub fn make_known(&mut self, id: VarId, value: Scalar) {
        self.set(id, VarValue::NumericVar(NumericState::Known(value)));
    }

    /// Get the serial number of an independent variable.
    #[must_use]
    pub fn serial(&self, id: VarId) -> Option<u32> {
        match self.get(id) {
            VarValue::NumericVar(NumericState::Independent { serial }) => Some(*serial),
            _ => None,
        }
    }

    /// Get the dependency list of a dependent variable.
    #[must_use]
    pub fn dep_list(&self, id: VarId) -> Option<&DepList> {
        match self.get(id) {
            VarValue::NumericVar(NumericState::Dependent(dep)) => Some(dep),
            _ => None,
        }
    }

    /// Check if a variable is unknown (undefined or declared-but-unconstrained).
    ///
    /// This includes Undefined, `NumericVar(Undefined)`, `NumericVar(Numeric)`,
    /// and compound types whose sub-parts are all unknown.
    #[must_use]
    pub fn is_unknown(&self, id: VarId) -> bool {
        match self.get(id) {
            VarValue::Undefined
            | VarValue::NumericVar(NumericState::Undefined | NumericState::Numeric) => true,
            VarValue::Pair { x, y } => self.is_unknown(*x) && self.is_unknown(*y),
            VarValue::Color { r, g, b } => {
                self.is_unknown(*r) && self.is_unknown(*g) && self.is_unknown(*b)
            }
            VarValue::Transform {
                tx,
                ty,
                txx,
                txy,
                tyx,
                tyy,
            } => [*tx, *ty, *txx, *txy, *tyx, *tyy]
                .iter()
                .all(|id| self.is_unknown(*id)),
            _ => false,
        }
    }

    /// Get a known numeric value.
    #[must_use]
    #[allow(clippy::match_same_arms)]
    pub fn known_value(&self, id: VarId) -> Option<Scalar> {
        match self.get(id) {
            VarValue::NumericVar(NumericState::Known(v)) => Some(*v),
            VarValue::Known(Value::Numeric(v)) => Some(*v),
            _ => None,
        }
    }

    /// Allocate a pair variable with two sub-parts.
    pub fn alloc_pair(&mut self) -> (VarId, VarId, VarId) {
        let x = self.alloc();
        let y = self.alloc();
        let pair = self.alloc();
        self.set(pair, VarValue::Pair { x, y });
        (pair, x, y)
    }

    /// Allocate a color variable with three sub-parts.
    pub fn alloc_color(&mut self) -> (VarId, VarId, VarId, VarId) {
        let r = self.alloc();
        let g = self.alloc();
        let b = self.alloc();
        let color = self.alloc();
        self.set(color, VarValue::Color { r, g, b });
        (color, r, g, b)
    }

    /// Allocate a transform variable with six sub-parts.
    #[allow(clippy::similar_names)]
    pub fn alloc_transform(&mut self) -> (VarId, VarId, VarId, VarId, VarId, VarId, VarId) {
        let tx = self.alloc();
        let ty = self.alloc();
        let txx = self.alloc();
        let txy = self.alloc();
        let tyx = self.alloc();
        let tyy = self.alloc();
        let transform = self.alloc();
        self.set(
            transform,
            VarValue::Transform {
                tx,
                ty,
                txx,
                txy,
                tyx,
                tyy,
            },
        );
        (transform, tx, ty, txx, txy, tyx, tyy)
    }

    /// Total number of allocated variables.
    #[must_use]
    pub fn count(&self) -> usize {
        self.values.len()
    }

    /// Iterate over all variable ids and their values.
    pub fn iter(&self) -> impl Iterator<Item = (VarId, &VarValue)> {
        self.values
            .iter()
            .enumerate()
            .map(|(i, v)| (VarId(i as u32), v))
    }
}

impl Default for Variables {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Save stack for scoping
// ---------------------------------------------------------------------------

/// An entry on the save stack for `begingroup`/`endgroup` scoping.
#[derive(Debug, Clone)]
pub enum SaveEntry {
    /// Group boundary marker.
    Boundary,
    /// Saved variable value.
    Variable { id: VarId, value: VarValue },
    /// Saved internal quantity.
    Internal { index: u16, value: Scalar },
    /// Saved symbol entry.
    Symbol {
        id: crate::symbols::SymbolId,
        entry: crate::symbols::SymbolEntry,
    },
}

/// The save stack for scoping.
#[derive(Debug, Default)]
pub struct SaveStack {
    entries: Vec<SaveEntry>,
}

impl SaveStack {
    /// Create a new save stack.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Push a group boundary.
    pub fn push_boundary(&mut self) {
        self.entries.push(SaveEntry::Boundary);
    }

    /// Save a variable's current value.
    pub fn save_variable(&mut self, id: VarId, value: VarValue) {
        self.entries.push(SaveEntry::Variable { id, value });
    }

    /// Save an internal quantity's current value.
    pub fn save_internal(&mut self, index: u16, value: Scalar) {
        self.entries.push(SaveEntry::Internal { index, value });
    }

    /// Save a symbol entry.
    pub fn save_symbol(
        &mut self,
        id: crate::symbols::SymbolId,
        entry: crate::symbols::SymbolEntry,
    ) {
        self.entries.push(SaveEntry::Symbol { id, entry });
    }

    /// Restore all entries back to the last boundary.
    ///
    /// Returns the list of entries to restore (in reverse order).
    pub fn restore_to_boundary(&mut self) -> Vec<SaveEntry> {
        let mut restored = Vec::new();
        while let Some(entry) = self.entries.pop() {
            if matches!(entry, SaveEntry::Boundary) {
                break;
            }
            restored.push(entry);
        }
        restored
    }

    /// Current depth (number of entries).
    #[must_use]
    pub fn depth(&self) -> usize {
        self.entries.len()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alloc_and_get() {
        let mut vars = Variables::new();
        let id = vars.alloc();
        assert!(matches!(vars.get(id), VarValue::Undefined));
    }

    #[test]
    fn lookup_creates_var() {
        let mut vars = Variables::new();
        let id1 = vars.lookup("x");
        let id2 = vars.lookup("x");
        assert_eq!(id1, id2);
    }

    #[test]
    fn set_known_numeric() {
        let mut vars = Variables::new();
        let id = vars.lookup("x");
        vars.set_numeric(id, 42.0);
        assert!((vars.known_value(id).unwrap() - 42.0).abs() < f64::EPSILON);
    }

    #[test]
    fn independent_serial() {
        let mut vars = Variables::new();
        let id = vars.lookup("x");
        let s = vars.make_independent(id);
        assert_eq!(vars.serial(id), Some(s));
    }

    #[test]
    fn pair_allocation() {
        let mut vars = Variables::new();
        let (pair_id, x_id, y_id) = vars.alloc_pair();
        assert!(matches!(vars.get(pair_id), VarValue::Pair { .. }));
        assert!(matches!(vars.get(x_id), VarValue::Undefined));
        assert!(matches!(vars.get(y_id), VarValue::Undefined));
    }

    #[test]
    fn save_stack_boundary() {
        let mut stack = SaveStack::new();
        stack.push_boundary();
        stack.save_internal(1, 5.0);
        stack.save_internal(2, 10.0);

        let restored = stack.restore_to_boundary();
        assert_eq!(restored.len(), 2);
        assert_eq!(stack.depth(), 0);
    }

    #[test]
    fn save_stack_nested() {
        let mut stack = SaveStack::new();
        stack.push_boundary();
        stack.save_internal(1, 5.0);
        stack.push_boundary();
        stack.save_internal(2, 10.0);

        // Inner group
        let restored = stack.restore_to_boundary();
        assert_eq!(restored.len(), 1); // only the inner save

        // Outer group
        let restored = stack.restore_to_boundary();
        assert_eq!(restored.len(), 1); // the outer save
    }
}
