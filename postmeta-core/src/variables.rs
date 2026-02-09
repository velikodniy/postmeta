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

use crate::equation::{constant_value, dep_substitute, DepList, VarId};
use crate::symbols::SymbolId;
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

    /// Apply a solved linear equation `pivot = dep` and substitute it into all
    /// existing dependent variables.
    pub fn apply_linear_solution(&mut self, pivot: VarId, dep: &DepList) {
        if let Some(v) = constant_value(dep) {
            self.make_known(pivot, v);
        } else {
            self.make_dependent(pivot, dep.clone());
        }

        let mut updates: Vec<(VarId, NumericState)> = Vec::new();
        for i in 0..self.values.len() {
            let id = VarId(i as u32);
            if id == pivot {
                continue;
            }
            if let VarValue::NumericVar(NumericState::Dependent(existing)) = &self.values[i] {
                let new_dep = dep_substitute(existing, pivot, dep);
                if let Some(v) = constant_value(&new_dep) {
                    updates.push((id, NumericState::Known(v)));
                } else {
                    updates.push((id, NumericState::Dependent(new_dep)));
                }
            }
        }

        for (id, state) in updates {
            self.set(id, VarValue::NumericVar(state));
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
// Variable type trie
// ---------------------------------------------------------------------------

/// A node in the variable type trie.
///
/// The trie records the structure of declared variables so the scanner can
/// determine whether a suffix token extends a variable name or starts a new
/// syntactic construct (e.g. a macro call).
///
/// This is a simplified version of `mp.web`'s "suffix tree". It does NOT
/// store values (those stay in the flat [`Variables`] map); it only tracks
/// **what paths are declared** and their types.
#[derive(Debug, Clone, Default)]
struct TrieNode {
    /// The type declared at this node (`Undefined` if no declaration here).
    ty: Type,
    /// Named children (attribute suffixes, keyed by `SymbolId`).
    ///
    /// For `pair laboff.lft`, the root "laboff" node has a child keyed by
    /// the `SymbolId` for "lft" with `ty = PairType`.
    attrs: HashMap<SymbolId, Self>,
    /// Collective subscript child (`[]`).
    ///
    /// If present, any numeric subscript at this level follows this subtree
    /// for type and structure information. For `numeric x[]`, the "x" node
    /// has a `collective` child with `ty = Numeric`.
    collective: Option<Box<Self>>,
}

/// Variable type trie — tracks the structure of declared variables.
///
/// Enables the scanner to answer "is `lft` a suffix of `laboff`?" by
/// checking whether `laboff.lft` exists as a declared path in the trie.
/// This is the Rust equivalent of `mp.web`'s variable tree structure,
/// but only for type/structure info (values stay in [`Variables`]).
///
/// # Usage
///
/// 1. **Type declarations** (`pair laboff.lft;`) register paths via
///    [`declare`].
/// 2. **Suffix scanning** uses [`has_suffix`] to check whether extending
///    the current variable name is valid.
/// 3. **Collective subscripts** (`numeric x[];`) register via `declare`
///    with `None` suffix segments for `[]`.
#[derive(Debug, Clone, Default)]
pub struct VarTrie {
    /// Root nodes keyed by the root variable's `SymbolId`.
    roots: HashMap<SymbolId, TrieNode>,
}

/// One segment of a variable suffix path.
#[derive(Debug, Clone)]
pub enum SuffixSegment {
    /// A named attribute (e.g. `.lft`, `.x`, `.r`).
    Attr(SymbolId),
    /// A collective subscript (`[]`).
    Subscript,
}

impl VarTrie {
    /// Create an empty trie.
    #[must_use]
    pub fn new() -> Self {
        Self {
            roots: HashMap::new(),
        }
    }

    /// Declare a variable path with the given type.
    ///
    /// `root` is the `SymbolId` of the root token (e.g. "laboff").
    /// `suffixes` is the path of suffix segments (e.g. `[Attr("lft")]`).
    /// `ty` is the declared type (e.g. `PairType`).
    ///
    /// This creates all intermediate nodes as needed and sets the type
    /// on the leaf node.
    pub fn declare(&mut self, root: SymbolId, suffixes: &[SuffixSegment], ty: Type) {
        let node = self.roots.entry(root).or_default();
        let leaf = Self::walk_or_create(node, suffixes);
        leaf.ty = ty;
    }

    /// Check whether extending a variable rooted at `root` with the given
    /// `suffix_id` (a named attribute) would match a declared path.
    ///
    /// Returns `true` if the trie has a child for `suffix_id` at the
    /// position described by `path_so_far` (the suffix segments already
    /// consumed). This is used by the suffix scanner to decide whether
    /// to collect a token as part of the variable name.
    #[must_use]
    pub fn has_suffix(
        &self,
        root: SymbolId,
        path_so_far: &[SuffixSegment],
        suffix_id: SymbolId,
    ) -> bool {
        let Some(node) = self.roots.get(&root) else {
            return false;
        };
        let Some(current) = Self::walk(node, path_so_far) else {
            return false;
        };
        current.attrs.contains_key(&suffix_id)
    }

    /// Check whether a root variable has any structure in the trie.
    #[must_use]
    pub fn has_root(&self, root: SymbolId) -> bool {
        self.roots.contains_key(&root)
    }

    /// Get the type at a given path, or `None` if the path doesn't exist.
    #[must_use]
    pub fn get_type(&self, root: SymbolId, suffixes: &[SuffixSegment]) -> Option<Type> {
        let node = self.roots.get(&root)?;
        if suffixes.is_empty() {
            return Some(node.ty);
        }
        let leaf = Self::walk(node, suffixes)?;
        Some(leaf.ty)
    }

    /// Walk a path in the trie, returning the node at the end.
    fn walk<'a>(node: &'a TrieNode, segments: &[SuffixSegment]) -> Option<&'a TrieNode> {
        let mut current = node;
        for seg in segments {
            match seg {
                SuffixSegment::Attr(id) => {
                    current = current.attrs.get(id)?;
                }
                SuffixSegment::Subscript => {
                    current = current.collective.as_deref()?;
                }
            }
        }
        Some(current)
    }

    /// Walk or create a path in the trie, returning a mutable ref to the leaf.
    fn walk_or_create<'a>(node: &'a mut TrieNode, segments: &[SuffixSegment]) -> &'a mut TrieNode {
        let mut current = node;
        for seg in segments {
            match seg {
                SuffixSegment::Attr(id) => {
                    current = current.attrs.entry(*id).or_default();
                }
                SuffixSegment::Subscript => {
                    current = current.collective.get_or_insert_with(Default::default);
                }
            }
        }
        current
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
