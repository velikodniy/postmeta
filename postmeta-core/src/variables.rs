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

use std::collections::{HashMap, HashSet};

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
    /// Reverse dependency index: independent `VarId` → set of dependent `VarId`s
    /// that reference it. Maintained by `set()` so `apply_linear_solution` can
    /// find affected dependents in O(k) instead of scanning all variables.
    dep_index: HashMap<VarId, HashSet<VarId>>,
    /// Root name → set of all full names (root + suffixes) in `name_to_id`.
    /// Enables O(k) lookup for `take_name_bindings_for_root` and
    /// `clear_name_bindings_for_root` instead of scanning all names.
    names_by_root: HashMap<String, HashSet<String>>,
}

impl Variables {
    /// Create empty variable storage.
    #[must_use]
    pub fn new() -> Self {
        Self {
            values: Vec::with_capacity(256),
            name_to_id: HashMap::with_capacity(256),
            next_serial: 1,
            dep_index: HashMap::new(),
            names_by_root: HashMap::new(),
        }
    }

    /// Extract the root portion of a variable name (before the first `.` or `[`).
    fn root_of(name: &str) -> &str {
        name.find(['.', '[']).map_or(name, |i| &name[..i])
    }

    /// Record a name in the root index.
    fn add_to_root_index(&mut self, name: &str) {
        let root = Self::root_of(name).to_owned();
        self.names_by_root
            .entry(root)
            .or_default()
            .insert(name.to_owned());
    }

    /// Remove a name from the root index.
    fn remove_from_root_index(&mut self, name: &str) {
        let root = Self::root_of(name);
        if let Some(set) = self.names_by_root.get_mut(root) {
            set.remove(name);
            if set.is_empty() {
                self.names_by_root.remove(root);
            }
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
        self.add_to_root_index(name);
        id
    }

    /// Register a name for an existing variable id.
    ///
    /// Used when creating compound type sub-parts (e.g. `p.x`, `p.y` for a pair `p`).
    pub fn register_name(&mut self, name: &str, id: VarId) {
        self.name_to_id.insert(name.to_owned(), id);
        self.add_to_root_index(name);
    }

    /// Remove a name binding and return the previously bound variable id.
    pub fn unbind_name(&mut self, name: &str) -> Option<VarId> {
        let result = self.name_to_id.remove(name);
        if result.is_some() {
            self.remove_from_root_index(name);
        }
        result
    }

    /// Remove all bindings for a root name and its suffix/subscript descendants.
    ///
    /// Examples for root `a`: `a`, `a.x`, `a[1]`, `a[1].x`.
    pub fn take_name_bindings_for_root(&mut self, root: &str) -> Vec<(String, VarId)> {
        let Some(names) = self.names_by_root.remove(root) else {
            return Vec::new();
        };

        let mut taken = Vec::with_capacity(names.len());
        for name in names {
            if let Some(id) = self.name_to_id.remove(&name) {
                taken.push((name, id));
            }
        }

        taken
    }

    /// Clear current bindings for a root name and all its descendants.
    pub fn clear_name_bindings_for_root(&mut self, root: &str) {
        let Some(names) = self.names_by_root.remove(root) else {
            return;
        };

        for name in names {
            self.name_to_id.remove(&name);
        }
    }

    /// Restore a name binding to a previous state.
    pub fn restore_name_binding(&mut self, name: &str, prev: Option<VarId>) {
        if let Some(id) = prev {
            self.name_to_id.insert(name.to_owned(), id);
            self.add_to_root_index(name);
        } else {
            self.name_to_id.remove(name);
            self.remove_from_root_index(name);
        }
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

    /// Set a variable's value, maintaining the reverse dependency index.
    pub fn set(&mut self, id: VarId, value: VarValue) {
        let idx = id.0 as usize;
        if idx >= self.values.len() {
            return;
        }

        // Remove old dep-index entries for this variable.
        if let VarValue::NumericVar(NumericState::Dependent(ref old_dep)) = self.values[idx] {
            for term in old_dep {
                if let Some(ref_id) = term.var_id {
                    if let Some(set) = self.dep_index.get_mut(&ref_id) {
                        set.remove(&id);
                        if set.is_empty() {
                            self.dep_index.remove(&ref_id);
                        }
                    }
                }
            }
        }

        // Add new dep-index entries.
        if let VarValue::NumericVar(NumericState::Dependent(ref new_dep)) = value {
            for term in new_dep {
                if let Some(ref_id) = term.var_id {
                    self.dep_index.entry(ref_id).or_default().insert(id);
                }
            }
        }

        self.values[idx] = value;
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
    /// existing dependent variables that reference the pivot.
    pub fn apply_linear_solution(&mut self, pivot: VarId, dep: &DepList) {
        if let Some(v) = constant_value(dep) {
            self.make_known(pivot, v);
        } else {
            self.make_dependent(pivot, dep.clone());
        }

        // Use the reverse dependency index to find only variables that
        // actually reference the pivot, instead of scanning all variables.
        let dependents: Vec<VarId> = self
            .dep_index
            .get(&pivot)
            .map(|s| s.iter().copied().collect())
            .unwrap_or_default();

        let mut updates: Vec<(VarId, NumericState)> = Vec::new();
        for id in dependents {
            if id == pivot {
                continue;
            }
            if let VarValue::NumericVar(NumericState::Dependent(existing)) =
                &self.values[id.0 as usize]
            {
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

    /// Return the declared type for an exact variable path.
    ///
    /// For collective declarations like `pair A[]`, querying
    /// `[SuffixSegment::Subscript]` on root `A` returns `Some(PairType)`.
    #[must_use]
    pub fn declared_type(&self, root: SymbolId, suffixes: &[SuffixSegment]) -> Option<Type> {
        let mut node = self.roots.get(&root)?;
        for seg in suffixes {
            node = match seg {
                SuffixSegment::Attr(id) => node.attrs.get(id)?,
                SuffixSegment::Subscript => node.collective.as_deref()?,
            };
        }
        (node.ty != Type::Undefined).then_some(node.ty)
    }

    /// Check whether extending a variable rooted at `root` with the given
    /// `suffix_id` (a named attribute) would match a declared path.
    ///
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
    /// Saved bindings for a root name and its descendants (`a`, `a[1]`, `a.x`, ...).
    NameBindings {
        root: String,
        prev: Vec<(String, VarId)>,
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

    /// Save bindings for a root name and its descendants.
    pub fn save_name_bindings(&mut self, root: String, prev: Vec<(String, VarId)>) {
        self.entries.push(SaveEntry::NameBindings { root, prev });
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
    fn var_trie_declared_type_for_collective_subscript() {
        let mut trie = VarTrie::new();
        let mut symbols = crate::symbols::SymbolTable::new();
        let a = symbols.lookup("A");

        trie.declare(a, &[SuffixSegment::Subscript], Type::PairType);

        assert_eq!(trie.declared_type(a, &[]), None);
        assert_eq!(
            trie.declared_type(a, &[SuffixSegment::Subscript]),
            Some(Type::PairType)
        );
    }

    #[test]
    fn var_trie_declared_type_for_attr_suffix() {
        let mut trie = VarTrie::new();
        let mut symbols = crate::symbols::SymbolTable::new();
        let a = symbols.lookup("A");
        let s = symbols.lookup("s");

        trie.declare(a, &[SuffixSegment::Attr(s)], Type::Numeric);

        assert_eq!(
            trie.declared_type(a, &[SuffixSegment::Attr(s)]),
            Some(Type::Numeric)
        );
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

    // take_name_bindings_for_root / clear_name_bindings_for_root must only
    // match the root and its `.`/`[` descendants, not similarly-prefixed roots.

    #[test]
    fn take_name_bindings_does_not_match_similar_prefix() {
        let mut vars = Variables::new();
        let _a = vars.lookup("a");
        let _ax = vars.lookup("a.x");
        let _a1 = vars.lookup("a[1]");
        let _ab = vars.lookup("ab"); // different root, should NOT match
        let _abc = vars.lookup("abc.x"); // different root, should NOT match

        let taken = vars.take_name_bindings_for_root("a");
        let taken_names: Vec<&str> = taken.iter().map(|(n, _)| n.as_str()).collect();

        assert!(taken_names.contains(&"a"), "should take 'a'");
        assert!(taken_names.contains(&"a.x"), "should take 'a.x'");
        assert!(taken_names.contains(&"a[1]"), "should take 'a[1]'");
        assert!(!taken_names.contains(&"ab"), "should NOT take 'ab'");
        assert!(!taken_names.contains(&"abc.x"), "should NOT take 'abc.x'");
    }

    #[test]
    fn clear_name_bindings_removes_descendants_only() {
        let mut vars = Variables::new();
        let _a = vars.lookup("a");
        let _a_y = vars.lookup("a.y");
        let _a_1_x = vars.lookup("a[1].x");
        let _ab = vars.lookup("ab");

        vars.clear_name_bindings_for_root("a");

        assert!(vars.lookup_existing("a").is_none(), "'a' should be cleared");
        assert!(
            vars.lookup_existing("a.y").is_none(),
            "'a.y' should be cleared"
        );
        assert!(
            vars.lookup_existing("a[1].x").is_none(),
            "'a[1].x' should be cleared"
        );
        assert!(
            vars.lookup_existing("ab").is_some(),
            "'ab' should NOT be cleared"
        );
    }

    // apply_linear_solution must update only dependents that reference the pivot.

    #[test]
    fn apply_linear_solution_updates_referenced_dependent_only() {
        use crate::equation::{const_dep, DepTerm};

        let mut vars = Variables::new();
        let x = vars.alloc();
        let y = vars.alloc();
        let z = vars.alloc();

        // Make x independent (serial 1)
        vars.make_independent(x);

        // y = 2*x + 3  (depends on x)
        let dep_y = vec![
            DepTerm {
                coeff: 2.0,
                var_id: Some(x),
            },
            DepTerm {
                coeff: 3.0,
                var_id: None,
            },
        ];
        vars.make_dependent(y, dep_y);

        // z = 5.0  (known, does NOT depend on x)
        vars.make_known(z, 5.0);

        // Solve: x = 10
        let solution = const_dep(10.0);
        vars.apply_linear_solution(x, &solution);

        // x should be known(10)
        assert!((vars.known_value(x).unwrap() - 10.0).abs() < 1e-9);
        // y = 2*10 + 3 = 23
        assert!((vars.known_value(y).unwrap() - 23.0).abs() < 1e-9);
        // z should still be 5 (unchanged)
        assert!((vars.known_value(z).unwrap() - 5.0).abs() < 1e-9);
    }

    #[test]
    fn apply_linear_solution_chain_substitution() {
        use crate::equation::{const_dep, DepTerm};

        let mut vars = Variables::new();
        let x = vars.alloc(); // VarId(0)
        let y = vars.alloc(); // VarId(1)
        let z = vars.alloc(); // VarId(2)

        vars.make_independent(x);
        vars.make_independent(y);

        // z = x + y + 1
        let dep_z = vec![
            DepTerm {
                coeff: 1.0,
                var_id: Some(y),
            },
            DepTerm {
                coeff: 1.0,
                var_id: Some(x),
            },
            DepTerm {
                coeff: 1.0,
                var_id: None,
            },
        ];
        vars.make_dependent(z, dep_z);

        // Solve: x = 2
        vars.apply_linear_solution(x, &const_dep(2.0));
        // z should now be y + 3

        // Solve: y = 4
        vars.apply_linear_solution(y, &const_dep(4.0));
        // z should now be 7

        assert!((vars.known_value(x).unwrap() - 2.0).abs() < 1e-9);
        assert!((vars.known_value(y).unwrap() - 4.0).abs() < 1e-9);
        assert!((vars.known_value(z).unwrap() - 7.0).abs() < 1e-9);
    }
}
