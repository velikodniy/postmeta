use crate::internals::Internals;
use crate::symbols::{SymbolId, SymbolTable};
use crate::variables::{SaveStack, Variables};

use super::macros::MacroTable;
use super::pictures::PictureManager;

/// Coordinates `begingroup`/`save`/`endgroup` state transitions.
#[derive(Debug, Default)]
pub(in crate::interpreter) struct ScopeManager {
    save_stack: SaveStack,
}

impl ScopeManager {
    pub(in crate::interpreter) fn new() -> Self {
        Self::default()
    }

    pub(in crate::interpreter) fn begin_group(&mut self, macros: &mut MacroTable) {
        self.save_stack.push_boundary();
        macros.begin_group();
    }

    pub(in crate::interpreter) fn save_name(
        &mut self,
        symbol: SymbolId,
        symbols: &mut SymbolTable,
        variables: &mut Variables,
        picture_manager: &mut PictureManager,
        macros: &mut MacroTable,
    ) {
        let entry = symbols.get(symbol);
        self.save_stack.save_symbol(symbol, entry);

        if picture_manager.currentpicture_dirty() && symbols.name(symbol) == "currentpicture" {
            picture_manager.sync_currentpicture_variable(variables);
        }

        let root = symbols.name(symbol);
        if let Some((root_name, var_id, value)) = variables.try_save_root_fast(root) {
            self.save_stack
                .save_root_value_only(root_name, symbol, var_id, value);
        } else {
            let root = root.to_owned();
            let prev = variables.take_name_bindings_for_root(&root);
            self.save_stack.save_name_bindings(root, symbol, prev);
        }

        variables.invalidate_sym_cache_entry(symbol);
        symbols.clear(symbol);
        macros.save_and_remove(symbol);
    }

    pub(in crate::interpreter) fn save_internal(&mut self, index: u16, value: f64) {
        self.save_stack.save_internal(index, value);
    }

    pub(in crate::interpreter) fn end_group(
        &mut self,
        symbols: &mut SymbolTable,
        variables: &mut Variables,
        internals: &mut Internals,
        macros: &mut MacroTable,
    ) {
        macros.restore_to_group_boundary();

        let entries = self.save_stack.restore_to_boundary();
        for entry in entries {
            match entry {
                crate::variables::SaveEntry::Variable { id, value } => {
                    variables.set(id, value);
                }
                crate::variables::SaveEntry::Internal { index, value } => {
                    internals.set(index, value);
                }
                crate::variables::SaveEntry::Symbol { id, entry } => {
                    symbols.set(id, entry);
                }
                crate::variables::SaveEntry::NameBindings { root, sym, prev } => {
                    variables.invalidate_sym_cache_entry(sym);
                    variables.clear_name_bindings_for_root(&root);
                    for (name, id) in prev {
                        variables.register_name(&name, id);
                    }
                }
                crate::variables::SaveEntry::RootValueOnly {
                    root,
                    sym,
                    id,
                    value,
                } => {
                    variables.invalidate_sym_cache_entry(sym);
                    variables.clear_name_bindings_for_root(&root);
                    variables.set(id, value);
                    variables.register_name(&root, id);
                }
                crate::variables::SaveEntry::Boundary => {}
            }
        }
    }
}
