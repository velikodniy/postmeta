use std::collections::HashMap;

use crate::symbols::SymbolId;

use crate::interpreter::expand::MacroInfo;

/// Runtime storage for defined macros plus `save`/group restoration state.
#[derive(Debug, Default)]
pub(in crate::interpreter) struct MacroTable {
    definitions: HashMap<SymbolId, MacroInfo>,
    save_stack: Vec<Option<(SymbolId, MacroInfo)>>,
}

impl MacroTable {
    pub(in crate::interpreter) fn new() -> Self {
        Self::default()
    }

    pub(in crate::interpreter) fn insert(&mut self, symbol: SymbolId, info: MacroInfo) {
        self.definitions.insert(symbol, info);
    }

    pub(in crate::interpreter) fn get(&self, symbol: SymbolId) -> Option<&MacroInfo> {
        self.definitions.get(&symbol)
    }

    pub(in crate::interpreter) fn get_cloned(&self, symbol: SymbolId) -> Option<MacroInfo> {
        self.definitions.get(&symbol).cloned()
    }

    pub(in crate::interpreter) fn begin_group(&mut self) {
        self.save_stack.push(None);
    }

    pub(in crate::interpreter) fn save_and_remove(&mut self, symbol: SymbolId) {
        if let Some(info) = self.definitions.remove(&symbol) {
            self.save_stack.push(Some((symbol, info)));
        }
    }

    pub(in crate::interpreter) fn rebind(&mut self, lhs: SymbolId, rhs: SymbolId) {
        if lhs == rhs {
            return;
        }
        let rhs_info = self.get_cloned(rhs);
        self.definitions.remove(&lhs);
        if let Some(info) = rhs_info {
            self.insert(lhs, info);
        }
    }

    pub(in crate::interpreter) fn restore_to_group_boundary(&mut self) {
        while let Some(entry) = self.save_stack.pop() {
            if let Some((symbol, info)) = entry {
                self.definitions.insert(symbol, info);
            } else {
                break;
            }
        }
    }
}
