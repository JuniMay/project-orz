use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};

use crate::support::{bimap::BiMap, storage::ArenaPtr};
use anyhow::Result;
use thiserror::Error;

use super::operation::OpObj;

pub type SymbolTableOwned = Rc<RefCell<SymbolTable>>;
pub type SymbolTableCell = Weak<RefCell<SymbolTable>>;

/// A symbol table.
///
/// Symbol table defines the non-SSA values
pub struct SymbolTable {
    symbols: HashMap<String, ArenaPtr<OpObj>>,
    above: Option<SymbolTableCell>,
}

impl SymbolTable {
    /// Create a new symbol table.
    pub fn new(above: Option<SymbolTableCell>) -> Self {
        Self {
            symbols: HashMap::new(),
            above,
        }
    }

    /// Insert a symbol into the table.
    pub fn insert(&mut self, name: String, value: ArenaPtr<OpObj>) {
        self.symbols.insert(name, value);
    }

    pub fn lookup(&self, name: &str) -> Option<ArenaPtr<OpObj>> {
        self.symbols.get(name).cloned().or_else(|| {
            self.above
                .as_ref()
                .and_then(|above| above.upgrade().map(|table| table.borrow().lookup(name)))
                .flatten()
        })
    }
}

#[derive(Debug, Error)]
pub enum NameAllocErr {
    /// The key is already assigned or allocated.
    #[error("key is already allocated.")]
    KeyDuplicated,

    /// The name is already assigned or allocated.
    #[error("name is already allocated.")]
    NameDuplicated,
}

pub struct NameManager<T> {
    counter: u32,
    names: BiMap<ArenaPtr<T>, String>,
}

impl<T> Default for NameManager<T> {
    fn default() -> Self {
        Self {
            counter: 0,
            names: BiMap::default(),
        }
    }
}

impl<T> NameManager<T> {
    pub fn set(&mut self, ptr: ArenaPtr<T>, name: String) -> Result<()> {
        if self.names.contains_rev(&name) {
            return Err(NameAllocErr::NameDuplicated.into());
        }
        if self.names.contains_fwd(&ptr) {
            return Err(NameAllocErr::KeyDuplicated.into());
        }
        self.names.insert(ptr, name);
        Ok(())
    }

    pub fn get(&mut self, ptr: ArenaPtr<T>) -> String {
        if let Some(name) = self.names.get_fwd(&ptr) {
            return name.clone();
        }

        loop {
            let name = format!("{}", self.counter);
            self.counter += 1;
            if !self.names.contains_rev(&name) {
                self.names.insert(ptr, name.clone());
                return name;
            }
        }
    }

    pub(super) fn get_by_name(&self, name: &str) -> Option<ArenaPtr<T>> {
        self.names.get_rev(&name.to_string()).cloned()
    }
}
