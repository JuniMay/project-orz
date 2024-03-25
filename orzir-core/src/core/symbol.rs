use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};

use anyhow::Result;
use thiserror::Error;

use super::operation::OpObj;
use crate::support::{
    bimap::{BiMap, Duplicated},
    storage::ArenaPtr,
};

pub type SymbolTableOwned = Rc<RefCell<SymbolTable>>;
pub type SymbolTableCell = Weak<RefCell<SymbolTable>>;

/// A symbol table.
///
/// Symbol table defines the non-SSA values
pub struct SymbolTable {
    /// The symbol name and the operation that defines it.
    symbols: HashMap<String, ArenaPtr<OpObj>>,
    /// The upper-level symbol table.
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

    /// Insert a symbol and its definition operation into the table.
    pub fn insert(&mut self, name: String, op: ArenaPtr<OpObj>) { self.symbols.insert(name, op); }

    /// Get the operation that defines the symbol.
    ///
    /// This might return the operation from the upper-level symbol table.
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
pub enum NameAllocDuplicatedErr {
    /// The key is already assigned or allocated with a different name.
    #[error("key is already allocated.")]
    Key,

    /// The name is already assigned or allocated for a different key.
    #[error("name is already allocated.")]
    Name,

    /// The key and name are both duplicated with different values.
    #[error("key and name are both duplicated.")]
    Both,
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
    pub(super) fn set(&mut self, ptr: ArenaPtr<T>, name: String) -> Result<()> {
        let result = self.names.checked_insert(ptr, name);
        match result {
            Ok(_) => Ok(()),
            Err(Duplicated::Fwd(_)) => Err(NameAllocDuplicatedErr::Key.into()),
            Err(Duplicated::Rev(_)) => Err(NameAllocDuplicatedErr::Name.into()),
            Err(Duplicated::Both(_, _)) => Err(NameAllocDuplicatedErr::Both.into()),
            Err(Duplicated::Full) => Ok(()),
        }
    }

    pub(super) fn get(&mut self, ptr: ArenaPtr<T>) -> String {
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
