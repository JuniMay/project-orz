use std::{cell::RefCell, collections::HashMap};

use super::symbol::NameManager;
use crate::{
    Arena,
    Block,
    CasterStorage,
    Dialect,
    MnemonicSegment,
    OpObj,
    Region,
    TyObj,
    UniqueArena,
    Value,
};

/// The context of the whole IR.
///
/// The context stores all the entities using a simple arena system.
#[derive(Default)]
pub struct Context {
    /// The values.
    pub values: Arena<Value>,
    /// The blocks.
    pub blocks: Arena<Block>,
    /// The regions.
    pub regions: Arena<Region>,
    /// The operations.
    pub ops: Arena<OpObj>,
    /// The types.
    pub tys: UniqueArena<TyObj>,
    /// The dialects.
    pub dialects: HashMap<MnemonicSegment, Dialect>,
    /// The caster storage.
    ///
    /// This is used for interface casting.
    pub casters: CasterStorage,
    /// The name of values.
    pub(crate) value_names: RefCell<NameManager<Value>>,
}

impl Context {
    pub fn register_dialect(&mut self, dialect: Dialect) {
        self.dialects.insert(dialect.mnemonic(), dialect);
    }
}
