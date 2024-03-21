use std::collections::HashMap;

use crate::support::storage::{Arena, UniqueArena};

use super::{
    block::Block, dialect::Dialect, mnemonic::MnemonicSegment, operation::OpObj, region::Region,
    symbol::NameManager, ty::TypeObj, value::Value,
};

/// The context of the whole IR.
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
    pub types: UniqueArena<TypeObj>,
    /// The dialects.
    pub dialects: HashMap<MnemonicSegment, Dialect>,
    /// The name of values.
    pub value_names: NameManager<Value>,
}

impl Default for Context {
    fn default() -> Self {
        Self {
            values: Arena::default(),
            blocks: Arena::default(),
            regions: Arena::default(),
            ops: Arena::default(),
            types: UniqueArena::default(),
            dialects: HashMap::default(),
            value_names: NameManager::default(),
        }
    }
}
