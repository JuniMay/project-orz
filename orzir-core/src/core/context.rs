use std::{cell::RefCell, collections::HashMap};

use crate::support::storage::{Arena, UniqueArena};

use super::{
    block::Block, dialect::Dialect, mnemonic::MnemonicSegment, operation::OpObj, region::Region,
    symbol::NameManager, ty::TypeObj, value::Value,
};

/// The context of the whole IR.
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
    pub types: UniqueArena<TypeObj>,
    /// The dialects.
    pub dialects: HashMap<MnemonicSegment, Dialect>,
    /// The name of values.
    pub(crate) value_names: RefCell<NameManager<Value>>,
}
