use std::collections::HashMap;

use crate::support::storage::{Arena, UniqueArena};

use super::{
    block::Block, dialect::Dialect, mnemonic::MnemonicSegment, operation::OpObj, region::Region,
    symbol::NameManager, ty::TypeObj, value::Value,
};

/// The context of the whole IR.
pub struct Context {
    /// The values.
    values: Arena<Value>,
    /// The blocks.
    blocks: Arena<Block>,
    /// The regions.
    regions: Arena<Region>,
    /// The operations.
    ops: Arena<OpObj>,
    /// The types.
    types: UniqueArena<TypeObj>,
    /// The dialects.
    dialects: HashMap<MnemonicSegment, Dialect>,
    /// The name of values.
    value_names: NameManager<Value>,
}
