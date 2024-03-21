use std::cell::RefCell;

use crate::support::storage::ArenaPtr;

use super::{
    block::Block,
    layout::Layout,
    operation::OpObj,
    symbol::{NameManager, SymbolTableOwned},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RegionKind {
    Graph,
    SsaCfg,
}

/// A region in the IR.
pub struct Region {
    /// The kind of the region.
    kind: RegionKind,
    /// The layout of the region.
    layout: Layout,
    /// The symbol table of the region.
    symbol_table: SymbolTableOwned,
    /// The block names of the region.
    block_names: RefCell<NameManager<ArenaPtr<Block>>>,
    /// The parent operation of the region.
    parent_op: ArenaPtr<OpObj>,
    /// The index of the region in the parent operation.
    index: usize,
}
