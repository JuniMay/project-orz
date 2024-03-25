use super::{block::Block, operation::OpObj};
use crate::{
    impl_list_node,
    support::{list::List, storage::ArenaPtr},
};

#[derive(Default)]
pub struct BlockNode {
    prev: Option<ArenaPtr<Block>>,
    next: Option<ArenaPtr<Block>>,

    ops: OpList,
}

impl_list_node!(BlockNode, ArenaPtr<Block>);

pub type BlockList = List<ArenaPtr<Block>, BlockNode>;

#[derive(Default)]
pub struct OpNode {
    prev: Option<ArenaPtr<OpObj>>,
    next: Option<ArenaPtr<OpObj>>,
}

impl_list_node!(OpNode, ArenaPtr<OpObj>);

pub type OpList = List<ArenaPtr<OpObj>, OpNode>;

/// The layout of a function.
///
/// The layout utilizes a key-node system to build a safe linked list.
/// This is inspired by the [key-node-list](https://github.com/MaxXSoft/key-node-list) crate.
#[derive(Default)]
pub struct Layout {
    /// The block list of the layout.
    blocks: BlockList,
}

impl Layout {
    /// Get the entry block of the layout.
    ///
    /// This will get the first block in the layout as the entry block without
    /// any control-flow analysis.
    pub fn entry_block(&self) -> Option<ArenaPtr<Block>> { self.blocks.front() }

    /// Get the iterator of the blocks.
    pub fn iter_blocks(&self) -> impl Iterator<Item = ArenaPtr<Block>> + '_ {
        self.blocks.into_iter().map(|(block, _)| block)
    }

    /// Get the iterator of the operations in a block.
    pub fn iter_ops(&self, block: ArenaPtr<Block>) -> impl Iterator<Item = ArenaPtr<OpObj>> + '_ {
        self.blocks.node(block).unwrap().ops.into_iter().map(|(op, _)| op)
    }

    /// Get the iterator of the operations in all blocks.
    pub fn iter_ops_chained(&self) -> impl Iterator<Item = ArenaPtr<OpObj>> + '_ {
        self.blocks
            .into_iter()
            .flat_map(|(_, node)| node.ops.into_iter().map(move |(op, _)| op))
    }

    /// Append a block to the layout.
    pub fn append_block(&mut self, block: ArenaPtr<Block>) { self.blocks.append(block).unwrap(); }

    /// Append an operation to a block.
    pub fn append_op(&mut self, block: ArenaPtr<Block>, op: ArenaPtr<OpObj>) {
        self.blocks.node_mut(block).unwrap().ops.append(op).unwrap();
    }

    /// Remove a block from the layout.
    pub fn remove_block(&mut self, block: ArenaPtr<Block>) { self.blocks.remove(block).unwrap(); }

    /// Remove an operation from a block.
    pub fn remove_op(&mut self, block: ArenaPtr<Block>, op: ArenaPtr<OpObj>) {
        self.blocks.node_mut(block).unwrap().ops.remove(op).unwrap();
    }

    /// Insert a block before another block.
    pub fn insert_block_before(&mut self, block: ArenaPtr<Block>, before: ArenaPtr<Block>) {
        self.blocks.insert_before(block, before).unwrap();
    }

    /// Insert a block after another block.
    pub fn insert_block_after(&mut self, block: ArenaPtr<Block>, after: ArenaPtr<Block>) {
        self.blocks.insert_after(block, after).unwrap();
    }

    /// Insert an operation before another operation in a block.
    pub fn insert_op_before(
        &mut self,
        block: ArenaPtr<Block>,
        op: ArenaPtr<OpObj>,
        before: ArenaPtr<OpObj>,
    ) {
        self.blocks.node_mut(block).unwrap().ops.insert_before(op, before).unwrap();
    }

    /// Insert an operation after another operation in a block.
    pub fn insert_op_after(
        &mut self,
        block: ArenaPtr<Block>,
        op: ArenaPtr<OpObj>,
        after: ArenaPtr<OpObj>,
    ) {
        self.blocks.node_mut(block).unwrap().ops.insert_after(op, after).unwrap();
    }
}
