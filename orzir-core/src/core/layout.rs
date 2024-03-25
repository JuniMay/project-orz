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

#[derive(Default)]
pub struct Layout {
    blocks: BlockList,
}

impl Layout {
    pub fn entry_block(&self) -> Option<ArenaPtr<Block>> { self.blocks.front() }

    pub fn iter_blocks(&self) -> impl Iterator<Item = ArenaPtr<Block>> + '_ {
        self.blocks.into_iter().map(|(block, _)| block)
    }

    pub fn iter_ops(&self, block: ArenaPtr<Block>) -> impl Iterator<Item = ArenaPtr<OpObj>> + '_ {
        self.blocks
            .node(block)
            .unwrap()
            .ops
            .into_iter()
            .map(|(op, _)| op)
    }

    pub fn iter_ops_chained(&self) -> impl Iterator<Item = ArenaPtr<OpObj>> + '_ {
        self.blocks
            .into_iter()
            .flat_map(|(_, node)| node.ops.into_iter().map(move |(op, _)| op))
    }

    pub fn append_block(&mut self, block: ArenaPtr<Block>) { self.blocks.append(block).unwrap(); }

    pub fn append_op(&mut self, block: ArenaPtr<Block>, op: ArenaPtr<OpObj>) {
        self.blocks.node_mut(block).unwrap().ops.append(op).unwrap();
    }

    pub fn remove_block(&mut self, block: ArenaPtr<Block>) { self.blocks.remove(block).unwrap(); }

    pub fn remove_op(&mut self, block: ArenaPtr<Block>, op: ArenaPtr<OpObj>) {
        self.blocks.node_mut(block).unwrap().ops.remove(op).unwrap();
    }

    pub fn insert_block_before(&mut self, block: ArenaPtr<Block>, before: ArenaPtr<Block>) {
        self.blocks.insert_before(block, before).unwrap();
    }

    pub fn insert_block_after(&mut self, block: ArenaPtr<Block>, after: ArenaPtr<Block>) {
        self.blocks.insert_after(block, after).unwrap();
    }

    pub fn insert_op_before(
        &mut self,
        block: ArenaPtr<Block>,
        op: ArenaPtr<OpObj>,
        before: ArenaPtr<OpObj>,
    ) {
        self.blocks
            .node_mut(block)
            .unwrap()
            .ops
            .insert_before(op, before)
            .unwrap();
    }

    pub fn insert_op_after(
        &mut self,
        block: ArenaPtr<Block>,
        op: ArenaPtr<OpObj>,
        after: ArenaPtr<OpObj>,
    ) {
        self.blocks
            .node_mut(block)
            .unwrap()
            .ops
            .insert_after(op, after)
            .unwrap();
    }
}
