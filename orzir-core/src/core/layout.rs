use super::{block::Block, op::OpObj};
use crate::{
    impl_list_node,
    support::{list::List, storage::ArenaPtr},
};

#[derive(Default, Debug)]
pub struct BlockNode {
    prev: Option<ArenaPtr<Block>>,
    next: Option<ArenaPtr<Block>>,
}

impl_list_node!(BlockNode, ArenaPtr<Block>);

pub type BlockList = List<ArenaPtr<Block>, BlockNode>;

#[derive(Default, Debug)]
pub struct OpNode {
    prev: Option<ArenaPtr<OpObj>>,
    next: Option<ArenaPtr<OpObj>>,
}

impl_list_node!(OpNode, ArenaPtr<OpObj>);

pub type OpList = List<ArenaPtr<OpObj>, OpNode>;
