use crate::support::storage::ArenaPtr;

use super::{
    block::Block,
    context::Context,
    operation::OpObj,
    ty::{TypeObj, Typed},
};

pub enum Value {
    /// The value is a result of an operation.
    OpResult {
        /// The type of the result.
        ty: ArenaPtr<TypeObj>,
        /// The operation.
        op: ArenaPtr<OpObj>,
        /// The index of the result.
        index: usize,
    },
    /// The value is a block argument.
    BlockArgument {
        /// The type of the argument.
        ty: ArenaPtr<TypeObj>,
        /// The block of the argument.
        block: ArenaPtr<Block>,
        /// The index of the argument.
        index: usize,
    },
}

impl Typed for Value {
    fn ty(&self, _: &Context) -> ArenaPtr<TypeObj> {
        match self {
            Value::OpResult { ty, .. } => *ty,
            Value::BlockArgument { ty, .. } => *ty,
        }
    }
}
