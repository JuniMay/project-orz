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

impl Value {
    pub fn build_op_result() -> OpResultBuilder {
        OpResultBuilder::default()
    }

    pub fn build_block_argument() -> BlockArgumentBuilder {
        BlockArgumentBuilder::default()
    }
}

#[derive(Debug, Default)]
pub struct OpResultBuilder {
    ty: Option<ArenaPtr<TypeObj>>,
    op: Option<ArenaPtr<OpObj>>,
}

#[derive(Debug, Default)]
pub struct BlockArgumentBuilder {
    ty: Option<ArenaPtr<TypeObj>>,
    block: Option<ArenaPtr<Block>>,
}

impl OpResultBuilder {
    pub fn ty(mut self, ty: ArenaPtr<TypeObj>) -> Self {
        self.ty = Some(ty);
        self
    }

    pub fn op(mut self, op: ArenaPtr<OpObj>) -> Self {
        self.op = Some(op);
        self
    }

    pub fn build(self, ctx: &mut Context) -> ArenaPtr<Value> {
        let ty = self.ty.expect("missing type");
        let op = self.op.expect("missing operation");
        let ptr = ctx.values.reserve();
        let index = op
            .deref_mut(&mut ctx.ops)
            .as_inner_mut()
            .as_base_mut()
            .add_result(ptr);

        let instance = Value::OpResult { ty, op, index };
        ctx.values.fill(ptr, instance);
        ptr
    }
}

impl BlockArgumentBuilder {
    pub fn ty(mut self, ty: ArenaPtr<TypeObj>) -> Self {
        self.ty = Some(ty);
        self
    }

    pub fn block(mut self, block: ArenaPtr<Block>) -> Self {
        self.block = Some(block);
        self
    }

    pub fn build(self, ctx: &mut Context) -> ArenaPtr<Value> {
        let ty = self.ty.expect("missing type");
        let block = self.block.expect("missing block");
        let ptr = ctx.values.reserve();
        let index = block.deref_mut(&mut ctx.blocks).add_arg(ptr);

        let instance = Value::BlockArgument { ty, block, index };
        ctx.values.fill(ptr, instance);
        ptr
    }
}
