use crate::{support::storage::ArenaPtr, Parse, Print, PrintState, TokenStream};
use anyhow::{anyhow, Result};
use std::fmt::Write;

use super::{
    block::Block,
    context::Context,
    operation::OpObj,
    parse::TokenKind,
    ty::{TypeObj, Typed},
};

pub enum Value {
    /// The value is a result of an operation.
    OpResult {
        /// The self ptr.
        self_ptr: ArenaPtr<Self>,
        /// The type of the result.
        ty: ArenaPtr<TypeObj>,
        /// The operation.
        op: ArenaPtr<OpObj>,
        /// The index of the result.
        index: usize,
    },
    /// The value is a block argument.
    BlockArgument {
        /// The self ptr.
        self_ptr: ArenaPtr<Self>,
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
    pub fn op_result_builder() -> OpResultBuilder {
        OpResultBuilder::default()
    }

    pub fn block_argument_builder() -> BlockArgumentBuilder {
        BlockArgumentBuilder::default()
    }

    fn self_ptr(&self) -> ArenaPtr<Self> {
        match self {
            Value::OpResult { self_ptr, .. } => *self_ptr,
            Value::BlockArgument { self_ptr, .. } => *self_ptr,
        }
    }

    pub(crate) fn name(&self, ctx: &Context) -> String {
        let name = ctx.value_names.borrow_mut().get(self.self_ptr());
        name
    }

    pub(crate) fn set_name(&self, ctx: &Context, name: String) -> Result<()> {
        ctx.value_names.borrow_mut().set(self.self_ptr(), name)
    }
}

#[derive(Debug, Default)]
pub struct OpResultBuilder {
    name: Option<String>,
    ty: Option<ArenaPtr<TypeObj>>,
    op: Option<ArenaPtr<OpObj>>,
}

#[derive(Debug, Default)]
pub struct BlockArgumentBuilder {
    name: Option<String>,
    ty: Option<ArenaPtr<TypeObj>>,
    block: Option<ArenaPtr<Block>>,
}

/// The builder for [`OpResult`].
impl OpResultBuilder {
    /// Set the type of the result.
    pub fn ty(mut self, ty: ArenaPtr<TypeObj>) -> Self {
        self.ty = Some(ty);
        self
    }

    /// Set the name of the result.
    pub fn name(mut self, name: String) -> Self {
        self.name = Some(name);
        self
    }

    /// Set the operation.
    pub fn op(mut self, op: ArenaPtr<OpObj>) -> Self {
        self.op = Some(op);
        self
    }

    /// Build the value.
    pub fn build(self, ctx: &mut Context) -> Result<ArenaPtr<Value>> {
        let ty = self.ty.ok_or_else(|| anyhow!("missing type"))?;
        let op = self.op.ok_or_else(|| anyhow!("missing op"))?;
        // the value might be used before, so try to get the reference by the name.
        let self_ptr = if let Some(ref name) = self.name {
            ctx.value_names
                .borrow()
                .get_by_name(name)
                .unwrap_or_else(|| ctx.values.reserve())
        } else {
            ctx.values.reserve()
        };
        let index = op
            .deref_mut(&mut ctx.ops)
            .as_inner_mut()
            .as_base_mut()
            .add_result(self_ptr);

        let instance = Value::OpResult {
            self_ptr,
            ty,
            op,
            index,
        };
        if let Some(name) = self.name {
            instance.set_name(ctx, name)?;
        }
        ctx.values.fill(self_ptr, instance);
        Ok(self_ptr)
    }
}

/// The builder for [`BlockArgument`].
impl BlockArgumentBuilder {
    /// Set the type of the argument.
    pub fn ty(mut self, ty: ArenaPtr<TypeObj>) -> Self {
        self.ty = Some(ty);
        self
    }

    /// Set the name of the result.
    pub fn name(mut self, name: String) -> Self {
        self.name = Some(name);
        self
    }

    /// Set the block of the argument.
    pub fn block(mut self, block: ArenaPtr<Block>) -> Self {
        self.block = Some(block);
        self
    }

    /// Build the value.
    pub fn build(self, ctx: &mut Context) -> Result<ArenaPtr<Value>> {
        let ty = self.ty.ok_or_else(|| anyhow!("missing type"))?;
        let block = self.block.ok_or_else(|| anyhow!("missing block"))?;
        let self_ptr = if let Some(ref name) = self.name {
            ctx.value_names
                .borrow()
                .get_by_name(name)
                .unwrap_or_else(|| ctx.values.reserve())
        } else {
            ctx.values.reserve()
        };
        let index = block.deref_mut(&mut ctx.blocks).add_arg(self_ptr);

        let instance = Value::BlockArgument {
            self_ptr,
            ty,
            block,
            index,
        };
        if let Some(name) = self.name {
            instance.set_name(ctx, name)?;
        }
        ctx.values.fill(self_ptr, instance);
        Ok(self_ptr)
    }
}

impl Print for Value {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        write!(state.buffer, "%{}", self.name(ctx))?;
        Ok(())
    }
}

impl Parse for Value {
    type Arg = ();
    type Item = ArenaPtr<Value>;

    fn parse(_: (), ctx: &mut Context, stream: &mut TokenStream) -> Result<Self::Item> {
        let name = stream.consume()?;
        let self_ptr = if let TokenKind::ValueName(name) = &name.kind {
            // try to get the value by name, or reserve a new one.
            let self_ptr = ctx
                .value_names
                .borrow()
                .get_by_name(name)
                .unwrap_or_else(|| ctx.values.reserve());
            // set the name of the value.
            ctx.value_names.borrow_mut().set(self_ptr, name.clone())?;
            self_ptr
        } else {
            anyhow::bail!("expect a value name.")
        };
        Ok(self_ptr)
    }
}
