use std::fmt::Write;

use anyhow::Result;

use super::{
    block::Block,
    context::Context,
    operation::OpObj,
    parse::{ParseState, TokenKind},
    ty::{TyObj, Typed},
};
use crate::{
    support::storage::ArenaPtr, Parse, Print, PrintState, Region, Verify, VerifyInterfaces,
};

/// An SSA value.
pub enum Value {
    /// The value is a result of an operation.
    OpResult {
        /// The self ptr.
        self_ptr: ArenaPtr<Self>,
        /// The type of the result.
        ty: ArenaPtr<TyObj>,
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
        ty: ArenaPtr<TyObj>,
        /// The block of the argument.
        block: ArenaPtr<Block>,
        /// The index of the argument.
        index: usize,
    },
}

impl Typed for Value {
    fn ty(&self, _: &Context) -> ArenaPtr<TyObj> {
        match self {
            Value::OpResult { ty, .. } => *ty,
            Value::BlockArgument { ty, .. } => *ty,
        }
    }
}

impl VerifyInterfaces for Value {
    fn verify_interfaces(&self, _ctx: &Context) -> Result<()> { Ok(()) }
}

impl Verify for Value {
    fn verify(&self, ctx: &Context) -> Result<()> {
        self.ty(ctx).deref(&ctx.tys).as_ref().verify(ctx)
    }
}

impl Value {
    pub fn new_op_result(
        ctx: &mut Context,
        ty: ArenaPtr<TyObj>,
        op: ArenaPtr<OpObj>,
        index: usize,
        name: Option<String>,
    ) -> Result<ArenaPtr<Value>> {
        // let self_ptr = ctx.values.reserve();
        let self_ptr = if let Some(name) = name {
            let self_ptr = ctx
                .value_names
                .borrow()
                .get_by_name(&name)
                .unwrap_or_else(|| ctx.values.reserve());
            ctx.value_names.borrow_mut().set(self_ptr, name)?;
            self_ptr
        } else {
            ctx.values.reserve()
        };
        let instance = Value::OpResult {
            self_ptr,
            ty,
            op,
            index,
        };
        ctx.values.fill(self_ptr, instance);
        Ok(self_ptr)
    }

    pub fn new_block_argument(
        ctx: &mut Context,
        ty: ArenaPtr<TyObj>,
        block: ArenaPtr<Block>,
        index: usize,
        name: Option<String>,
    ) -> Result<ArenaPtr<Value>> {
        let self_ptr = if let Some(name) = name {
            let self_ptr = ctx
                .value_names
                .borrow()
                .get_by_name(&name)
                .unwrap_or_else(|| ctx.values.reserve());
            ctx.value_names.borrow_mut().set(self_ptr, name)?;
            self_ptr
        } else {
            ctx.values.reserve()
        };
        let instance = Value::BlockArgument {
            self_ptr,
            ty,
            block,
            index,
        };
        ctx.values.fill(self_ptr, instance);
        Ok(self_ptr)
    }

    /// Get the self ptr.
    fn self_ptr(&self) -> ArenaPtr<Self> {
        match self {
            Value::OpResult { self_ptr, .. } => *self_ptr,
            Value::BlockArgument { self_ptr, .. } => *self_ptr,
        }
    }

    /// Get the name of the value.
    ///
    /// This will lookup the name by the self ptr. If the name is not set, the
    /// name manager will allocate a new name.
    pub fn name(&self, ctx: &Context) -> String {
        let name = ctx.value_names.borrow_mut().get(self.self_ptr());
        name
    }

    /// Get the parent region of the value.
    pub fn parent_region(&self, ctx: &Context) -> ArenaPtr<Region> {
        match self {
            Value::OpResult { op, .. } => op
                .deref(&ctx.ops)
                .as_ref()
                .parent_region(ctx)
                .expect("OpResult should be embraced by a region."),
            Value::BlockArgument { block, .. } => block.deref(&ctx.blocks).parent_region(),
        }
    }
}

impl Print for Value {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        write!(state.buffer, "%{}", self.name(ctx))?;
        Ok(())
    }
}

impl Parse for Value {
    type Item = ArenaPtr<Value>;

    fn parse(ctx: &mut Context, state: &mut ParseState) -> Result<Self::Item> {
        let name = state.stream.consume()?;
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
