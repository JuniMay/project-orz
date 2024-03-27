use std::fmt::Write;

use anyhow::{anyhow, Result};

use super::{
    block::Block,
    context::Context,
    operation::OpObj,
    parse::TokenKind,
    ty::{TyObj, Typed},
};
use crate::{
    support::storage::ArenaPtr, Parse, Print, PrintState, Region, TokenStream, Verify,
    VerifyInterfaces,
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
    /// Get a clean builder of the operation result.
    pub fn op_result_builder() -> OpResultBuilder { OpResultBuilder::default() }

    /// Get a clean builder of the block argument.
    pub fn block_argument_builder() -> BlockArgumentBuilder { BlockArgumentBuilder::default() }

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
    pub(crate) fn name(&self, ctx: &Context) -> String {
        let name = ctx.value_names.borrow_mut().get(self.self_ptr());
        name
    }

    /// Set the name of the value.
    pub(crate) fn set_name(&self, ctx: &Context, name: String) -> Result<()> {
        ctx.value_names.borrow_mut().set(self.self_ptr(), name)
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

/// The builder to build [`Value::OpResult`].
///
/// This builder requires the type of the result, the parent operation, and the
/// index of the result. If the name is set, the builder will lookup if there is
/// a reserved [`ArenaPtr<Value>`] by the name. If not, a new
/// [`ArenaPtr<Value>`] will be reserved, and the name will be set.
///
/// The index represents the position of this result in the operation. If the
/// index is not set, the builder cannot attach the result to the operation and
/// will thus return an error.
#[derive(Debug, Default)]
pub struct OpResultBuilder {
    name: Option<String>,
    ty: Option<ArenaPtr<TyObj>>,
    op: Option<ArenaPtr<OpObj>>,
    index: Option<usize>,
}

/// The builder to build [`Value::BlockArgument`].
///
/// This builder requires the type of the argument, the parent block, and the
/// index of the argument. If the name is set, the builder will lookup if there
/// is a reserved [`ArenaPtr<Value>`] by the name. If not, a new
/// [`ArenaPtr<Value>`] will be reserved, and the name will be set.
///
/// The index represents the position of this argument in the block. If the
/// index is not set, the builder cannot attach the argument to the block and
/// will thus return an error.
#[derive(Debug, Default)]
pub struct BlockArgumentBuilder {
    name: Option<String>,
    ty: Option<ArenaPtr<TyObj>>,
    block: Option<ArenaPtr<Block>>,
    index: Option<usize>,
}

impl OpResultBuilder {
    /// Set the type of the result.
    pub fn ty(mut self, ty: ArenaPtr<TyObj>) -> Self {
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

    /// Set the index of the result.
    pub fn index(mut self, index: usize) -> Self {
        self.index = Some(index);
        self
    }

    /// Build the value and consume the builder.
    ///
    /// This will add the result to the operation.
    ///
    /// # Errors
    ///
    /// This function will return an error if the type, operation, or index is not
    pub fn build(self, ctx: &mut Context) -> Result<ArenaPtr<Value>> {
        let ty = self.ty.ok_or_else(|| anyhow!("missing type"))?;
        let op = self.op.ok_or_else(|| anyhow!("missing op"))?;
        let index = self.index.ok_or_else(|| anyhow!("missing index"))?;

        // the value might be used before, so try to get the reference by the name.
        let self_ptr = if let Some(ref name) = self.name {
            ctx.value_names
                .borrow()
                .get_by_name(name)
                .unwrap_or_else(|| ctx.values.reserve())
        } else {
            ctx.values.reserve()
        };
        op.deref_mut(&mut ctx.ops).as_mut().set_result(index, self_ptr)?;
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

impl BlockArgumentBuilder {
    /// Set the type of the argument.
    pub fn ty(mut self, ty: ArenaPtr<TyObj>) -> Self {
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

    /// Set the index of the argument.
    pub fn index(mut self, index: usize) -> Self {
        self.index = Some(index);
        self
    }

    /// Build the value and consume the builder.
    ///
    /// This will add the block argument to the block.
    ///
    /// # Errors
    ///
    /// This function will return an error if the type, block, or index is not set.
    pub fn build(self, ctx: &mut Context) -> Result<ArenaPtr<Value>> {
        let ty = self.ty.ok_or_else(|| anyhow!("missing type"))?;
        let block = self.block.ok_or_else(|| anyhow!("missing block"))?;
        let index = self.index.ok_or_else(|| anyhow!("missing index"))?;

        let self_ptr = if let Some(ref name) = self.name {
            ctx.value_names
                .borrow()
                .get_by_name(name)
                .unwrap_or_else(|| ctx.values.reserve())
        } else {
            ctx.values.reserve()
        };
        block.deref_mut(&mut ctx.blocks).set_arg(index, self_ptr)?;
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
