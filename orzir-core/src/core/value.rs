use std::fmt::Write;

use super::{
    block::Block,
    context::Context,
    op::OpObj,
    parse::{ParseState, TokenKind},
    symbol::NameAllocDuplicatedErr,
    ty::TyObj,
};
use crate::{
    core::parse::ParseErrorKind,
    parse_error,
    support::storage::ArenaPtr,
    token_wildcard,
    Parse,
    ParseResult,
    Print,
    PrintResult,
    PrintState,
    Region,
    RunVerifiers,
    Verify,
    VerifyResult,
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

impl RunVerifiers for Value {
    fn run_verifiers(&self, _ctx: &Context) -> VerifyResult<()> { Ok(()) }
}

impl Verify for Value {
    fn verify(&self, ctx: &Context) -> VerifyResult<()> {
        self.ty(ctx).deref(&ctx.tys).as_ref().verify(ctx)
    }
}

impl Value {
    /// Create a new [`Value::OpResult`].
    ///
    /// If the name is not none, this will lookup for reserved arena ptr by the
    /// name.
    pub fn new_op_result(
        ctx: &mut Context,
        ty: ArenaPtr<TyObj>,
        op: ArenaPtr<OpObj>,
        index: usize,
        name: Option<String>,
    ) -> ArenaPtr<Value> {
        // let self_ptr = ctx.values.reserve();
        let self_ptr = if let Some(name) = name {
            let self_ptr = ctx
                .value_names
                .borrow()
                .get_by_name(&name)
                .unwrap_or_else(|| ctx.values.reserve());
            ctx.value_names
                .borrow_mut()
                .set(self_ptr, name)
                .expect("should be able to set a name for op result.");
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
        self_ptr
    }

    /// Create a new [`Value::BlockArgument`].
    ///
    /// If the name is not none, this will lookup for reserved arena ptr by the
    /// name.
    pub fn new_block_argument(
        ctx: &mut Context,
        ty: ArenaPtr<TyObj>,
        block: ArenaPtr<Block>,
        index: usize,
        name: Option<String>,
    ) -> ArenaPtr<Value> {
        let self_ptr = if let Some(name) = name {
            let self_ptr = ctx
                .value_names
                .borrow()
                .get_by_name(&name)
                .unwrap_or_else(|| ctx.values.reserve());
            ctx.value_names
                .borrow_mut()
                .set(self_ptr, name)
                .expect("should be able to set a name for block argument.");
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
        self_ptr
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

    pub fn ty(&self, _: &Context) -> ArenaPtr<TyObj> {
        match self {
            Value::OpResult { ty, .. } => *ty,
            Value::BlockArgument { ty, .. } => *ty,
        }
    }
}

impl Print for Value {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> PrintResult<()> {
        write!(state.buffer, "%{}", self.name(ctx))?;
        Ok(())
    }
}

impl Parse for Value {
    type Item = ArenaPtr<Value>;

    fn parse(ctx: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        let name_token = state.stream.consume()?;
        let self_ptr = if let TokenKind::ValueName(name) = &name_token.kind {
            let name = name.clone();
            // try to get the value by name, or reserve a new one.
            let self_ptr = ctx
                .value_names
                .borrow()
                .get_by_name(&name)
                .unwrap_or_else(|| ctx.values.reserve());
            // set the name of the value.
            ctx.value_names
                .borrow_mut()
                .set(self_ptr, name.clone())
                .map_err(|e| match e {
                    NameAllocDuplicatedErr::Name => {
                        // if the name is duplicated, this might be a problem of the source code.
                        parse_error!(
                            name_token.span,
                            ParseErrorKind::DuplicatedValueName(name.clone())
                        )
                    }
                    _ => {
                        // but if the key is duplicated, this is a bug of internal system.
                        panic!("unexpected error: {:?}", e);
                    }
                })?;
            self_ptr
        } else {
            return parse_error!(
                name_token.span,
                ParseErrorKind::InvalidToken(vec![token_wildcard!("%...")].into(), name_token.kind)
            )
            .into();
        };
        Ok(self_ptr)
    }
}
