use std::fmt::Write;

use downcast_rs::{impl_downcast, Downcast};
use thiserror::Error;

use super::{
    block::Block,
    context::Context,
    mnemonic::Mnemonic,
    parse::{ParseFn, ParseState, TokenKind},
    value::Value,
};
use crate::{
    core::parse::ParseErrorKind,
    parse_error,
    support::{
        cast::{CastMut, CastRef},
        storage::ArenaPtr,
    },
    token, ControlFlow, DataFlow, Parse, ParseResult, Print, PrintResult, PrintState, Region,
    RegionInterface, Verify,
};

/// The successor.
pub struct Successor {
    /// The block destination of the successor.
    block: ArenaPtr<Block>,
    /// The arguments passed to the block.
    args: Vec<ArenaPtr<Value>>,
}

impl Successor {
    /// Create a new successor entity.
    pub fn new(block: ArenaPtr<Block>, args: Vec<ArenaPtr<Value>>) -> Self { Self { block, args } }

    /// Get the block destination of the successor.
    pub fn block(&self) -> ArenaPtr<Block> { self.block }

    /// Get the arguments passed to the block.
    pub fn args(&self) -> &[ArenaPtr<Value>] { &self.args }
}

#[derive(Debug, Error)]
#[error("expect block label, found {0:?}")]
struct ExpectBlockLabelInSuccessor(TokenKind);

impl Parse for Successor {
    type Item = Successor;

    /// Parse the successor.
    ///
    /// # Syntax
    ///
    /// ```text
    /// <block_label> `(` <arg_name_list> `)`
    /// ```
    fn parse(ctx: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        let token = state.stream.consume()?;
        let region = state.curr_region();
        if let TokenKind::BlockLabel(label) = &token.kind {
            let label = label.as_ref().unwrap();
            let block = Block::reserve_with_name(ctx, label.clone(), region);
            let mut args = Vec::new();
            if state.stream.consume_if(TokenKind::Char('('))?.is_some() {
                loop {
                    if state.stream.consume_if(TokenKind::Char(')'))?.is_some() {
                        break;
                    }
                    let arg = Value::parse(ctx, state)?;
                    args.push(arg);

                    match state.stream.consume()?.kind {
                        TokenKind::Char(')') => break,
                        TokenKind::Char(',') => continue,
                        _ => {
                            return parse_error!(
                                token.span,
                                ParseErrorKind::InvalidToken(
                                    vec![token!(')'), token!(',')].into(),
                                    token.kind
                                )
                            )
                            .into();
                        }
                    }
                }
            }
            Ok(Successor::new(block, args))
        } else {
            parse_error!(token.span, ExpectBlockLabelInSuccessor(token.kind)).into()
        }
    }
}

impl Print for Successor {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> PrintResult<()> {
        let block_name = self.block.deref(&ctx.blocks).name(ctx);
        write!(state.buffer, "^{}", block_name)?;
        if !self.args.is_empty() {
            write!(state.buffer, "(")?;
            for (i, arg) in self.args.iter().enumerate() {
                arg.deref(&ctx.values).print(ctx, state)?;
                if i != self.args.len() - 1 {
                    write!(state.buffer, ", ")?;
                }
            }
            write!(state.buffer, ")")?;
        }
        Ok(())
    }
}

pub struct OpMetadata {
    /// The self ptr.
    self_ptr: ArenaPtr<OpObj>,
    /// The parent block of the operation.
    parent_block: Option<ArenaPtr<Block>>,
}

impl OpMetadata {
    pub fn new(self_ptr: ArenaPtr<OpObj>) -> Self {
        Self {
            self_ptr,
            parent_block: None,
        }
    }
}

/// The trait of all operations.
pub trait Op: Downcast + Print + Verify + DataFlow + ControlFlow + RegionInterface {
    /// Get the mnemonic of the type.
    fn mnemonic(&self) -> Mnemonic;

    /// Get the mnemonic of the type statically.
    fn mnemonic_static() -> Mnemonic
    where
        Self: Sized;

    /// Register the operation to the context.
    ///
    /// The [`Parse`](crate::core::parse::Parse) trait is not object-safe, so
    /// here just pass the parse function.
    fn register(ctx: &mut Context, parse_fn: OpParseFn)
    where
        Self: Sized;

    fn metadata(&self) -> &OpMetadata;

    fn metadata_mut(&mut self) -> &mut OpMetadata;

    /// Get the self ptr.
    fn self_ptr(&self) -> ArenaPtr<OpObj> { self.metadata().self_ptr }

    /// Get the parent block of the operation.
    fn parent_block(&self) -> Option<ArenaPtr<Block>> { self.metadata().parent_block }

    /// Set the parent block of the operation.
    fn set_parent_block(
        &mut self,
        parent_block: Option<ArenaPtr<Block>>,
    ) -> Option<ArenaPtr<Block>> {
        let old = self.metadata_mut().parent_block.take();
        self.metadata_mut().parent_block = parent_block;
        old
    }

    /// Get the parent region of the operation.
    ///
    /// If the operation has no parent block, the parent region will be `None`.
    fn parent_region(&self, ctx: &Context) -> Option<ArenaPtr<Region>> {
        self.parent_block().map(|ptr| {
            let block = ptr.deref(&ctx.blocks);
            block.parent_region()
        })
    }
}

impl_downcast!(Op);

pub struct OpObj(Box<dyn Op>);

impl<T> From<T> for OpObj
where
    T: Op,
{
    fn from(t: T) -> Self { OpObj(Box::new(t)) }
}

impl AsRef<dyn Op> for OpObj {
    fn as_ref(&self) -> &dyn Op { &*self.0 }
}

impl AsMut<dyn Op> for OpObj {
    fn as_mut(&mut self) -> &mut dyn Op { &mut *self.0 }
}

impl OpObj {
    /// Check if the type object is a concrete type.
    pub fn is_a<T: Op>(&self) -> bool { self.as_ref().is::<T>() }

    /// Try to downcast the type object to a concrete type.
    pub fn as_a<T: Op>(&self) -> Option<&T> { self.as_ref().downcast_ref() }

    /// Check if the type object implements a trait.
    pub fn impls<T: ?Sized + 'static>(&self, ctx: &Context) -> bool {
        self.as_ref().impls::<T>(&ctx.casters)
    }

    /// Try to cast the type object to another trait.
    pub fn cast_ref<T: ?Sized + 'static>(&self, ctx: &Context) -> Option<&T> {
        self.as_ref().cast_ref(&ctx.casters)
    }

    pub fn cast_mut<T: ?Sized + 'static>(&mut self, ctx: &Context) -> Option<&mut T> {
        self.as_mut().cast_mut(&ctx.casters)
    }
}

impl Parse for OpObj {
    type Item = ArenaPtr<OpObj>;

    /// The top-level parsing for an operation.
    ///
    /// This function will parse the operation result, push the names to the
    /// state, then parse the mnemonic and the dialect-specific text.
    ///
    /// e.g. for the oepration text below:
    /// ```text
    /// %0, %1 = dialect.agnostic_op %2, %3 : int<32>, int<32>
    /// ```
    ///
    /// The result part `%0, %1` will be saved as names, then the `=` will be
    /// consumed and the mnemonic will be parsed. According to the mnemonic,
    /// the parse function will be looked up from the context and called.
    ///
    /// The dialect-specific parse function should only parse the rest of the
    /// text.
    ///
    /// # Syntax
    ///
    /// ```text
    /// <result_name_list> `=` <mnemonic> <dialect_specific_text>
    /// ````
    /// 
    /// # Notes
    /// 
    /// The components of an operation needs to accept the corresponding `ArenaPtr<OpObj>`, and
    /// thus it is necessary to call `ctx.ops.reserve()` to get the `ArenaPtr<OpObj>` and then
    /// enter the parsing process. Of course, after the operation is constructed, the slot should
    /// be filled.
    fn parse(ctx: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        let mut result_names = Vec::new();
        let parent = state.curr_block();

        loop {
            let token = state.stream.peek()?;
            match token.kind {
                TokenKind::ValueName(_) => {
                    // eat the value name
                    let token = state.stream.consume()?;

                    if let TokenKind::ValueName(_) = token.kind {
                        result_names.push(token);
                    } else {
                        unreachable!();
                    }

                    // eat the next token, `=` or `,`
                    let token = state.stream.consume()?;
                    match token.kind {
                        TokenKind::Char(',') => continue,
                        TokenKind::Char('=') => break,
                        _ => {
                            return parse_error!(
                                token.span,
                                ParseErrorKind::InvalidToken(
                                    vec![token!(','), token!('=')].into(),
                                    token.kind
                                )
                            )
                            .into();
                        }
                    }
                }
                _ => break,
            }
        }

        let mnemonic = Mnemonic::parse(ctx, state)?;

        let parse_fn = ctx
            .dialects
            .get(mnemonic.primary())
            .unwrap_or_else(|| panic!("dialect {} not found: ", mnemonic.primary().as_str()))
            .get_op_parse_fn(&mnemonic)
            .unwrap_or_else(|| {
                panic!(
                    "op {}.{} not found",
                    mnemonic.primary().as_str(),
                    mnemonic.secondary().as_str()
                )
            });

        state.push_result_names(result_names);
        let op = parse_fn(ctx, state)?;

        if op.deref(&ctx.ops).as_ref().parent_block().is_none() {
            op.deref_mut(&mut ctx.ops).as_mut().set_parent_block(parent);
        }

        Ok(op)
    }
}

/// The parse function type of the operations.
///
/// The parse function should take the result builders and the parent block as
/// arguments and return the operation object.
pub type OpParseFn = ParseFn<ArenaPtr<OpObj>>;

impl Print for OpObj {
    /// Print the operation.
    ///
    /// This is actually symmetric to the parsing process.
    fn print(&self, ctx: &Context, state: &mut PrintState) -> PrintResult<()> {
        let num_results = self.as_ref().num_results();

        if num_results > 0 {
            for i in 0..num_results {
                if let Some(result) = self.as_ref().get_result(i) {
                    result.deref(&ctx.values).print(ctx, state)?;
                } else {
                    panic!("result {} not found", i);
                }
                if i != num_results - 1 {
                    write!(state.buffer, ", ")?;
                }
            }
            write!(state.buffer, " = ")?;
        }

        self.as_ref().mnemonic().print(ctx, state)?;
        write!(state.buffer, " ")?;
        self.as_ref().print(ctx, state)?;
        Ok(())
    }
}
