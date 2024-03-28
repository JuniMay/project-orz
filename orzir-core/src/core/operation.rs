use std::fmt::Write;

use anyhow::Result;
use downcast_rs::{impl_downcast, Downcast};

use super::{
    block::Block,
    context::Context,
    mnemonic::Mnemonic,
    parse::{ParseFn, ParseState, TokenKind},
    value::{OpResultBuilder, Value},
};
use crate::{
    support::{
        cast::{CastMut, CastRef},
        storage::ArenaPtr,
    },
    Parse, Print, PrintState, Region, TyObj, Typed, Verify,
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

impl Parse for Successor {
    type Arg = ArenaPtr<Region>;
    type Item = Successor;

    /// Parse the successor.
    ///
    /// # Syntax
    ///
    /// ```text
    /// <block_label> `(` <arg_name_list> `)`
    /// ```
    fn parse(region: Self::Arg, ctx: &mut Context, state: &mut ParseState) -> Result<Self::Item> {
        let token = state.stream.consume()?;
        if let TokenKind::BlockLabel(label) = &token.kind {
            let block = Block::reserve_with_name(ctx, label.clone(), region);
            let mut args = Vec::new();
            if state.stream.consume_if(TokenKind::Char('('))?.is_some() {
                loop {
                    if state.stream.consume_if(TokenKind::Char(')'))?.is_some() {
                        break;
                    }
                    let arg = Value::parse((), ctx, state)?;
                    args.push(arg);

                    match state.stream.consume()?.kind {
                        TokenKind::Char(')') => break,
                        TokenKind::Char(',') => continue,
                        _ => anyhow::bail!("expected ')' or ','"),
                    }
                }
            }
            Ok(Successor::new(block, args))
        } else {
            anyhow::bail!("expected block label");
        }
    }
}

impl Print for Successor {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
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
pub trait Op: Downcast + Print + Verify {
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
    ) -> Result<Option<ArenaPtr<Block>>> {
        let old = self.metadata_mut().parent_block.take();
        self.metadata_mut().parent_block = parent_block;
        Ok(old)
    }

    /// Get the number of operands.
    fn num_operands(&self) -> usize;

    /// Get the number of results.
    fn num_results(&self) -> usize;

    /// Get the number of regions.
    fn num_regions(&self) -> usize;

    /// Get the number of successors.
    fn num_successors(&self) -> usize;

    /// Get the operand by index.
    fn get_operand(&self, index: usize) -> Option<ArenaPtr<Value>>;

    /// Get the result by index.
    fn get_result(&self, index: usize) -> Option<ArenaPtr<Value>>;

    /// Get the region by index.
    fn get_region(&self, index: usize) -> Option<ArenaPtr<Region>>;

    /// Get the successor by index.
    fn get_successor(&self, index: usize) -> Option<&Successor>;

    /// Get the operands
    fn operands(&self) -> Vec<ArenaPtr<Value>> {
        let mut operands = Vec::new();
        for i in 0..self.num_operands() {
            operands.push(
                self.get_operand(i)
                    .unwrap_or_else(|| panic!("operand at index {} not found", i)),
            );
        }
        operands
    }

    /// Get the results
    fn results(&self) -> Vec<ArenaPtr<Value>> {
        let mut results = Vec::new();
        for i in 0..self.num_results() {
            results.push(
                self.get_result(i).unwrap_or_else(|| panic!("result at index {} not found", i)),
            );
        }
        results
    }

    /// Get the regions
    fn regions(&self) -> Vec<ArenaPtr<Region>> {
        let mut regions = Vec::new();
        for i in 0..self.num_regions() {
            regions.push(
                self.get_region(i).unwrap_or_else(|| panic!("region at index {} not found", i)),
            );
        }
        regions
    }

    /// Get the successors
    fn successors(&self) -> Vec<&Successor> {
        let mut successors = Vec::new();
        for i in 0..self.num_successors() {
            successors.push(
                self.get_successor(i)
                    .unwrap_or_else(|| panic!("successor at index {} not found", i)),
            );
        }
        successors
    }

    /// Set the operand by index.
    ///
    /// If success, return the original operand, if any. Otherwise, return an
    /// error.
    fn set_operand(
        &mut self,
        index: usize,
        operand: ArenaPtr<Value>,
    ) -> Result<Option<ArenaPtr<Value>>>;

    /// Set the result by index.
    ///
    /// If success, return the original result, if any. Otherwise, return an
    /// error.
    fn set_result(
        &mut self,
        index: usize,
        result: ArenaPtr<Value>,
    ) -> Result<Option<ArenaPtr<Value>>>;

    /// Set the region by index.
    ///
    /// If success, return the original region, if any. Otherwise, return an
    /// error.
    fn set_region(
        &mut self,
        index: usize,
        region: ArenaPtr<Region>,
    ) -> Result<Option<ArenaPtr<Region>>>;

    /// Set the successor by index.
    ///
    /// If success, return the original successor, if any. Otherwise, return an
    /// error.
    fn set_successor(&mut self, index: usize, successor: Successor) -> Result<Option<Successor>>;

    /// Get the types of operands.
    fn operand_tys(&self, ctx: &Context) -> Vec<ArenaPtr<TyObj>> {
        let mut tys = Vec::new();
        for i in 0..self.num_operands() {
            if let Some(operand) = self.get_operand(i) {
                tys.push(operand.deref(&ctx.values).ty(ctx));
            } else {
                panic!("operand {} not found", i);
            }
        }
        tys
    }

    /// Get the types of the results.
    fn result_tys(&self, ctx: &Context) -> Vec<ArenaPtr<TyObj>> {
        let mut tys = Vec::new();
        for i in 0..self.num_results() {
            if let Some(result) = self.get_result(i) {
                tys.push(result.deref(&ctx.values).ty(ctx));
            } else {
                panic!("result {} not found", i);
            }
        }
        tys
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
    type Arg = Option<ArenaPtr<Block>>;
    type Item = ArenaPtr<OpObj>;

    /// The top-level parsing for an operation.
    ///
    /// This function will parse the operation result, generate the
    /// corresponding builders and pass them to the operation parse
    /// function.
    ///
    /// e.g. for the oepration text below:
    /// ```text
    /// %0, %1 = dialect.agnostic_op %2, %3 : int<32>, int<32>
    /// ```
    ///
    /// The result part `%0, %1` will be parsed and into [`OpResultBuilder`]s,
    /// then the `=` will be consumed and the mnemonic will be parsed.
    /// According to the mnemonic, the parse function will be looked up from
    /// the context and called.
    ///
    /// The dialect-specific parse function should only parse the rest of the
    /// text.
    ///
    /// # Syntax
    ///
    /// ```text
    /// <result_name_list> `=` <mnemonic> <dialect_specific_text>
    /// ````
    fn parse(parent: Self::Arg, ctx: &mut Context, state: &mut ParseState) -> Result<Self::Item> {
        let mut result_builders = Vec::new();

        loop {
            let token = state.stream.peek()?;
            match token.kind {
                TokenKind::ValueName(ref name) => {
                    let builder =
                        Value::op_result_builder().name(name.clone()).index(result_builders.len());
                    result_builders.push(builder);
                    // eat the value name
                    let _ = state.stream.consume()?;
                    // eat the next token, `=` or `,`
                    let token = state.stream.consume()?;
                    match token.kind {
                        TokenKind::Char(',') => continue,
                        TokenKind::Char('=') => break,
                        _ => anyhow::bail!("invalid token: {:?}, expected ',' or '='", token.kind),
                    }
                }
                _ => break,
            }
        }

        let mnemonic = Mnemonic::parse((), ctx, state)?;

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

        let op = parse_fn(result_builders, ctx, state)?;

        if op.deref(&ctx.ops).as_ref().parent_block().is_none() {
            op.deref_mut(&mut ctx.ops).as_mut().set_parent_block(parent)?;
        }

        Ok(op)
    }
}

/// The parse function type of the operations.
///
/// The parse function should take the result builders and the parent block as
/// arguments and return the operation object.
pub type OpParseFn = ParseFn<Vec<OpResultBuilder>, ArenaPtr<OpObj>>;

impl Print for OpObj {
    /// Print the operation.
    ///
    /// This is actually symmetric to the parsing process.
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
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
        self.as_ref().print(ctx, state)?;
        Ok(())
    }
}
