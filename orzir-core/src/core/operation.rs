use std::fmt::Write;

use anyhow::Result;
use downcast_rs::{impl_downcast, Downcast};
use intertrait::{cast::CastRef, CastFrom};

use super::{
    block::Block,
    context::Context,
    mnemonic::Mnemonic,
    parse::{ParseFn, TokenKind},
    value::{OpResultBuilder, Value},
};
use crate::{
    support::storage::ArenaPtr, Parse, Print, PrintState, Region, TokenStream, TypeObj, Typed,
};

pub struct Successor {
    block: ArenaPtr<Block>,
    args: Vec<ArenaPtr<Value>>,
}

impl Successor {
    pub fn new(block: ArenaPtr<Block>, args: Vec<ArenaPtr<Value>>) -> Self { Self { block, args } }

    pub fn block(&self) -> ArenaPtr<Block> { self.block }

    pub fn args(&self) -> &[ArenaPtr<Value>] { &self.args }
}

impl Parse for Successor {
    type Arg = ArenaPtr<Region>;
    type Item = Successor;

    fn parse(region: Self::Arg, ctx: &mut Context, stream: &mut TokenStream) -> Result<Self::Item> {
        let token = stream.consume()?;
        if let TokenKind::BlockLabel(label) = &token.kind {
            let block = Block::reserve_with_name(ctx, label.clone(), region);
            let mut args = Vec::new();
            if stream.consume_if(TokenKind::Char('('))?.is_some() {
                loop {
                    if stream.consume_if(TokenKind::Char(')'))?.is_some() {
                        break;
                    }
                    let arg = Value::parse((), ctx, stream)?;
                    args.push(arg);

                    match stream.consume()?.kind {
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

#[derive(Default)]
pub struct OpBase {
    results: Vec<ArenaPtr<Value>>,
    operands: Vec<ArenaPtr<Value>>,
    regions: Vec<ArenaPtr<Region>>,
    successors: Vec<Successor>,
    parent_block: Option<ArenaPtr<Block>>,
}

impl OpBase {
    /// Get the results of the operation.
    pub fn results(&self) -> &[ArenaPtr<Value>] { &self.results }

    /// Get the operands of the operation.
    pub fn operands(&self) -> &[ArenaPtr<Value>] { &self.operands }

    /// Get the successors of the operation.
    pub fn successors(&self) -> &[Successor] { &self.successors }

    /// Collect the types of the operands.
    pub fn operand_types(&self, ctx: &Context) -> Vec<ArenaPtr<TypeObj>> {
        self.operands.iter().map(|ptr| ptr.deref(&ctx.values).ty(ctx)).collect()
    }

    /// Collect the types of the results.
    pub fn result_types(&self, ctx: &Context) -> Vec<ArenaPtr<TypeObj>> {
        self.results.iter().map(|ptr| ptr.deref(&ctx.values).ty(ctx)).collect()
    }

    /// Get the regions of the operation.
    pub fn regions(&self) -> &[ArenaPtr<Region>] { &self.regions }

    /// Set the results of the operation.
    ///
    /// This will replace the original results and return the original results.
    pub fn set_results(&mut self, results: Vec<ArenaPtr<Value>>) -> Vec<ArenaPtr<Value>> {
        std::mem::replace(&mut self.results, results)
    }

    /// Set the operands of the operation.
    ///
    /// This will replace the original operands and return the original
    /// operands.
    pub fn set_operands(&mut self, operands: Vec<ArenaPtr<Value>>) -> Vec<ArenaPtr<Value>> {
        std::mem::replace(&mut self.operands, operands)
    }

    /// Get a result by index.
    pub fn get_result(&self, index: usize) -> Option<ArenaPtr<Value>> {
        self.results.get(index).copied()
    }

    /// Get an operand by index.
    pub fn get_operand(&self, index: usize) -> Option<ArenaPtr<Value>> {
        self.operands.get(index).copied()
    }

    /// Get a region by index.
    pub fn get_region(&self, index: usize) -> Option<ArenaPtr<Region>> {
        self.regions.get(index).copied()
    }

    /// Get a successor by index.
    pub fn get_successor(&self, index: usize) -> Option<&Successor> { self.successors.get(index) }

    /// Add an operand to the operation.
    pub fn add_operand(&mut self, operand: ArenaPtr<Value>) -> usize {
        self.operands.push(operand);
        self.operands.len() - 1
    }

    pub fn add_successor(&mut self, successor: Successor) { self.successors.push(successor); }

    /// Add a result to the operation.
    ///
    /// This should only be used by the
    /// [`OpResultBuilder`](crate::core::value::OpResultBuilder), which will
    /// automatically set the result index.
    pub(crate) fn add_result(&mut self, result: ArenaPtr<Value>) -> usize {
        self.results.push(result);
        self.results.len() - 1
    }

    /// Add a region to the operation.
    ///
    /// This should only be used by the
    /// [`RegionBuilder`](crate::core::region::RegionBuilder), which will
    /// automatically set the region index.
    pub(crate) fn add_region(&mut self, region: ArenaPtr<Region>) -> usize {
        self.regions.push(region);
        self.regions.len() - 1
    }

    /// Get the parent block of the operation.
    pub fn parent_block(&self) -> Option<ArenaPtr<Block>> { self.parent_block }

    /// Set the parent block of the operation.
    pub fn set_parent_block(&mut self, parent_block: Option<ArenaPtr<Block>>) {
        self.parent_block = parent_block;
    }

    /// Get the parent region of the operation.
    pub fn parent_region(&self, ctx: &Context) -> Option<ArenaPtr<Region>> {
        self.parent_block.map(|ptr| {
            let block = ptr.deref(&ctx.blocks);
            block.parent_region()
        })
    }
}

pub trait Op: Downcast + CastFrom + Print {
    /// Get the mnemonic of the type.
    fn mnemonic(&self) -> Mnemonic;
    /// Get the mnemonic of the type statically.
    fn mnemonic_static() -> Mnemonic
    where
        Self: Sized;

    /// Get the operation base.
    fn as_base(&self) -> &OpBase;

    /// Get the mutable operation base.
    fn as_base_mut(&mut self) -> &mut OpBase;

    fn register(ctx: &mut Context, parse_fn: OpParseFn)
    where
        Self: Sized,
    {
        let mnemonic = Self::mnemonic_static();
        ctx.dialects.get_mut(mnemonic.primary()).unwrap().add_op(mnemonic, parse_fn);
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

impl OpObj {
    /// Get the inside trait object.
    pub fn as_inner(&self) -> &dyn Op { &*self.0 }

    pub fn as_inner_mut(&mut self) -> &mut dyn Op { &mut *self.0 }

    /// Check if the type object is a concrete type.
    pub fn is_a<T: Op>(&self) -> bool { self.as_inner().is::<T>() }

    /// Try to downcast the type object to a concrete type.
    pub fn as_a<T: Op>(&self) -> Option<&T> { self.as_inner().downcast_ref() }

    /// Check if the type object implements a trait.
    pub fn impls<T: Op + ?Sized>(&self) -> bool { self.as_inner().impls::<T>() }

    /// Try to cast the type object to another trait.
    pub fn cast<T: Op + ?Sized>(&self) -> Option<&T> { self.as_inner().cast() }
}

impl Parse for OpObj {
    type Arg = Option<ArenaPtr<Block>>;
    type Item = ArenaPtr<OpObj>;

    fn parse(parent: Self::Arg, ctx: &mut Context, stream: &mut TokenStream) -> Result<Self::Item> {
        let mut result_builders = Vec::new();

        loop {
            let token = stream.peek()?;
            match token.kind {
                TokenKind::ValueName(ref name) => {
                    let builder = Value::op_result_builder().name(name.clone());
                    result_builders.push(builder);
                    // eat the value name
                    let _ = stream.consume()?;
                    // eat the next token, `=` or `,`
                    let token = stream.consume()?;
                    match token.kind {
                        TokenKind::Char(',') => continue,
                        TokenKind::Char('=') => break,
                        _ => anyhow::bail!("invalid token: {:?}, expected ',' or '='", token.kind),
                    }
                }
                _ => break,
            }
        }

        let mnemonic = Mnemonic::parse((), ctx, stream)?;

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

        let op = parse_fn((result_builders, parent), ctx, stream)?;

        if op.deref(&ctx.ops).as_inner().as_base().parent_block().is_none() {
            op.deref_mut(&mut ctx.ops).as_inner_mut().as_base_mut().set_parent_block(parent);
        }

        Ok(op)
    }
}

pub type OpParseFn = ParseFn<(Vec<OpResultBuilder>, Option<ArenaPtr<Block>>), ArenaPtr<OpObj>>;

impl Print for OpObj {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        let results = self.as_inner().as_base().results();

        if !results.is_empty() {
            for (i, result) in results.iter().enumerate() {
                result.deref(&ctx.values).print(ctx, state)?;
                if i != results.len() - 1 {
                    write!(state.buffer, ", ")?;
                }
            }
            write!(state.buffer, " = ")?;
        }

        self.as_inner().mnemonic().print(ctx, state)?;
        self.as_inner().print(ctx, state)?;
        Ok(())
    }
}
