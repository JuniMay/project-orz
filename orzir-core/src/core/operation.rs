use std::collections::HashMap;

use anyhow::Result;
use downcast_rs::{impl_downcast, Downcast};
use intertrait::{cast::CastRef, CastFrom};

use crate::{support::storage::ArenaPtr, Parse, Print, PrintState, Region, TokenStream};

use super::{
    block::Block,
    context::Context,
    mnemonic::Mnemonic,
    parse::{ParseFn, TokenKind},
    value::{OpResultBuilder, Value},
};

#[derive(Default)]
pub struct OpBase {
    results: Vec<ArenaPtr<Value>>,
    operands: Vec<ArenaPtr<Value>>,
    regions: Vec<ArenaPtr<Region>>,
    parent_block: Option<ArenaPtr<Block>>,
}

impl OpBase {
    pub fn results(&self) -> &[ArenaPtr<Value>] {
        &self.results
    }

    pub fn operands(&self) -> &[ArenaPtr<Value>] {
        &self.operands
    }

    pub fn regions(&self) -> &[ArenaPtr<Region>] {
        &self.regions
    }

    pub fn set_results(&mut self, results: Vec<ArenaPtr<Value>>) {
        self.results = results;
    }

    pub fn set_operands(&mut self, operands: Vec<ArenaPtr<Value>>) {
        self.operands = operands;
    }

    pub fn get_result(&self, index: usize) -> Option<ArenaPtr<Value>> {
        self.results.get(index).copied()
    }

    pub fn get_operand(&self, index: usize) -> Option<ArenaPtr<Value>> {
        self.operands.get(index).copied()
    }

    pub fn get_region(&self, index: usize) -> Option<ArenaPtr<Region>> {
        self.regions.get(index).copied()
    }

    pub fn add_result(&mut self, result: ArenaPtr<Value>) -> usize {
        self.results.push(result);
        self.results.len() - 1
    }

    pub fn add_operand(&mut self, operand: ArenaPtr<Value>) -> usize {
        self.operands.push(operand);
        self.operands.len() - 1
    }

    pub fn add_region(&mut self, region: ArenaPtr<Region>) -> usize {
        self.regions.push(region);
        self.regions.len() - 1
    }

    pub fn parent_block(&self) -> Option<ArenaPtr<Block>> {
        self.parent_block
    }

    pub fn set_parent_block(&mut self, parent_block: ArenaPtr<Block>) {
        self.parent_block = Some(parent_block);
    }

    pub fn parent_region(&self, ctx: &Context) -> Option<ArenaPtr<Region>> {
        self.parent_block.map(|ptr| {
            let block = ptr.deref(&ctx.blocks);
            block.parent_region()
        })
    }
}

pub trait Op: Downcast + CastFrom {
    /// Get the mnemonic of the type.
    fn mnemonic(&self, ctx: &Context) -> Mnemonic;
    /// Get the mnemonic of the type statically.
    fn mnemonic_static(ctx: &Context) -> Mnemonic
    where
        Self: Sized;

    /// Get the operation base.
    fn as_base(&self) -> &OpBase;

    /// Get the mutable operation base.
    fn as_base_mut(&mut self) -> &mut OpBase;
}

impl_downcast!(Op);

pub struct OpObj(Box<dyn Op>);

impl<T> From<T> for OpObj
where
    T: Op,
{
    fn from(t: T) -> Self {
        OpObj(Box::new(t))
    }
}

impl OpObj {
    /// Get the inside trait object.
    pub fn as_inner(&self) -> &dyn Op {
        &*self.0
    }

    pub fn as_inner_mut(&mut self) -> &mut dyn Op {
        &mut *self.0
    }

    /// Check if the type object is a concrete type.
    pub fn is_a<T: Op>(&self) -> bool {
        self.as_inner().is::<T>()
    }

    /// Try to downcast the type object to a concrete type.
    pub fn as_a<T: Op>(&self) -> Option<&T> {
        self.as_inner().downcast_ref()
    }

    /// Check if the type object implements a trait.
    pub fn impls<T: Op + ?Sized>(&self) -> bool {
        self.as_inner().impls::<T>()
    }

    /// Try to cast the type object to another trait.
    pub fn cast<T: Op + ?Sized>(&self) -> Option<&T> {
        self.as_inner().cast()
    }
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
            .expect("dialect not registered")
            .get_op_parse_fn(&mnemonic)
            .expect("op not registered");

        parse_fn((result_builders, parent), ctx, stream)
    }
}

pub type OpParseFn = ParseFn<(Vec<OpResultBuilder>, Option<ArenaPtr<Block>>), ArenaPtr<OpObj>>;

impl Print for OpObj {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        todo!()
    }
}
