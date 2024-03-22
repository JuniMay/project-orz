use std::collections::HashMap;

use anyhow::Result;
use downcast_rs::{impl_downcast, Downcast};
use intertrait::{cast::CastRef, CastFrom};

use crate::{support::storage::ArenaPtr, Parse, Print, PrintState, Region, TokenStream};

use super::{
    attribute::AttrObj, block::Block, context::Context, mnemonic::Mnemonic, ty, value::Value,
};

pub struct OpBase {
    attrs: HashMap<String, AttrObj>,
    results: Vec<ArenaPtr<Value>>,
    operands: Vec<ArenaPtr<Value>>,
    regions: Vec<ArenaPtr<Region>>,
    parent_block: Option<ArenaPtr<Block>>,
}

impl Default for OpBase {
    fn default() -> Self {
        Self {
            attrs: HashMap::default(),
            results: Vec::default(),
            operands: Vec::default(),
            regions: Vec::default(),
            parent_block: None,
        }
    }
}

impl OpBase {
    pub fn results(&self) -> &[ArenaPtr<Value>] {
        &self.results
    }

    pub fn operands(&self) -> &[ArenaPtr<Value>] {
        &self.operands
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

    pub fn get_attr(&self, name: &str) -> Option<&AttrObj> {
        self.attrs.get(name)
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

    pub fn add_attr(&mut self, name: String, attr: AttrObj) -> Result<()> {
        if self.attrs.contains_key(&name) {
            anyhow::bail!("The attribute name is already used.");
        }
        self.attrs.insert(name, attr);
        Ok(())
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

    fn parse(arg: Self::Arg, ctx: &mut Context, stream: &mut TokenStream) -> Result<Self::Item> {
        todo!()
    }
}

impl Print for OpObj {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        todo!()
    }
}
