use std::collections::HashMap;

use downcast_rs::{impl_downcast, Downcast};
use intertrait::{cast::CastRef, CastFrom};

use crate::{support::storage::ArenaPtr, Region};

use super::{attribute::AttrObj, context::Context, mnemonic::Mnemonic, value::Value};

pub struct OpBase {
    attrs: HashMap<String, AttrObj>,
    results: Vec<ArenaPtr<Value>>,
    operands: Vec<ArenaPtr<Value>>,
    regions: Vec<ArenaPtr<Region>>,
    parent_region: Option<ArenaPtr<Region>>,
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

    pub fn parent_region(&self) -> Option<ArenaPtr<Region>> {
        self.parent_region
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

pub trait OpBuilder {
    fn build(self, ctx: &Context) -> OpObj;
}
