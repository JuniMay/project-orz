use std::fmt::Write;

use anyhow::Result;
use downcast_rs::{impl_downcast, Downcast};

use super::{
    block::Block,
    context::Context,
    mnemonic::Mnemonic,
    parse::{ParseFn, TokenKind},
    value::{OpResultBuilder, Value},
};
use crate::{
    support::{
        cast::{CastMut, CastRef},
        storage::ArenaPtr,
    },
    Parse, Print, PrintState, Region, TokenStream, TyObj, Typed, Verify,
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

/// The common struct of all operations.
///
/// All operation should wrap this struct to provide basic operations.
pub struct OpBase {
    /// The self ptr.
    self_ptr: ArenaPtr<OpObj>,
    /// The results of the operation.
    results: Vec<ArenaPtr<Value>>,
    /// The operands of the operation.
    operands: Vec<ArenaPtr<Value>>,
    /// The regions attached to the operation.
    regions: Vec<ArenaPtr<Region>>,
    /// The successors of the operation.
    ///
    /// Successors represents the control-flow destinations.
    successors: Vec<Successor>,
    /// The parent block of the operation.
    ///
    /// TODO: Make sure this field is always maintained.
    parent_block: Option<ArenaPtr<Block>>,
}

impl OpBase {
    pub fn new(self_ptr: ArenaPtr<OpObj>) -> Self {
        Self {
            self_ptr,
            results: Vec::new(),
            operands: Vec::new(),
            regions: Vec::new(),
            successors: Vec::new(),
            parent_block: None,
        }
    }

    fn self_ptr(&self) -> ArenaPtr<OpObj> { self.self_ptr }

    /// Get the results of the operation.
    fn results(&self) -> &[ArenaPtr<Value>] { &self.results }

    /// Get the operands of the operation.
    fn operands(&self) -> &[ArenaPtr<Value>] { &self.operands }

    /// Get the successors of the operation.
    fn successors(&self) -> &[Successor] { &self.successors }

    /// Collect the types of the operands.
    fn operand_tys(&self, ctx: &Context) -> Vec<ArenaPtr<TyObj>> {
        self.operands.iter().map(|ptr| ptr.deref(&ctx.values).ty(ctx)).collect()
    }

    /// Collect the types of the results.
    fn result_tys(&self, ctx: &Context) -> Vec<ArenaPtr<TyObj>> {
        self.results.iter().map(|ptr| ptr.deref(&ctx.values).ty(ctx)).collect()
    }

    /// Get the regions of the operation.
    fn regions(&self) -> &[ArenaPtr<Region>] { &self.regions }

    /// Get a result by index.
    fn get_result(&self, index: usize) -> Option<ArenaPtr<Value>> {
        self.results.get(index).copied()
    }

    /// Get an operand by index.
    fn get_operand(&self, index: usize) -> Option<ArenaPtr<Value>> {
        self.operands.get(index).copied()
    }

    /// Get a region by index.
    fn get_region(&self, index: usize) -> Option<ArenaPtr<Region>> {
        self.regions.get(index).copied()
    }

    /// Get a successor by index.
    fn get_successor(&self, index: usize) -> Option<&Successor> { self.successors.get(index) }

    /// Add an operand to the operation.
    fn add_operand(&mut self, operand: ArenaPtr<Value>) -> usize {
        self.operands.push(operand);
        self.operands.len() - 1
    }

    /// Add a successor to the operation.
    fn add_successor(&mut self, successor: Successor) { self.successors.push(successor); }

    /// Add a result to the operation.
    ///
    /// This should only be used by the
    /// [`OpResultBuilder`](crate::core::value::OpResultBuilder), which will
    /// automatically set the result index.
    fn add_result(&mut self, result: ArenaPtr<Value>) -> usize {
        self.results.push(result);
        self.results.len() - 1
    }

    /// Add a region to the operation.
    ///
    /// This should only be used by the
    /// [`RegionBuilder`](crate::core::region::RegionBuilder), which will
    /// automatically set the region index.
    fn add_region(&mut self, region: ArenaPtr<Region>) -> usize {
        self.regions.push(region);
        self.regions.len() - 1
    }

    fn set_operand(
        &mut self,
        index: usize,
        operand: ArenaPtr<Value>,
    ) -> Result<Option<ArenaPtr<Value>>> {
        if index > self.operands.len() {
            anyhow::bail!("operand index out of range");
        }
        if index == self.operands.len() {
            self.operands.push(operand);
            return Ok(None);
        }
        Ok(std::mem::replace(&mut self.operands[index], operand).into())
    }

    fn set_result(
        &mut self,
        index: usize,
        result: ArenaPtr<Value>,
    ) -> Result<Option<ArenaPtr<Value>>> {
        if index > self.results.len() {
            anyhow::bail!("result index out of range");
        }
        if index == self.results.len() {
            self.results.push(result);
            return Ok(None);
        }
        Ok(std::mem::replace(&mut self.results[index], result).into())
    }

    fn set_region(
        &mut self,
        index: usize,
        region: ArenaPtr<Region>,
    ) -> Result<Option<ArenaPtr<Region>>> {
        if index > self.regions.len() {
            anyhow::bail!("region index out of range");
        }
        if index == self.regions.len() {
            self.regions.push(region);
            return Ok(None);
        }
        Ok(std::mem::replace(&mut self.regions[index], region).into())
    }

    fn set_successor(&mut self, index: usize, successor: Successor) -> Result<Option<Successor>> {
        if index > self.successors.len() {
            anyhow::bail!("successor index out of range");
        }
        if index == self.successors.len() {
            self.successors.push(successor);
            return Ok(None);
        }
        Ok(std::mem::replace(&mut self.successors[index], successor).into())
    }

    /// Get the parent block of the operation.
    fn parent_block(&self) -> Option<ArenaPtr<Block>> { self.parent_block }

    /// Set the parent block of the operation.
    fn set_parent_block(&mut self, parent_block: Option<ArenaPtr<Block>>) {
        self.parent_block = parent_block;
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

    /// Get the operation base.
    fn as_base(&self) -> &OpBase;

    /// Get the mutable operation base.
    fn as_base_mut(&mut self) -> &mut OpBase;

    /// Register the operation to the context.
    ///
    /// The [`Parse`](crate::core::parse::Parse) trait is not object-safe, so
    /// here just pass the parse function.
    fn register(ctx: &mut Context, parse_fn: OpParseFn)
    where
        Self: Sized;

    /// Get the self ptr.
    fn self_ptr(&self) -> ArenaPtr<OpObj> { self.as_base().self_ptr() }

    /// Get the types of operands.
    fn operand_tys(&self, ctx: &Context) -> Vec<ArenaPtr<TyObj>> { self.as_base().operand_tys(ctx) }

    /// Get the types of the results.
    fn result_tys(&self, ctx: &Context) -> Vec<ArenaPtr<TyObj>> { self.as_base().result_tys(ctx) }

    /// Get the regions of the operation.
    fn regions(&self) -> &[ArenaPtr<Region>] { self.as_base().regions() }

    /// Get the results of the operation.
    fn results(&self) -> &[ArenaPtr<Value>] { self.as_base().results() }

    /// Get the operands of the operation.
    fn operands(&self) -> &[ArenaPtr<Value>] { self.as_base().operands() }

    /// Get the successors of the operation.
    fn successors(&self) -> &[Successor] { self.as_base().successors() }

    /// Get the number of operands.
    fn num_operands(&self) -> usize { self.as_base().operands().len() }

    /// Get the number of results.
    fn num_results(&self) -> usize { self.as_base().results().len() }

    /// Get the number of regions.
    fn num_regions(&self) -> usize { self.as_base().regions().len() }

    /// Get the number of successors.
    fn num_successors(&self) -> usize { self.as_base().successors().len() }

    /// Get the operand by index.
    fn get_operand(&self, index: usize) -> Option<ArenaPtr<Value>> {
        self.as_base().get_operand(index)
    }

    /// Get the result by index.
    fn get_result(&self, index: usize) -> Option<ArenaPtr<Value>> {
        self.as_base().get_result(index)
    }

    /// Get the region by index.
    fn get_region(&self, index: usize) -> Option<ArenaPtr<Region>> {
        self.as_base().get_region(index)
    }

    /// Get the successor by index.
    fn get_successor(&self, index: usize) -> Option<&Successor> {
        self.as_base().get_successor(index)
    }

    /// Add an operand to the operation.
    fn add_operand(&mut self, operand: ArenaPtr<Value>) -> usize {
        self.as_base_mut().add_operand(operand)
    }

    /// Add a successor to the operation.
    fn add_successor(&mut self, successor: Successor) {
        self.as_base_mut().add_successor(successor)
    }

    /// Add a result to the operation.
    fn add_result(&mut self, result: ArenaPtr<Value>) -> usize {
        self.as_base_mut().add_result(result)
    }

    /// Add a region to the operation.
    fn add_region(&mut self, region: ArenaPtr<Region>) -> usize {
        self.as_base_mut().add_region(region)
    }

    /// Set the operand by index.
    ///
    /// If success, return the original operand, if any. Otherwise, return an
    /// error.
    fn set_operand(
        &mut self,
        index: usize,
        operand: ArenaPtr<Value>,
    ) -> Result<Option<ArenaPtr<Value>>> {
        self.as_base_mut().set_operand(index, operand)
    }

    /// Set the result by index.
    ///
    /// If success, return the original result, if any. Otherwise, return an
    /// error.
    fn set_result(
        &mut self,
        index: usize,
        result: ArenaPtr<Value>,
    ) -> Result<Option<ArenaPtr<Value>>> {
        self.as_base_mut().set_result(index, result)
    }

    /// Set the region by index.
    ///
    /// If success, return the original region, if any. Otherwise, return an
    /// error.
    fn set_region(
        &mut self,
        index: usize,
        region: ArenaPtr<Region>,
    ) -> Result<Option<ArenaPtr<Region>>> {
        self.as_base_mut().set_region(index, region)
    }

    /// Set the successor by index.
    ///
    /// If success, return the original successor, if any. Otherwise, return an
    /// error.
    fn set_successor(&mut self, index: usize, successor: Successor) -> Result<Option<Successor>> {
        self.as_base_mut().set_successor(index, successor)
    }

    /// Get the parent block of the operation.
    fn parent_block(&self) -> Option<ArenaPtr<Block>> { self.as_base().parent_block() }

    /// Set the parent block of the operation.
    fn set_parent_block(&mut self, parent_block: Option<ArenaPtr<Block>>) {
        self.as_base_mut().set_parent_block(parent_block);
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

        if op.deref(&ctx.ops).as_ref().as_base().parent_block().is_none() {
            op.deref_mut(&mut ctx.ops).as_mut().as_base_mut().set_parent_block(parent);
        }

        Ok(op)
    }
}

/// The parse function type of the operations.
///
/// The parse function should take the result builders and the parent block as
/// arguments and return the operation object.
pub type OpParseFn = ParseFn<(Vec<OpResultBuilder>, Option<ArenaPtr<Block>>), ArenaPtr<OpObj>>;

impl Print for OpObj {
    /// Print the operation.
    ///
    /// This is actually symmetric to the parsing process.
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        let results = self.as_ref().as_base().results();

        if !results.is_empty() {
            for (i, result) in results.iter().enumerate() {
                result.deref(&ctx.values).print(ctx, state)?;
                if i != results.len() - 1 {
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
