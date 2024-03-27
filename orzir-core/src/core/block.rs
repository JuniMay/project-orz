use std::fmt::Write;

use anyhow::{anyhow, Result};

use super::value::Value;
use crate::{
    core::parse::TokenKind, support::storage::ArenaPtr, Context, OpObj, Parse, Print, PrintState,
    Region, TokenStream, TyObj, Typed, Verify, VerifyInterfaces,
};

/// The block in the region.
///
/// The block does not store the operations, but represents the necessary
/// argument information.
#[derive(Debug)]
pub struct Block {
    /// Self ptr.
    self_ptr: ArenaPtr<Self>,
    /// Arguments of the block.
    args: Vec<ArenaPtr<Value>>,
    /// If this block is an entry.
    is_entry: bool,
    /// The parent region.
    parent_region: ArenaPtr<Region>,
}

impl VerifyInterfaces for Block {
    fn verify_interfaces(&self, _ctx: &Context) -> Result<()> { Ok(()) }
}

impl Verify for Block {
    fn verify(&self, ctx: &Context) -> Result<()> {
        for arg in &self.args {
            arg.deref(&ctx.values).verify(ctx)?;
        }
        Ok(())
    }
}

impl Block {
    /// Get the builder of the block.
    pub fn builder() -> BlockBuilder { BlockBuilder::default() }

    /// Get the name of the block.
    ///
    /// This will allocate a new name if the block does not have one.
    pub fn name(&self, ctx: &Context) -> String {
        let region = self.parent_region.deref(&ctx.regions);
        let name = region.block_names.borrow_mut().get(self.self_ptr);
        name
    }

    /// Set the name of the block.
    pub fn set_name(&self, ctx: &Context, name: String) -> Result<()> {
        let region = self.parent_region.deref(&ctx.regions);
        region.block_names.borrow_mut().set(self.self_ptr, name)
    }

    pub fn set_arg(
        &mut self,
        index: usize,
        arg: ArenaPtr<Value>,
    ) -> Result<Option<ArenaPtr<Value>>> {
        if index > self.args.len() {
            anyhow::bail!("index out of range");
        }
        if index == self.args.len() {
            self.args.push(arg);
            return Ok(None);
        }
        let old = std::mem::replace(&mut self.args[index], arg);
        Ok(Some(old))
    }

    pub fn num_args(&self) -> usize { self.args.len() }

    /// Get the arguments of the block.
    pub fn args(&self) -> &[ArenaPtr<Value>] { &self.args }

    /// Test if the block is an entry block.
    pub fn is_entry(&self) -> bool { self.is_entry }

    /// Reserve a unknown block with a name, if the name is already used, return
    /// the block.
    pub(crate) fn reserve_with_name(
        ctx: &mut Context,
        name: String,
        region: ArenaPtr<Region>,
    ) -> ArenaPtr<Block> {
        let region = region.deref(&ctx.regions);
        let self_ptr = region
            .block_names
            .borrow()
            .get_by_name(&name)
            .unwrap_or_else(|| ctx.blocks.reserve());
        region.block_names.borrow_mut().set(self_ptr, name).unwrap();
        self_ptr
    }

    /// Get the parent region of the block.
    pub fn parent_region(&self) -> ArenaPtr<Region> { self.parent_region }
}

/// A block builder.
///
/// This can be used to perform simple chained style block building.
#[derive(Debug, Default)]
pub struct BlockBuilder {
    /// The name of the block.
    name: Option<String>,
    /// If the block is an entry block.
    is_entry: Option<bool>,
    /// The parent region of the block.
    parent_region: Option<ArenaPtr<Region>>,
}

impl BlockBuilder {
    /// Set the if the block is an entry block.
    pub fn entry(mut self, is_entry: bool) -> Self {
        self.is_entry = Some(is_entry);
        self
    }

    /// Set the parent region of the block.
    pub fn parent_region(mut self, parent_region: ArenaPtr<Region>) -> Self {
        self.parent_region = Some(parent_region);
        self
    }

    /// Set the name of the block.
    pub fn name(mut self, name: String) -> Self {
        self.name = Some(name);
        self
    }

    /// Build the block.
    ///
    /// This will generate a new block, but will **NOT** add it to the layout.
    pub fn build(self, ctx: &mut Context) -> Result<ArenaPtr<Block>> {
        let parent_region = self.parent_region.ok_or_else(|| anyhow!("missing parent region"))?;
        // try to get the reference by the name first.
        let self_ptr = if let Some(name) = &self.name {
            parent_region
                .deref(&ctx.regions)
                .block_names
                .borrow()
                .get_by_name(name)
                .unwrap_or_else(|| ctx.blocks.reserve())
        } else {
            ctx.blocks.reserve()
        };
        let block = Block {
            self_ptr,
            args: Vec::new(),
            is_entry: self.is_entry.unwrap_or(false),
            parent_region,
        };
        if let Some(name) = self.name {
            block.set_name(ctx, name)?;
        }
        ctx.blocks.fill(self_ptr, block);
        Ok(self_ptr)
    }
}

impl Parse for Block {
    type Arg = BlockBuilder;
    type Item = ArenaPtr<Block>;

    fn parse(
        builder: Self::Arg,
        ctx: &mut Context,
        stream: &mut TokenStream,
    ) -> Result<Self::Item> {
        let block = builder.build(ctx)?;
        block
            .deref(&ctx.blocks)
            .parent_region
            .deref_mut(&mut ctx.regions)
            .layout_mut()
            .append_block(block);
        // parse the block arguments.

        let is_entry = block.deref(&ctx.blocks).is_entry();
        if !is_entry {
            let token = stream.consume()?;
            match token.kind {
                TokenKind::Char('(') => {
                    let mut cnt = 0;
                    // parse the arguments.
                    loop {
                        let token = stream.peek()?;
                        match &token.kind {
                            TokenKind::Char(')') => {
                                stream.consume()?;
                                break;
                            }
                            TokenKind::ValueName(ref name) => {
                                let name = name.clone();
                                // the argument ptr will be fetched in the builder.
                                let _arg = Value::parse((), ctx, stream)?;
                                stream.expect(TokenKind::Char(':'))?;
                                let ty = TyObj::parse((), ctx, stream)?;

                                // the `build` function will automatically add the argument to
                                // the block and set the index of the argument in the block.
                                let _arg = Value::block_argument_builder()
                                    .name(name)
                                    .block(block)
                                    .ty(ty)
                                    .index(cnt)
                                    .build(ctx)?;

                                cnt += 1;

                                if stream.consume_if(TokenKind::Char(','))?.is_none() {
                                    // end of the arguments.
                                    stream.expect(TokenKind::Char(')'))?;
                                    break;
                                }
                            }
                            _ => {
                                anyhow::bail!("unexpected token: {:?}", token.kind);
                            }
                        }
                    }
                    stream.expect(TokenKind::Char(':'))?;
                }
                TokenKind::Char(':') => {
                    // just exit.
                }
                _ => {
                    anyhow::bail!("unexpected token: {:?}", token.kind);
                }
            }
        }

        // parse the operations.
        loop {
            let token = stream.peek()?;
            match token.kind {
                TokenKind::ValueName(_) | TokenKind::Tokenized(_) => {
                    // parse an operation
                    let op = OpObj::parse(Some(block), ctx, stream)?;
                    block
                        .deref(&ctx.blocks)
                        .parent_region
                        .deref_mut(&mut ctx.regions)
                        .layout_mut()
                        .append_op(block, op);
                }
                TokenKind::BlockLabel(_) | TokenKind::Char('}') => {
                    // end of the block
                    break;
                }
                _ => {
                    anyhow::bail!("unexpected token: {:?}", token.kind);
                }
            }
        }

        Ok(block)
    }
}

impl Print for Block {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        if !self.is_entry() {
            state.write_indent()?;
            write!(state.buffer, "^{}", self.name(ctx))?;
            if self.args.is_empty() {
                write!(state.buffer, ":")?;
            } else {
                write!(state.buffer, "(")?;
                for (i, arg) in self.args.iter().enumerate() {
                    let arg = arg.deref(&ctx.values);
                    write!(state.buffer, "{}:", arg.name(ctx))?;
                    let ty = arg.ty(ctx);
                    ty.deref(&ctx.tys).print(ctx, state)?;
                    if i != self.args.len() - 1 {
                        write!(state.buffer, ", ")?;
                    }
                }
                write!(state.buffer, "):")?;
            }
            writeln!(state.buffer)?;
        }

        let region = self.parent_region.deref(&ctx.regions);

        state.indent();
        for op in region.layout().iter_ops(self.self_ptr) {
            state.write_indent()?;
            op.deref(&ctx.ops).print(ctx, state)?;
            writeln!(state.buffer)?;
        }
        state.dedent();

        Ok(())
    }
}
