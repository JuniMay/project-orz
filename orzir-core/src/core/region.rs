use anyhow::{anyhow, Result};
use std::fmt::Write;
use std::{cell::RefCell, rc::Rc};

use crate::{
    core::parse::TokenKind, support::storage::ArenaPtr, Context, Parse, Print, PrintState,
    TokenStream,
};

use super::{
    block::Block,
    layout::Layout,
    operation::OpObj,
    symbol::{NameManager, SymbolTable, SymbolTableOwned},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RegionKind {
    Graph,
    SsaCfg,
    Unknown,
}

/// A region in the IR.
pub struct Region {
    /// The self ptr.
    self_ptr: ArenaPtr<Self>,
    /// The kind of the region.
    kind: RegionKind,
    /// The layout of the region.
    layout: Layout,
    /// The symbol table of the region.
    symbol_table: SymbolTableOwned,
    /// The block names of the region.
    pub(crate) block_names: RefCell<NameManager<Block>>,
    /// The parent operation of the region.
    parent_op: ArenaPtr<OpObj>,
    /// The index of the region in the parent operation.
    index: usize,
}

#[derive(Debug, Default)]
pub struct RegionBuilder {
    kind: Option<RegionKind>,
    parent_op: Option<ArenaPtr<OpObj>>,
}

impl Region {
    pub fn layout(&self) -> &Layout {
        &self.layout
    }

    pub fn layout_mut(&mut self) -> &mut Layout {
        &mut self.layout
    }

    pub fn kind(&self) -> RegionKind {
        self.kind
    }

    pub fn set_kind(&mut self, kind: RegionKind) {
        self.kind = kind;
    }
}

impl RegionBuilder {
    pub fn kind(mut self, kind: RegionKind) -> Self {
        self.kind = Some(kind);
        self
    }

    pub fn parent_op(mut self, parent_op: ArenaPtr<OpObj>) -> Self {
        self.parent_op = Some(parent_op);
        self
    }

    /// Build the region.
    ///
    /// This will add the region to the parent operation.
    pub fn build(self, ctx: &mut Context) -> Result<ArenaPtr<Region>> {
        let kind = self.kind.ok_or_else(|| anyhow!("missing kind"))?;
        let parent_op = self.parent_op.ok_or_else(|| anyhow!("missing parent_op"))?;

        let above = parent_op
            .deref(&ctx.ops)
            .as_inner()
            .as_base()
            .parent_region(ctx)
            .map(|region| {
                let region = region.deref(&ctx.regions);
                Rc::downgrade(&region.symbol_table)
            });

        let self_ptr = ctx.regions.reserve();
        let index = parent_op
            .deref_mut(&mut ctx.ops)
            .as_inner_mut()
            .as_base_mut()
            .add_region(self_ptr);
        let symbol_table = Rc::new(RefCell::new(SymbolTable::new(above)));
        let region = Region {
            self_ptr,
            kind,
            layout: Layout::default(),
            symbol_table,
            block_names: RefCell::new(NameManager::default()),
            parent_op,
            index,
        };
        ctx.regions.fill(self_ptr, region);
        Ok(self_ptr)
    }
}

impl Region {
    pub fn builder() -> RegionBuilder {
        RegionBuilder::default()
    }

    pub fn register_symbol(&self, name: String, op: ArenaPtr<OpObj>) {
        self.symbol_table.borrow_mut().insert(name, op);
    }

    pub fn lookup_symbol(&self, name: &str) -> Option<ArenaPtr<OpObj>> {
        self.symbol_table.borrow().lookup(name)
    }
}

impl Parse for Region {
    type Arg = RegionBuilder;
    type Item = ArenaPtr<Region>;

    fn parse(
        builder: Self::Arg,
        ctx: &mut Context,
        stream: &mut TokenStream,
    ) -> Result<Self::Item> {
        stream.expect(TokenKind::Char('{'))?;
        // build the region at the beginning because the blocks may reference it.
        let region_ptr = builder.build(ctx)?;
        // parse the blocks inside the region.
        loop {
            let token = stream.peek()?;
            match &token.kind {
                TokenKind::BlockLabel(label) => {
                    let builder = Block::builder()
                        .name(label.clone())
                        .entry(false)
                        .parent_region(region_ptr);
                    // consume the label, the block already has it.
                    stream.consume()?;
                    // the block parser will add the block to the layout.
                    let _block_ptr = Block::parse(builder, ctx, stream)?;
                }
                TokenKind::Char('}') => {
                    stream.consume()?;
                    // end of the region.
                    break;
                }
                _ => {
                    let builder = Block::builder().entry(true).parent_region(region_ptr);
                    // not consuming the token, the block parser will consume it.
                    let _block_ptr = Block::parse(builder, ctx, stream)?;
                }
            }
        }
        Ok(region_ptr)
    }
}

impl Print for Region {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        writeln!(state.buffer, "{{")?;
        for block in self.layout.iter_blocks() {
            block.deref(&ctx.blocks).print(ctx, state)?;
        }
        state.write_indent()?;
        write!(state.buffer, "}}")?;
        Ok(())
    }
}
