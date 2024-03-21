use std::{cell::RefCell, rc::Rc};

use anyhow::{anyhow, Result};

use crate::{support::storage::ArenaPtr, Context, Parse, Print, PrintState, TokenStream};

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
}

/// A region in the IR.
pub struct Region {
    /// The kind of the region.
    kind: RegionKind,
    /// The layout of the region.
    layout: Layout,
    /// The symbol table of the region.
    symbol_table: SymbolTableOwned,
    /// The block names of the region.
    block_names: RefCell<NameManager<ArenaPtr<Block>>>,
    /// The parent operation of the region.
    parent_op: ArenaPtr<OpObj>,
    /// The index of the region in the parent operation.
    index: usize,
}

pub struct RegionBuilder {
    kind: Option<RegionKind>,
    parent_op: Option<ArenaPtr<OpObj>>,
}

impl Default for RegionBuilder {
    fn default() -> Self {
        Self {
            kind: None,
            parent_op: None,
        }
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

    pub fn build(self, ctx: &mut Context) -> Result<ArenaPtr<Region>> {
        let kind = self.kind.ok_or_else(|| anyhow!("missing kind"))?;
        let parent_op = self.parent_op.ok_or_else(|| anyhow!("missing parent_op"))?;

        let above = parent_op
            .deref(&mut ctx.ops)
            .as_inner()
            .as_base()
            .parent_region()
            .map(|region| {
                let region = region.deref(&mut ctx.regions);
                Rc::downgrade(&region.symbol_table)
            });

        let ptr = ctx.regions.reserve();
        let index = parent_op
            .deref_mut(&mut ctx.ops)
            .as_inner_mut()
            .as_base_mut()
            .add_region(ptr);
        let symbol_table = Rc::new(RefCell::new(SymbolTable::new(above)));
        let region = Region {
            kind,
            layout: Layout::default(),
            symbol_table,
            block_names: RefCell::new(NameManager::default()),
            parent_op,
            index,
        };
        ctx.regions.fill(ptr, region);
        Ok(ptr)
    }
}

impl Region {
    pub fn builder() -> RegionBuilder {
        RegionBuilder::default()
    }
}

impl Parse for Region {
    type Arg = ArenaPtr<OpObj>;
    type Item = ArenaPtr<Region>;

    fn parse(
        parent_op: Self::Arg,
        ctx: &mut Context,
        stream: &mut TokenStream,
    ) -> Result<Self::Item> {
        todo!()
    }
}

impl Print for Region {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        todo!()
    }
}
