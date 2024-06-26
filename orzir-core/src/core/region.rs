use std::{cell::RefCell, fmt::Write};

use super::{
    block::Block,
    layout::BlockList,
    op::OpObj,
    parse::ParseState,
    symbol::{NameManager, Symbol, SymbolTable},
};
use crate::{
    core::parse::TokenKind,
    delimiter,
    support::storage::ArenaPtr,
    Context,
    Parse,
    ParseResult,
    Print,
    PrintResult,
    PrintState,
    RunVerifiers,
    Verify,
    VerifyResult,
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
    layout: BlockList,
    /// The symbol table of the region.
    symbol_table: SymbolTable,
    /// The block names of the region.
    pub(crate) block_names: RefCell<NameManager<Block>>,
    /// The parent operation of the region.
    parent_op: ArenaPtr<OpObj>,
    /// The index of the region in the parent operation.
    index: usize,
}

impl RunVerifiers for Region {
    fn run_verifiers(&self, _ctx: &Context) -> VerifyResult<()> { Ok(()) }
}

impl Verify for Region {
    fn verify(&self, ctx: &Context) -> VerifyResult<()> {
        for block in self.layout().iter() {
            block.deref(&ctx.blocks).verify(ctx)?;
        }
        Ok(())
    }
}

impl Region {
    pub fn new(
        ctx: &mut Context,
        kind: RegionKind,
        parent_op: ArenaPtr<OpObj>,
        index: usize,
    ) -> ArenaPtr<Region> {
        let self_ptr = ctx.regions.reserve();

        let symbol_table = SymbolTable::new(self_ptr);
        let region = Region {
            self_ptr,
            kind,
            layout: BlockList::default(),
            symbol_table,
            block_names: RefCell::new(NameManager::default()),
            parent_op,
            index,
        };
        ctx.regions.fill(self_ptr, region);
        self_ptr
    }

    pub fn layout(&self) -> &BlockList { &self.layout }

    pub fn layout_mut(&mut self) -> &mut BlockList { &mut self.layout }

    pub fn kind(&self) -> RegionKind { self.kind }

    pub fn set_kind(&mut self, kind: RegionKind) { self.kind = kind; }

    pub fn parent_op(&self) -> ArenaPtr<OpObj> { self.parent_op }

    pub fn index(&self) -> usize { self.index }

    pub fn self_ptr(&self) -> ArenaPtr<Self> { self.self_ptr }

    pub fn parent_region(&self, ctx: &Context) -> Option<ArenaPtr<Region>> {
        self.parent_op.deref(&ctx.ops).as_ref().parent_region(ctx)
    }

    /// Check if this region is an ancestor of the other region.
    pub fn is_ancestor(&self, ctx: &Context, other: ArenaPtr<Region>) -> bool {
        if self.self_ptr() == other {
            return true;
        }
        let mut parent = other.deref(&ctx.regions).parent_region(ctx);
        while let Some(region) = parent {
            if region == self.self_ptr() {
                return true;
            }
            parent = other.deref(&ctx.regions).parent_region(ctx);
        }
        false
    }

    pub fn register_symbol(&mut self, symbol: Symbol, op: ArenaPtr<OpObj>) {
        self.symbol_table.insert(symbol, op);
    }

    pub fn lookup_symbol(&self, ctx: &Context, name: &str) -> Option<ArenaPtr<OpObj>> {
        self.symbol_table.lookup(ctx, name)
    }
}

impl Parse for Region {
    type Item = ArenaPtr<Region>;

    /// Parse the region.
    ///
    /// This require the parent operation parser to pass the builder to the
    /// region parser, and set the kind and parent operation.
    fn parse(ctx: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        state.stream.expect(delimiter!('{'))?;
        // build the region at the beginning because the blocks may reference it.
        let (region_kind, index) = state.curr_region_info();
        let parent_op = state.curr_op();
        let region = Region::new(ctx, region_kind, parent_op, index);
        // parse the blocks inside the region.
        state.enter_block_from(region);
        loop {
            let token = state.stream.peek()?;
            match &token.kind {
                TokenKind::Char('}') => {
                    state.stream.consume()?;
                    state.exit_block();
                    break;
                }
                _ => {
                    let block = Block::parse(ctx, state)?;
                    region
                        .deref_mut(&mut ctx.regions)
                        .layout_mut()
                        .append(block)
                        .expect("should be able to append block when parsing a region")
                }
            }
        }
        Ok(region)
    }
}

impl Print for Region {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> PrintResult<()> {
        writeln!(state.buffer, " {{")?;
        for block in self.layout.iter() {
            block.deref(&ctx.blocks).print(ctx, state)?;
        }
        state.write_indent()?;
        write!(state.buffer, "}}")?;
        Ok(())
    }
}
