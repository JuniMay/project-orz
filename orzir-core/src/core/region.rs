use std::{cell::RefCell, fmt::Write, rc::Rc};

use anyhow::Result;

use super::{
    block::Block,
    layout::Layout,
    operation::OpObj,
    parse::ParseState,
    symbol::{NameManager, SymbolTable, SymbolTableOwned},
};
use crate::{
    core::parse::TokenKind, support::storage::ArenaPtr, Context, Parse, Print, PrintState, Verify,
    VerifyInterfaces,
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

impl VerifyInterfaces for Region {
    fn verify_interfaces(&self, _ctx: &Context) -> Result<()> { Ok(()) }
}

impl Verify for Region {
    fn verify(&self, ctx: &Context) -> Result<()> {
        for block in self.layout().iter_blocks() {
            block.deref(&ctx.blocks).verify(ctx)?;
            for op in self.layout().iter_ops(block) {
                op.deref(&ctx.ops).as_ref().verify(ctx)?;
            }
        }
        Ok(())
    }
}

impl Region {
    pub fn layout(&self) -> &Layout { &self.layout }

    pub fn layout_mut(&mut self) -> &mut Layout { &mut self.layout }

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
}

/// The builder of the region.
///
/// This builder requires the kind, parent operation, and index to be set.
///
/// The index is used to attach the region to the parent operation, and if
/// it is not set, the build function will return an error.
#[derive(Debug, Default)]
pub struct RegionBuilder<
    const KIND: bool = false,
    const PARENT_OP: bool = false,
    const INDEX: bool = false,
> {
    kind: Option<RegionKind>,
    parent_op: Option<ArenaPtr<OpObj>>,
    index: Option<usize>,
}

impl<const PARENT_OP: bool, const INDEX: bool> RegionBuilder<false, PARENT_OP, INDEX> {
    /// Set the kind of the region.
    pub fn kind(mut self, kind: RegionKind) -> RegionBuilder<true, PARENT_OP, INDEX> {
        self.kind = Some(kind);
        RegionBuilder {
            kind: self.kind,
            parent_op: self.parent_op,
            index: self.index,
        }
    }
}

impl<const KIND: bool, const INDEX: bool> RegionBuilder<KIND, false, INDEX> {
    /// Set the parent operation of the region.
    pub fn parent_op(mut self, parent_op: ArenaPtr<OpObj>) -> RegionBuilder<KIND, true, INDEX> {
        self.parent_op = Some(parent_op);
        RegionBuilder {
            kind: self.kind,
            parent_op: self.parent_op,
            index: self.index,
        }
    }
}

impl<const KIND: bool, const PARENT_OP: bool> RegionBuilder<KIND, PARENT_OP, false> {
    /// Set the index of the region in the parent operation.
    pub fn index(mut self, index: usize) -> RegionBuilder<KIND, PARENT_OP, true> {
        self.index = Some(index);
        RegionBuilder {
            kind: self.kind,
            parent_op: self.parent_op,
            index: self.index,
        }
    }
}

impl RegionBuilder<true, true, true> {
    /// Build the region and consume the builder.
    ///
    /// This will add the region to the parent operation, and store the index in
    /// the parent operation.
    ///
    /// # Errors
    ///
    /// This function will return an error if the kind, parent operation, or
    /// index is not set.
    pub fn build(self, ctx: &mut Context) -> Result<ArenaPtr<Region>> {
        let kind = self.kind.unwrap();
        let parent_op = self.parent_op.unwrap();
        let index = self.index.unwrap();

        let above = parent_op.deref(&ctx.ops).as_ref().parent_region(ctx).map(|region| {
            let region = region.deref(&ctx.regions);
            Rc::downgrade(&region.symbol_table)
        });

        let self_ptr = ctx.regions.reserve();
        parent_op.deref_mut(&mut ctx.ops).as_mut().set_region(index, self_ptr)?;
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
    pub fn builder() -> RegionBuilder { RegionBuilder::default() }

    pub fn register_symbol(&self, name: String, op: ArenaPtr<OpObj>) {
        self.symbol_table.borrow_mut().insert(name, op);
    }

    pub fn lookup_symbol(&self, name: &str) -> Option<ArenaPtr<OpObj>> {
        self.symbol_table.borrow().lookup(name)
    }
}

impl Parse for Region {
    type Arg = ();
    type Item = ArenaPtr<Region>;

    /// Parse the region.
    ///
    /// This require the parent operation parser to pass the builder to the
    /// region parser, and set the kind and parent operation.
    fn parse(_: (), ctx: &mut Context, state: &mut ParseState) -> Result<Self::Item> {
        state.stream.expect(TokenKind::Char('{'))?;
        // build the region at the beginning because the blocks may reference it.
        let (region_kind, index) = state.curr_region_info();
        let parent_op = state.curr_op();
        let region = Region::builder()
            .parent_op(parent_op)
            .kind(region_kind)
            .index(index)
            .build(ctx)?;
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
                    let _block = Block::parse((), ctx, state)?;
                }
            }
        }
        Ok(region)
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
