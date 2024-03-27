use std::fmt::Write;

use anyhow::Result;
use orzir_core::{
    ArenaPtr, Block, Context, Op, OpBase, OpObj, OpResultBuilder, Parse, Print,
    PrintState, Region, RegionKind, TokenKind, TokenStream, Verify
};
use orzir_macros::Op;

#[derive(Op)]
#[mnemonic = "builtin.module"]
pub struct ModuleOp {
    #[base]
    op_base: OpBase,
    symbol: Option<String>,
}

impl Verify for ModuleOp {}

impl Parse for ModuleOp {
    type Arg = (Vec<OpResultBuilder>, Option<ArenaPtr<Block>>);
    type Item = ArenaPtr<OpObj>;

    fn parse(arg: Self::Arg, ctx: &mut Context, stream: &mut TokenStream) -> Result<Self::Item> {
        let (result_builders, parent_block) = arg;

        if !result_builders.is_empty() {
            anyhow::bail!("ModuleOp does not have any results");
        }

        let token = stream.peek()?;
        let symbol = if let TokenKind::ValueName(symbol) = &token.kind {
            let symbol = symbol.clone();
            stream.consume()?;
            Some(symbol)
        } else {
            None
        };

        let op = ModuleOp::new(ctx, symbol);
        op.deref_mut(&mut ctx.ops)
            .as_inner_mut()
            .set_parent_block(parent_block);

        let region_builder = Region::builder().parent_op(op).kind(RegionKind::Graph);
        // the region will be added in the parser.
        let _region = Region::parse(region_builder, ctx, stream)?;

        Ok(op)
    }
}

impl Print for ModuleOp {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        if let Some(symbol) = &self.symbol {
            write!(state.buffer, "@{}", symbol)?;
        }
        write!(state.buffer, " ")?;
        self.get_region(0).unwrap().deref(&ctx.regions).print(ctx, state)?;

        Ok(())
    }
}

fn main() {}
