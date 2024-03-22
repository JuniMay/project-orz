use anyhow::Result;
use orzir_core::{
    ArenaPtr, Block, Context, Dialect, Op, OpObj, OpResultBuilder, Parse, Print, PrintState,
    Region, RegionKind, TokenKind, TokenStream, TypeObj,
};
use orzir_macros::op;
use std::fmt::Write;

use super::builtin::FunctionType;

#[op("func.func")]
pub struct FuncOp {
    symbol: String,
    ty: ArenaPtr<TypeObj>,
}

impl Parse for FuncOp {
    type Arg = (Vec<OpResultBuilder>, Option<ArenaPtr<Block>>);
    type Item = ArenaPtr<OpObj>;

    fn parse(arg: Self::Arg, ctx: &mut Context, stream: &mut TokenStream) -> Result<Self::Item> {
        let (result_builders, parent_block) = arg;
        assert!(result_builders.is_empty());

        let symbol = if let TokenKind::SymbolName(s) = stream.consume()?.kind {
            s
        } else {
            anyhow::bail!("expected symbol name");
        };
        let ty = FunctionType::parse((), ctx, stream)?;
        let op = FuncOp::new(ctx, symbol.clone(), ty);

        // parse the region.
        let region_builder = Region::builder().parent_op(op).kind(RegionKind::SsaCfg);
        let _region = Region::parse(region_builder, ctx, stream)?;

        op.deref_mut(&mut ctx.ops)
            .as_inner_mut()
            .as_base_mut()
            .set_parent_block(parent_block);
        // register the symbol in the parent region.
        parent_block
            .expect("FuncOp should be embraced by a region.")
            .deref(&ctx.blocks)
            .parent_region()
            .deref_mut(&mut ctx.regions)
            .register_symbol(symbol, op);

        Ok(op)
    }
}

impl Print for FuncOp {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        write!(state.buffer, " {}", self.symbol)?;
        let func_type = self.ty.deref(&ctx.types).as_a::<FunctionType>().unwrap();
        func_type.print(ctx, state)?;
        write!(state.buffer, " ")?;
        self.as_base()
            .get_region(0)
            .unwrap()
            .deref(&ctx.regions)
            .print(ctx, state)?;
        Ok(())
    }
}

pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new("func".into());
    ctx.dialects.insert("func".into(), dialect);

    FuncOp::register(ctx, FuncOp::parse);
}

#[cfg(test)]
mod tests {
    use orzir_core::{Context, Op, OpObj, Parse, Print, PrintState, TokenStream};

    use crate::dialects::{
        builtin::{self, ModuleOp},
        func,
    };

    #[test]
    fn test_func_op() {
        let src = r#"
        module {
            func.func @foo () -> (int<32>, float) {
            ^entry:
                // nothing here
            }
        }
        "#;

        let mut stream = TokenStream::new(src);
        let mut ctx = Context::default();

        builtin::register(&mut ctx);
        func::register(&mut ctx);

        let op = OpObj::parse(None, &mut ctx, &mut stream).unwrap();
        let mut state = PrintState::new("");
        op.deref(&ctx.ops).print(&ctx, &mut state).unwrap();
        println!("{}", state.buffer);

        let module_op = op.deref(&ctx.ops).as_a::<ModuleOp>().unwrap();

        assert!(module_op
            .as_base()
            .get_region(0)
            .unwrap()
            .deref(&ctx.regions)
            .lookup_symbol("foo")
            .is_some());
    }
}
