use anyhow::{Ok, Result};
use orzir_core::{
    ArenaPtr, Block, Context, Dialect, Op, OpObj, OpResultBuilder, Parse, Print, PrintState,
    Region, RegionKind, TokenKind, TokenStream, TypeObj, Value,
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

#[op("func.return")]
pub struct ReturnOp;

impl Parse for ReturnOp {
    type Arg = (Vec<OpResultBuilder>, Option<ArenaPtr<Block>>);
    type Item = ArenaPtr<OpObj>;

    fn parse(arg: Self::Arg, ctx: &mut Context, stream: &mut TokenStream) -> Result<Self::Item> {
        // func.return %1, %2
        // func.return
        let (result_builders, parent_block) = arg;
        assert!(result_builders.is_empty());

        let op = ReturnOp::new(ctx);

        while let TokenKind::ValueName(_) = stream.peek()?.kind {
            let operand = Value::parse((), ctx, stream)?;
            op.deref_mut(&mut ctx.ops)
                .as_inner_mut()
                .as_base_mut()
                .add_operand(operand);

            if let TokenKind::Char(',') = stream.peek()?.kind {
                stream.consume()?;
            } else {
                break;
            }
        }

        op.deref_mut(&mut ctx.ops)
            .as_inner_mut()
            .as_base_mut()
            .set_parent_block(parent_block);

        Ok(op)
    }
}

impl Print for ReturnOp {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        let operations = self.as_base().operands();
        if !operations.is_empty() {
            write!(state.buffer, " ")?;
            for (i, operand) in operations.iter().enumerate() {
                if i > 0 {
                    write!(state.buffer, ", ")?;
                }
                operand.deref(&ctx.values).print(ctx, state)?;
            }
        }

        Ok(())
    }
}

pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new("func".into());
    ctx.dialects.insert("func".into(), dialect);

    FuncOp::register(ctx, FuncOp::parse);
    ReturnOp::register(ctx, ReturnOp::parse);
}

#[cfg(test)]
mod tests {
    use orzir_core::{Context, Op, OpObj, Parse, Print, PrintState, TokenStream};

    use crate::dialects::{
        arith,
        builtin::{self, ModuleOp},
        func,
    };

    #[test]
    fn test_func_op() {
        let src = r#"
        module {
            func.func @foo () -> (int<32>, float) {
            ^entry:
                // %x = arith.iconst 123 : int<32>
                // %y = arith.iconst 123 : int<32>
            ^return:
                func.return %x, %y
            ^single:
                func.return %x
            ^null:
                func.return
            }
        }
        "#;

        let mut stream = TokenStream::new(src);
        let mut ctx = Context::default();

        builtin::register(&mut ctx);
        func::register(&mut ctx);
        arith::register(&mut ctx);

        let op = OpObj::parse(None, &mut ctx, &mut stream).unwrap();
        let mut state = PrintState::new("    ");
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
