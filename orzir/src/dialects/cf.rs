use anyhow::Result;
use orzir_core::{
    ArenaPtr, Block, Context, Dialect, Op, OpObj, OpResultBuilder, Parse, Print, PrintState,
    Successor, TokenStream,
};
use orzir_macros::op;
use std::fmt::Write;

#[op("cf.jump")]
pub struct Jump;

impl Parse for Jump {
    type Arg = (Vec<OpResultBuilder>, Option<ArenaPtr<Block>>);
    type Item = ArenaPtr<OpObj>;

    fn parse(arg: Self::Arg, ctx: &mut Context, stream: &mut TokenStream) -> Result<Self::Item> {
        let (result_builders, parent_block) = arg;
        assert!(result_builders.is_empty());

        let parent_region = parent_block
            .expect("JumpOp should be embraced by a block.")
            .deref(&ctx.blocks)
            .parent_region();

        let successor = Successor::parse(parent_region, ctx, stream)?;

        let op = Jump::new(ctx);
        op.deref_mut(&mut ctx.ops)
            .as_inner_mut()
            .as_base_mut()
            .add_successor(successor);

        Ok(op)
    }
}

impl Print for Jump {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        let op_base = self.as_base();
        let successor = op_base.get_successor(0).unwrap();
        write!(state.buffer, " ")?;
        successor.print(ctx, state)?;
        Ok(())
    }
}

pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new("cf".into());
    ctx.dialects.insert("cf".into(), dialect);

    Jump::register(ctx, Jump::parse);
}

#[cfg(test)]
mod tests {
    use orzir_core::{Context, Op, OpObj, Parse, Print, PrintState, TokenStream};

    use crate::dialects::{
        arith,
        builtin::{self, ModuleOp},
        cf, func,
    };

    fn test_parse_print(src: &str, expected: &str) {
        let mut stream = TokenStream::new(src);
        let mut ctx = Context::default();
        builtin::register(&mut ctx);
        arith::register(&mut ctx);
        let item = OpObj::parse(None, &mut ctx, &mut stream).unwrap();
        let mut state = PrintState::new("");
        item.deref(&ctx.ops).print(&ctx, &mut state).unwrap();
        assert_eq!(state.buffer, expected);
    }

    #[test]
    fn test_0() {
        let src = r#"
        module {
            func.func @foo () -> (int<32>, float) {
            ^entry(%x : float, %y: int<32>):
                // nothing here
                %0 = arith.iconst true : int<32>
                %1 = arith.iconst false : int<32>
                %2 = arith.iadd %0, %1 : int<32>

                %aaaa = arith.iconst -0x123 : int<32>

                %b = arith.iconst 0b101 : int<32>
                %c = arith.iconst 0o123 : int<32>
                %d = arith.iconst 123 : int<32>

                cf.jump ^entry(%x, %y)
            }
        }
        "#;

        let mut stream = TokenStream::new(src);
        let mut ctx = Context::default();

        builtin::register(&mut ctx);
        func::register(&mut ctx);
        arith::register(&mut ctx);
        cf::register(&mut ctx);

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
