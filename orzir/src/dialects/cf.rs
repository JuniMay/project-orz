use std::fmt::Write;

use orzir_core::{
    parse_error, token, ArenaPtr, Context, ControlFlow, DataFlow, Dialect, Op, OpMetadata, OpObj,
    Parse, ParseErrorKind, ParseResult, ParseState, Print, PrintResult, PrintState, Successor,
    Value, Verify,
};
use orzir_macros::{ControlFlow, DataFlow, Op, RegionInterface};

use crate::verifiers::{control_flow::*, *};

/// The jump operation.
///
/// TODO: Make sure the operands number is ok to be zero.
#[derive(Op, DataFlow, RegionInterface, ControlFlow)]
#[mnemonic = "cf.jump"]
#[verifiers(NumResults<0>, NumOperands<0>, NumRegions<0>, NumSuccessors<1>, IsTerminator)]
pub struct Jump {
    #[metadata]
    metadata: OpMetadata,

    #[successor(0)]
    succ: Successor,
}

impl Verify for Jump {}

impl Parse for Jump {
    type Item = ArenaPtr<OpObj>;

    fn parse(ctx: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        let successor = Successor::parse(ctx, state)?;

        let result_names = state.pop_result_names();
        if !result_names.is_empty() {
            return parse_error!(
                // TODO: correct span
                state.stream.peek()?.span,
                ParseErrorKind::InvalidResultNumber(0, result_names.len())
            )
            .into();
        }

        let op = ctx.ops.reserve();
        let op = Jump::new(ctx, op, successor);

        Ok(op)
    }
}

impl Print for Jump {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> PrintResult<()> {
        let successor = self.get_successor(0).unwrap();
        write!(state.buffer, " ")?;
        successor.print(ctx, state)?;
        Ok(())
    }
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow)]
#[mnemonic = "cf.branch"]
#[verifiers(NumResults<0>, NumOperands<0>, NumRegions<0>, NumSuccessors<2>, IsTerminator)]
pub struct Branch {
    #[metadata]
    metadata: OpMetadata,

    #[operand(0)]
    cond: ArenaPtr<Value>,

    #[successor(0)]
    then_succ: Successor,

    #[successor(1)]
    else_succ: Successor,
}

impl Verify for Branch {}

impl Parse for Branch {
    type Item = ArenaPtr<OpObj>;

    fn parse(ctx: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        // cf.branch %cond, ^then(%a: int<32>), ^else(%b: float)
        let cond = Value::parse(ctx, state)?;
        state.stream.expect(token!(','))?;

        let then_block = Successor::parse(ctx, state)?;
        state.stream.expect(token!(','))?;

        let else_block = Successor::parse(ctx, state)?;

        let result_names = state.pop_result_names();

        if !result_names.is_empty() {}

        let op = ctx.ops.reserve();
        let op = Branch::new(ctx, op, cond, then_block, else_block);

        Ok(op)
    }
}

impl Print for Branch {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> PrintResult<()> {
        write!(state.buffer, " ")?;
        self.get_operand(0)
            .unwrap()
            .deref(&ctx.values)
            .print(ctx, state)?;
        write!(state.buffer, ", ")?;
        self.get_successor(0).unwrap().print(ctx, state)?;
        write!(state.buffer, ", ")?;
        self.get_successor(1).unwrap().print(ctx, state)?;
        Ok(())
    }
}

pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new("cf".into());
    ctx.dialects.insert("cf".into(), dialect);

    Jump::register(ctx, Jump::parse);
    Branch::register(ctx, Branch::parse);
}

#[cfg(test)]
mod tests {
    use orzir_core::{
        Context, OpObj, Parse, ParseState, Print, PrintState, RegionInterface, TokenStream,
    };

    use crate::dialects::{
        arith,
        builtin::{self, ModuleOp},
        cf, func,
    };

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

        let stream = TokenStream::new(src);
        let mut state = ParseState::new(stream);
        let mut ctx = Context::default();

        builtin::register(&mut ctx);
        func::register(&mut ctx);
        arith::register(&mut ctx);
        cf::register(&mut ctx);

        let op = OpObj::parse(&mut ctx, &mut state).unwrap();
        let mut state = PrintState::new("    ");
        op.deref(&ctx.ops).print(&ctx, &mut state).unwrap();
        println!("{}", state.buffer);

        let module_op = op.deref(&ctx.ops).as_a::<ModuleOp>().unwrap();
        assert!(module_op
            .get_region(0)
            .unwrap()
            .deref(&ctx.regions)
            .lookup_symbol(&ctx, "foo")
            .is_some());
    }

    #[test]
    fn test_1() {
        let src = r#"
        module {
            func.func @foo () -> int<32> {
            ^entry:
                %a = arith.iconst 123 : int<32>
                %b = arith.iconst 456 : int<32>

                %cond = arith.iconst true : int<32>

                cf.branch %cond, ^then(%a), ^else(%b)

            ^then(%x: int<32>):
                cf.jump ^return

            ^else(%y: int<32>):
                cf.jump ^return

            ^return:
                func.return %a
            }
        }
        "#;

        let stream = TokenStream::new(src);
        let mut state = ParseState::new(stream);
        let mut ctx = Context::default();

        builtin::register(&mut ctx);
        func::register(&mut ctx);
        arith::register(&mut ctx);
        cf::register(&mut ctx);

        let op = OpObj::parse(&mut ctx, &mut state).unwrap();
        let mut state = PrintState::new("    ");
        op.deref(&ctx.ops).print(&ctx, &mut state).unwrap();
        println!("{}", state.buffer);

        let module_op = op.deref(&ctx.ops).as_a::<ModuleOp>().unwrap();
        assert!(module_op
            .get_region(0)
            .unwrap()
            .deref(&ctx.regions)
            .lookup_symbol(&ctx, "foo")
            .is_some());
    }
}
