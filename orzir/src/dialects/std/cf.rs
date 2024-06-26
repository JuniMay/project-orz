use std::fmt::Write;

use orzir_core::{ArenaPtr, Context, Dialect, Op, OpMetadata, Parse, Successor, Value};
use orzir_macros::{ControlFlow, DataFlow, Op, Parse, Print, RegionInterface, Verify};

use crate::verifiers::{control_flow::*, *};

/// The jump operation.
///
/// This represents an unconditional jump to another block with some arguments.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "cf.jump"]
#[verifiers(NumResults<0>, VariadicOperands, NumRegions<0>, NumSuccessors<1>, IsTerminator)]
#[format(pattern = "{succ}", kind = "op", num_results = 0)]
pub struct JumoOp {
    #[metadata]
    metadata: OpMetadata,
    /// The successor of this jump operation.
    #[successor(0)]
    succ: Successor,
}

/// The branch operation.
///
/// This represents a conditional branch to two different blocks.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "cf.branch"]
#[verifiers(NumResults<0>, NumOperands<1>, NumRegions<0>, NumSuccessors<2>, IsTerminator)]
#[format(
    kind = "op",
    pattern = "{cond}, {then_succ}, {else_succ}",
    num_results = 0
)]
pub struct BranchOp {
    #[metadata]
    metadata: OpMetadata,
    /// The condition of the branch.
    #[operand(0)]
    cond: ArenaPtr<Value>,
    /// The successor of the branch if the condition is true.
    #[successor(0)]
    then_succ: Successor,
    /// The successor of the branch if the condition is false.
    #[successor(1)]
    else_succ: Successor,
}

/// Register the control flow dialect.
pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new("cf".into());
    ctx.register_dialect(dialect);

    JumoOp::register(ctx, JumoOp::parse);
    BranchOp::register(ctx, BranchOp::parse);
}

#[cfg(test)]
mod tests {
    use orzir_core::{
        Context,
        OpObj,
        Parse,
        ParseState,
        Print,
        PrintState,
        RegionInterface,
        TokenStream,
    };

    use crate::dialects::std::{
        arith,
        builtin::{self, ModuleOp},
        cf,
        func,
        register_std_dialects,
    };

    #[test]
    fn test_0() {
        let src = r#"
        module {
            func.func @foo : fn() -> (int<32>, float) {
            ^entry(%x : float, %y: int<32>):
                // nothing here
                %0 = arith.iconst true : int<1>
                %1 = arith.iconst false : int<1>
                %2 = arith.iadd %0, %1 : int<1>

                %aaaa = arith.iconst -0x123i32 : int<32>

                %b = arith.iconst 0b101i32 : int<32>
                %c = arith.iconst 0o123i32 : int<32>
                %d = arith.iconst 123i32 : int<32>

                cf.jump ^entry(%x, %y)
            }
        }
        "#;

        let stream = TokenStream::new(src);
        let mut state = ParseState::new(stream);
        let mut ctx = Context::default();

        register_std_dialects(&mut ctx);

        let op = OpObj::parse(&mut ctx, &mut state).unwrap();
        let mut state = PrintState::new("    ");
        op.deref(&ctx.ops).as_ref().verify(&ctx).unwrap();
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
            func.func @foo : fn () -> int<32> {
            ^entry:
                %a = arith.iconst 123i32 : int<32>
                %b = arith.iconst 456i32 : int<32>

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
