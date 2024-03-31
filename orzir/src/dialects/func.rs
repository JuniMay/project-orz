use std::fmt::Write;

use orzir_core::{
    ArenaPtr, Context, Dialect, Op, OpMetadata, OpObj, Parse, Region, RegionInterface, RegionKind,
    RunVerifiers, TyObj, Value, VerificationResult, Verify,
};
use orzir_macros::{ControlFlow, DataFlow, Op, Parse, Print, RegionInterface};

use super::builtin::Symbol;
use crate::verifiers::{control_flow::*, *};

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print)]
#[mnemonic = "func.func"]
#[verifiers(IsIsolatedFromAbove, NumRegions<1>, NumResults<0>)]
#[format(pattern = "{symbol} : {ty} {region}", num_results = 0)]
pub struct FuncOp {
    #[metadata]
    metadata: OpMetadata,

    #[region(0, kind = RegionKind::SsaCfg)]
    region: ArenaPtr<Region>,

    symbol: Symbol,

    ty: ArenaPtr<TyObj>,
}

impl Verify for FuncOp {
    fn verify(&self, ctx: &Context) -> VerificationResult<()> {
        self.run_verifiers(ctx)?;
        self.ty.deref(&ctx.tys).as_ref().verify(ctx)?;
        self.get_region(0)
            .unwrap()
            .deref(&ctx.regions)
            .verify(ctx)?;
        Ok(())
    }
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print)]
#[mnemonic = "func.return"]
#[verifiers(NumResults<0>, VariadicOperands, NumRegions<0>, IsTerminator)]
#[format(pattern = "{operands}", num_results = 0)]
pub struct ReturnOp {
    #[metadata]
    metadata: OpMetadata,

    #[operand(...)]
    #[format(sep = ",")]
    operands: Vec<ArenaPtr<Value>>,
}

impl Verify for ReturnOp {}

/// A direct call operation.
///
/// Format (example):
/// ```text
/// %result = func.call @callee(%arg1, %arg2) : int<32>
/// ```
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print)]
#[mnemonic = "func.call"]
#[verifiers(VariadicResults, VariadicOperands, NumRegions<0>)]
#[format(pattern = "{callee} {operands}")]
pub struct CallOp {
    #[metadata]
    metadata: OpMetadata,

    #[result(...)]
    results: Vec<ArenaPtr<Value>>,

    #[operand(...)]
    #[format(sep = ",", leading = "(", trailing = ")")]
    operands: Vec<ArenaPtr<Value>>,

    callee: Symbol,
}

impl Verify for CallOp {}

pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new("func".into());
    ctx.dialects.insert("func".into(), dialect);

    FuncOp::register(ctx, FuncOp::parse);
    ReturnOp::register(ctx, ReturnOp::parse);
    CallOp::register(ctx, CallOp::parse);
}

#[cfg(test)]
mod tests {
    use orzir_core::{
        Context, OpObj, Parse, ParseState, Print, PrintState, RegionInterface, RegionKind,
        TokenStream,
    };

    use crate::dialects::{
        arith,
        builtin::{self, ModuleOp},
        cf,
        func::{self},
    };

    #[test]
    fn test_func_op() {
        let src = r#"
        module {
            func.func @foo :  fn() -> (int<32>, float) {
            ^entry:
                %x = arith.iconst 123 : int<32>
                %y = arith.iconst 123 : int<32>
            ^return:
                func.return %x, %y
            ^single:
                func.return %x
            ^null:
                func.return
            }
        }
        "#;

        let stream = TokenStream::new(src);
        let mut state = ParseState::new(stream);
        let mut ctx = Context::default();

        builtin::register(&mut ctx);
        func::register(&mut ctx);
        arith::register(&mut ctx);

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
    fn test_call_op() {
        let src = r#"
        module {
            func.func @bar : fn(int<32>) -> int<32> {
            ^entry(%0 : int<32>):
                func.return %0
            }

            func.func @foo : fn() -> (int<32>, int<32>) {
            ^entry:
                %x = arith.iconst 123 : int<32>
                %y = arith.iconst 123 : int<32>
                %z = func.call @bar(%x) : int<32>
                cf.jump ^return(%x, %y)
            ^return:
                func.return %x, %y
            }
        }
        "#;

        let stream = TokenStream::new(src);
        let mut state = ParseState::new(stream);
        let mut ctx = Context::default();

        builtin::register(&mut ctx);
        func::register(&mut ctx);
        cf::register(&mut ctx);
        arith::register(&mut ctx);

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

        assert!(module_op
            .get_region(0)
            .unwrap()
            .deref(&ctx.regions)
            .lookup_symbol(&ctx, "bar")
            .is_some());

        assert!(module_op.get_region_kind(&ctx, 0) == RegionKind::Graph);
    }
}
