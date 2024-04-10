use std::fmt::Write;

use orzir_core::{apint::ApInt, ArenaPtr, Context, Dialect, Op, OpMetadata, Parse, Value};
use orzir_macros::{ControlFlow, DataFlow, Op, Parse, Print, RegionInterface, Verify};

use crate::verifiers::*;

/// An integer constant operation.
///
/// This will generate an integer constant with the given value.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "arith.iconst"]
#[verifiers(NumResults<1>, NumOperands<0>, NumRegions<0>, SameResultTys)]
#[format(pattern = "{value}", kind = "op", num_results = 1)]
pub struct IConstOp {
    #[metadata]
    metadata: OpMetadata,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The value of the integer constant.
    value: ApInt,
}

/// An integer addition operation.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "arith.iadd"]
#[verifiers(
    NumResults<1>, NumOperands<2>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys
)]
#[format(pattern = "{lhs} , {rhs}", kind = "op", num_results = 1)]
pub struct IAddOp {
    #[metadata]
    metadata: OpMetadata,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The left-hand side operand.
    #[operand(0)]
    lhs: ArenaPtr<Value>,
    /// The right-hand side operand.
    #[operand(1)]
    rhs: ArenaPtr<Value>,
}

/// An integer subtraction operation.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "arith.isub"]
#[verifiers(
    NumResults<1>, NumOperands<2>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys
)]
#[format(pattern = "{lhs} , {rhs}", kind = "op", num_results = 1)]
pub struct ISubOp {
    #[metadata]
    metadata: OpMetadata,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The left-hand side operand.
    #[operand(0)]
    lhs: ArenaPtr<Value>,
    /// The right-hand side operand.
    #[operand(1)]
    rhs: ArenaPtr<Value>,
}

/// An integer multiplication operation.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "arith.imul"]
#[verifiers(
    NumResults<1>, NumOperands<2>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys
)]
#[format(pattern = "{lhs} , {rhs}", kind = "op", num_results = 1)]
pub struct IMulOp {
    #[metadata]
    metadata: OpMetadata,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The left-hand side operand.
    #[operand(0)]
    lhs: ArenaPtr<Value>,
    /// The right-hand side operand.
    #[operand(1)]
    rhs: ArenaPtr<Value>,
}

/// Register the `arith` dialect.
pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new("arith".into());
    ctx.dialects.insert("arith".into(), dialect);

    IConstOp::register(ctx, IConstOp::parse);
    IAddOp::register(ctx, IAddOp::parse);
}

#[cfg(test)]
mod tests {
    use orzir_core::{
        Context, OpObj, Parse, ParseState, Print, PrintState, RegionInterface, TokenStream,
    };

    use crate::dialects::{
        arith,
        builtin::{self, ModuleOp},
        func,
    };

    fn test_parse_print(src: &str, expected: &str) {
        let stream = TokenStream::new(src);
        let mut state = ParseState::new(stream);
        let mut ctx = Context::default();
        builtin::register(&mut ctx);
        arith::register(&mut ctx);
        let item = OpObj::parse(&mut ctx, &mut state).unwrap();
        let mut state = PrintState::new("");
        item.deref(&ctx.ops).print(&ctx, &mut state).unwrap();
        assert_eq!(state.buffer, expected);
    }

    #[test]
    fn test_iconst_op() {
        let src = "%x = arith.iconst 123i32 : int<32>";
        let expected = "%x = arith.iconst 0x0000007bi32 : int<32>";
        test_parse_print(src, expected);
    }

    #[test]
    fn test_0() {
        let src = r#"
        module {
            func.func @foo : fn () -> (int<32>, float) {
            ^entry:
                // nothing here
                %0 = arith.iconst true : int<32>
                %1 = arith.iconst false : int<32>
                %2 = arith.iadd %0, %1 : int<32>

                %aaaa = arith.iconst -0x123i32 : int<32>

                %b = arith.iconst 0b101i32 : int<32>
                %c = arith.iconst 0o123i32 : int<32>
                %d = arith.iconst 123i32 : int<32>
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
}
