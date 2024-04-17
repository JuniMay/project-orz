use std::fmt::Write;

use orzir_core::{
    apint::ApInt, verification_error, ArenaPtr, Context, Dialect, Op, OpMetadata, Parse,
    RunVerifiers, Typed, Value, Verify,
};
use orzir_macros::{ControlFlow, DataFlow, Op, Parse, Print, RegionInterface, Verify};
use thiserror::Error;

use super::builtin::IntTy;
use crate::verifiers::*;

/// An integer constant operation.
///
/// This will generate an integer constant with the given value.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print)]
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

#[derive(Debug, Error)]
#[error("expected an integer with width {0}, but got {1}")]
pub struct IncompatibleWidthErr(pub usize, pub usize);

impl Verify for IConstOp {
    fn verify(&self, ctx: &Context) -> orzir_core::VerificationResult<()> {
        self.run_verifiers(ctx)?;
        self.result.deref(&ctx.values).verify(ctx)?;
        let result_ty = self.result.deref(&ctx.values).ty(ctx).deref(&ctx.tys);
        if let Some(ty) = result_ty.as_a::<IntTy>() {
            // for `index` type, the width can be arbitrary in verification time
            if ty.width() != self.value.width() {
                return verification_error!(IncompatibleWidthErr(ty.width(), self.value.width()))
                    .into();
            }
        }
        Ok(())
    }
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

/// A float addition operation.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "arith.fadd"]
#[verifiers(
    NumResults<1>, NumOperands<2>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys
)]
#[format(pattern = "{lhs} , {rhs}", kind = "op", num_results = 1)]
pub struct FAddOp {
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

/// A float subtraction operation.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "arith.fsub"]
#[verifiers(
    NumResults<1>, NumOperands<2>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys
)]
#[format(pattern = "{lhs} , {rhs}", kind = "op", num_results = 1)]
pub struct FSubOp {
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

/// A float multiplication operation.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "arith.fmul"]
#[verifiers(
    NumResults<1>, NumOperands<2>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys
)]
#[format(pattern = "{lhs} , {rhs}", kind = "op", num_results = 1)]
pub struct FMulOp {
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

/// A float division operation
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "arith.fdiv"]
#[verifiers(
    NumResults<1>, NumOperands<2>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys
)]
#[format(pattern = "{lhs} , {rhs}", kind = "op", num_results = 1)]
pub struct FDivOp {
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
    FAddOp::register(ctx, FAddOp::parse);
    ISubOp::register(ctx, ISubOp::parse);
    FSubOp::register(ctx, FSubOp::parse);
    IMulOp::register(ctx, IMulOp::parse);
    FMulOp::register(ctx, FMulOp::parse);
    FDivOp::register(ctx, FDivOp::parse);
    
}

#[cfg(test)]
mod tests {
    use orzir_core::{
        Context, OpObj, Parse, ParseState, Print, PrintState, RegionInterface, TokenStream,
    };

    use crate::dialects::std::{builtin::ModuleOp, register_std_dialects};

    fn test_parse_print(src: &str, expected: &str) {
        let stream = TokenStream::new(src);
        let mut state = ParseState::new(stream);
        let mut ctx = Context::default();
        register_std_dialects(&mut ctx);
        let item = OpObj::parse(&mut ctx, &mut state).unwrap();
        let mut state = PrintState::new("");
        item.deref(&ctx.ops).as_ref().verify(&ctx).unwrap();
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
                %0 = arith.iconst true : int<1>
                %1 = arith.iconst false : int<1>
                %2 = arith.iadd %0, %1 : int<1>

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
}
