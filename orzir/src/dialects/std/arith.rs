use core::fmt;
use std::fmt::Write;

use orzir_core::{
    apint::ApInt, parse_error, token_wildcard, verification_error, ArenaPtr, Context, Dialect, Op,
    OpMetadata, Parse, ParseErrorKind, ParseResult, ParseState, Print, PrintState, RunVerifiers,
    TokenKind, Typed, Value, Verify,
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
#[verifiers(NumResults<1>, NumOperands<0>, NumRegions<0>, IntegerLikeResults)]
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
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands, IntegerLikeResults,
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
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    FloatLikeOperands, FloatLikeResults,
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
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands, IntegerLikeResults,
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
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    FloatLikeOperands, FloatLikeResults,
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
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands, IntegerLikeResults,
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
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    FloatLikeOperands, FloatLikeResults,
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
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    FloatLikeOperands, FloatLikeResults,
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

/// A integer and operation
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "arith.iand"]
#[verifiers(
    NumResults<1>, NumOperands<2>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands, IntegerLikeResults
)]
#[format(pattern = "{lhs} , {rhs}", kind = "op", num_results = 1)]
pub struct IAndOp {
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

/// A integer or operation
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "arith.ior"]
#[verifiers(
    NumResults<1>, NumOperands<2>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands, IntegerLikeResults
)]
#[format(pattern = "{lhs} , {rhs}", kind = "op", num_results = 1)]
pub struct IOrOp {
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

/// A integer xor operation
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "arith.ixor"]
#[verifiers(
    NumResults<1>, NumOperands<2>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands, IntegerLikeResults
)]
#[format(pattern = "{lhs} , {rhs}", kind = "op", num_results = 1)]
pub struct IXorOp {
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

/// Bitcast operation.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "arith.bitcast"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys
)]
#[format(pattern = "{from}", kind = "op", num_results = 1)]
pub struct BitcastOp {
    #[metadata]
    metadata: OpMetadata,
    /// From value
    #[operand(0)]
    from: ArenaPtr<Value>,
    /// To value
    ///
    /// The destination type is determined by the type of the result.
    #[result(0)]
    to: ArenaPtr<Value>,
}

/// The cmp predicate for comparison operations.
pub enum ICmpPredicate {
    Equal,
    NotEqual,
    SignedLess,
    SignedLessEqual,
    SignedGreater,
    SignedGreaterEqual,
    UnsignedLess,
    UnsignedLessEqual,
    UnsignedGreater,
    UnsignedGreaterEqual,
}

impl fmt::Display for ICmpPredicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            ICmpPredicate::Equal => "eq",
            ICmpPredicate::NotEqual => "ne",
            ICmpPredicate::SignedLess => "slt",
            ICmpPredicate::SignedLessEqual => "sle",
            ICmpPredicate::SignedGreater => "sgt",
            ICmpPredicate::SignedGreaterEqual => "sge",
            ICmpPredicate::UnsignedLess => "ult",
            ICmpPredicate::UnsignedLessEqual => "ule",
            ICmpPredicate::UnsignedGreater => "ugt",
            ICmpPredicate::UnsignedGreaterEqual => "uge",
        };

        write!(f, "{}", s)
    }
}

#[derive(Debug, Error)]
#[error("invalid icmp predicate: {0}")]
pub struct InvalidICmpPredicate(String);

impl TryFrom<&str> for ICmpPredicate {
    type Error = InvalidICmpPredicate;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "eq" => Ok(ICmpPredicate::Equal),
            "ne" => Ok(ICmpPredicate::NotEqual),
            "slt" => Ok(ICmpPredicate::SignedLess),
            "sle" => Ok(ICmpPredicate::SignedLessEqual),
            "sgt" => Ok(ICmpPredicate::SignedGreater),
            "sge" => Ok(ICmpPredicate::SignedGreaterEqual),
            "ult" => Ok(ICmpPredicate::UnsignedLess),
            "ule" => Ok(ICmpPredicate::UnsignedLessEqual),
            "ugt" => Ok(ICmpPredicate::UnsignedGreater),
            "uge" => Ok(ICmpPredicate::UnsignedGreaterEqual),
            _ => Err(InvalidICmpPredicate(value.to_string())),
        }
    }
}

impl Parse for ICmpPredicate {
    type Item = Self;

    fn parse(_: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        let token = state.stream.consume()?;
        if let TokenKind::Tokenized(s) = token.kind {
            let pred =
                ICmpPredicate::try_from(s.as_str()).map_err(|e| parse_error!(token.span, e))?;
            Ok(pred)
        } else {
            parse_error!(
                token.span,
                ParseErrorKind::InvalidToken(vec![token_wildcard!("...")].into(), token.kind)
            )
            .into()
        }
    }
}

impl Print for ICmpPredicate {
    fn print(&self, _: &Context, state: &mut PrintState) -> orzir_core::PrintResult<()> {
        write!(state.buffer, "{}", self)?;
        Ok(())
    }
}

/// An integer comparison operation
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "arith.icmp"]
#[verifiers(
    NumResults<1>, NumOperands<2>, NumRegions<0>,
    SameResultTys, SameOperandTys, IntegerLikeOperands,
    IntegerLikeResults
)]
#[format(pattern = "{pred} , {lhs} , {rhs}", kind = "op", num_results = 1)]
pub struct ICmpOp {
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
    /// The predicate for the comparison.
    pred: ICmpPredicate,
}

// /// A float comparison operation
// #[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
// #[mnemonic = "arith.fcmp"]
// #[verifiers(
//     NumResults<1>, NumOperands<2>, NumRegions<0>,
//     SameResultTys, SameOperandTys, FloatLikeOperands, BoolLikeResults
// )]
// #[format(pattern = "{predicate} , {lhs} , {rhs}", kind = "op", num_results = 1)]
// pub struct FCmpOp {
//     #[metadata]
//     metadata: OpMetadata,
//     /// The result of the operation.
//     #[result(0)]
//     result: ArenaPtr<Value>,
//     /// The left-hand side operand.
//     #[operand(0)]
//     lhs: ArenaPtr<Value>,
//     /// The right-hand side operand.
//     #[operand(1)]
//     rhs: ArenaPtr<Value>,
//     /// The predicate for the comparison.
//     predicate: ComparisonPredicate,
// }

// /// A integer comparison operation
// #[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
// #[mnemonic = "arith.icmp"]
// #[verifiers(
//     NumResults<1>, NumOperands<2>, NumRegions<0>,
//     SameResultTys, SameOperandTys, IntegerLikeOperands, BoolLikeResults
// )]
// #[format(pattern = "{predicate} , {lhs} , {rhs}", kind = "op", num_results = 1)]
// pub struct ICmpOp {
//     #[metadata]
//     metadata: OpMetadata,
//     /// The result of the operation.
//     #[result(0)]
//     result: ArenaPtr<Value>,
//     /// The left-hand side operand.
//     #[operand(0)]
//     lhs: ArenaPtr<Value>,
//     /// The right-hand side operand.
//     #[operand(1)]
//     rhs: ArenaPtr<Value>,
//     /// The predicate for the comparison.
//     predicate: ComparisonPredicate,
// }

// /// A fp2si operation
// #[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
// #[mnemonic = "arith.fptosi"]
// #[verifiers(
//     NumResults<1>, NumOperands<1>, NumRegions<0>,
//     SameResultTys, SameOperandTys, FloatLikeOperands, IntegerLikeResults
// )]
// #[format(pattern = "{in_value} : {in_type} to {out_type}", kind = "op", num_results = 1)]
// pub struct FPToSIOp {
//     #[metadata]
//     metadata: OpMetadata,
//     /// The input value.
//     #[operand(0)]
//     in_value: ArenaPtr<Value>,
//     /// The input type.
//     in_type: Box<dyn Ty>,
//     /// The output type.
//     out_type: Box<dyn Ty>,
//     /// The result of the operation.
//     #[result(0)]
//     out_value: ArenaPtr<Value>,
// }

// /// A si2fp operation
// #[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
// #[mnemonic = "arith.sitofp"]
// #[verifiers(
//     NumResults<1>, NumOperands<1>, NumRegions<0>,
//     SameResultTys, SameOperandTys, IntegerLikeOperands, FloatLikeResults
// )]
// #[format(pattern = "{in_value} : {in_type} to {out_type}", kind = "op", num_results = 1)]
// pub struct SIToFPOp {
//     #[metadata]
//     metadata: OpMetadata,
//     /// The input value.
//     #[operand(0)]
//     in_value: ArenaPtr<Value>,
//     /// The input type.
//     in_type: Box<dyn Ty>,
//     /// The output type.
//     out_type: Box<dyn Ty>,
//     /// The result of the operation.
//     #[result(0)]
//     out_value: ArenaPtr<Value>,
// }

/// Floating-point negation
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "arith.fneg"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    FloatLikeOperands, FloatLikeResults
)]
#[format(pattern = "{operand}", kind = "op", num_results = 1)]
pub struct FNegOp {
    #[metadata]
    metadata: OpMetadata,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The operand to negate.
    #[operand(0)]
    operand: ArenaPtr<Value>,
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
    IAndOp::register(ctx, IAndOp::parse);
    IOrOp::register(ctx, IOrOp::parse);
    IXorOp::register(ctx, IXorOp::parse);
    FNegOp::register(ctx, FNegOp::parse);
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
