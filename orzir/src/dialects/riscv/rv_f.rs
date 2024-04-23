use std::fmt::{self, Write};

use orzir_core::{ArenaPtr, Context, Dialect, Op, OpMetadata, Parse, Value};
use orzir_macros::{ControlFlow, DataFlow, Op, Parse, Print, RegionInterface, Verify};
use thiserror::Error;

use super::regs::{FReg, IReg};
use crate::verifiers::*;

/// The floating point kind.
#[derive(Parse, Print)]
#[format(pattern = "{self}")]
pub enum FloatFmt {
    H,
    S,
    D,
    Q,
}

impl fmt::Display for FloatFmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FloatFmt::H => write!(f, "h"),
            FloatFmt::S => write!(f, "s"),
            FloatFmt::D => write!(f, "d"),
            FloatFmt::Q => write!(f, "q"),
        }
    }
}

#[derive(Error, Debug)]
#[error("invalid float kind: {0}")]
pub struct InvalidFloatFmtError(String);

impl TryFrom<&str> for FloatFmt {
    type Error = InvalidFloatFmtError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "h" => Ok(FloatFmt::H),
            "s" => Ok(FloatFmt::S),
            "d" => Ok(FloatFmt::D),
            "q" => Ok(FloatFmt::Q),
            _ => Err(InvalidFloatFmtError(value.to_string())),
        }
    }
}

#[rustfmt::skip]
macro_rules! rvf_fused {
    ($mnemonic:literal, $name:ident) => {
        #[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
        #[mnemonic = $mnemonic]
        #[verifiers(
            NumResults<1>, NumOperands<3>, NumRegions<0>, SameResultTys, SameOperandTys,
            SameOperandAndResultTys, OperandTysAre<FReg>, ResultTysAre<FReg>
        )]
        #[format(pattern = "{fmt} {rs1}, {rs2}, {rs3}", kind = "op", num_results = 1)]
        pub struct $name {
            #[metadata]
            metadata: OpMetadata,
            /// The result of the operation.
            #[result(0)]
            result: ArenaPtr<Value>,
            /// The format of the floating point number.
            fmt: FloatFmt,
            /// rs1, lhs for mul
            #[operand(0)]
            rs1: ArenaPtr<Value>,
            /// rs2, rhs for mul
            #[operand(1)]
            rs2: ArenaPtr<Value>,
            /// rs3
            #[operand(2)]
            rs3: ArenaPtr<Value>,
        }
    };
}

#[rustfmt::skip]
macro_rules! rvf_binary {
    ($mnemonic:literal, $name:ident) => {
        #[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
        #[mnemonic = $mnemonic]
        #[verifiers(
            NumResults<1>, NumOperands<2>, NumRegions<0>, SameResultTys, SameOperandTys,
            SameOperandAndResultTys, OperandTysAre<FReg>, ResultTysAre<FReg>
        )]
        #[format(pattern = "{fmt} {rs1}, {rs2}", kind = "op", num_results = 1)]
        pub struct $name {
            #[metadata]
            metadata: OpMetadata,
            /// The result of the operation.
            #[result(0)]
            result: ArenaPtr<Value>,
            /// The format of the floating point number.
            fmt: FloatFmt,
            /// lhs
            #[operand(0)]
            rs1: ArenaPtr<Value>,
            /// rhs
            #[operand(1)]
            rs2: ArenaPtr<Value>,
        }
    };
}

rvf_fused!("rv_f.madd", MAddOp);
rvf_fused!("rv_f.msub", MSubOp);
rvf_fused!("rv_f.nmadd", NMAddOp);
rvf_fused!("rv_f.nmsub", NMSubOp);

rvf_binary!("rv_f.fadd", FAddOp);
rvf_binary!("rv_f.fsub", FSubOp);
rvf_binary!("rv_f.fmul", FMulOp);
rvf_binary!("rv_f.fdiv", FDivOp);
rvf_binary!("rv_f.fmin", FMinOp);
rvf_binary!("rv_f.fmax", FMaxOp);
rvf_binary!("rv_f.fsgnj", FSgnjOp);
rvf_binary!("rv_f.fsgnjn", FSgnjnOp);
rvf_binary!("rv_f.fsgnjx", FSgnjxOp);

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv_f.sqrt"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    OperandTysAre<FReg>,ResultTysAre<FReg>
)]
#[format(pattern = "{fmt} {operand}", kind = "op", num_results = 1)]
pub struct FSqrtOp {
    #[metadata]
    metadata: OpMetadata,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The format of the floating point number.
    fmt: FloatFmt,
    /// The operand
    #[operand(0)]
    operand: ArenaPtr<Value>,
}

#[derive(Parse, Print)]
#[format(pattern = "{self}")]
pub enum FCmpPredicate {
    Eq,
    Lt,
    Le,
}

impl fmt::Display for FCmpPredicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FCmpPredicate::Eq => write!(f, "eq"),
            FCmpPredicate::Lt => write!(f, "lt"),
            FCmpPredicate::Le => write!(f, "le"),
        }
    }
}

impl TryFrom<&str> for FCmpPredicate {
    type Error = InvalidFloatFmtError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "eq" => Ok(FCmpPredicate::Eq),
            "lt" => Ok(FCmpPredicate::Lt),
            "le" => Ok(FCmpPredicate::Le),
            _ => Err(InvalidFloatFmtError(value.to_string())),
        }
    }
}

/// Float comparison instruction.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv_f.fcmp"]
#[verifiers(
    NumResults<1>, NumOperands<2>, NumRegions<0>,
    SameResultTys, SameOperandTys, OperandTysAre<FReg>, ResultTysAre<IReg>
)]
#[format(pattern = "{pred} {fmt} {lhs}, {rhs}", kind = "op", num_results = 1)]
pub struct FCmpOp {
    #[metadata]
    metadata: OpMetadata,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The predicate of the comparison.
    pred: FCmpPredicate,
    /// The format of the floating point number.
    fmt: FloatFmt,
    /// The lhs for comparison
    #[operand(0)]
    lhs: ArenaPtr<Value>,
    /// The rhs for comparison
    #[operand(1)]
    rhs: ArenaPtr<Value>,
}

/// Float class instruction
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv_f.fclass"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, OperandTysAre<FReg>, ResultTysAre<IReg>
)]
#[format(pattern = "{fmt} {operand}", kind = "op", num_results = 1)]
pub struct FClassOp {
    #[metadata]
    metadata: OpMetadata,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The format of the floating point number.
    fmt: FloatFmt,
    /// The operand to classify.
    #[operand(0)]
    operand: ArenaPtr<Value>,
}

pub fn register(ctx: &mut Context) {
    ctx.dialects
        .insert("rv_f".into(), Dialect::new("rv_f".into()));

    MAddOp::register(ctx, MAddOp::parse);
    MSubOp::register(ctx, MSubOp::parse);
    NMAddOp::register(ctx, NMAddOp::parse);
    NMSubOp::register(ctx, NMSubOp::parse);

    FAddOp::register(ctx, FAddOp::parse);
    FSubOp::register(ctx, FSubOp::parse);
    FMulOp::register(ctx, FMulOp::parse);
    FDivOp::register(ctx, FDivOp::parse);
    FMinOp::register(ctx, FMinOp::parse);
    FMaxOp::register(ctx, FMaxOp::parse);
    FSgnjOp::register(ctx, FSgnjOp::parse);
    FSgnjnOp::register(ctx, FSgnjnOp::parse);
    FSgnjxOp::register(ctx, FSgnjxOp::parse);

    FSqrtOp::register(ctx, FSqrtOp::parse);

    FCmpOp::register(ctx, FCmpOp::parse);
    FClassOp::register(ctx, FClassOp::parse);
}
