use std::fmt::{self, Write};

use orzir_core::{apint::ApInt, ArenaPtr, Context, Dialect, Op, OpMetadata, Parse, Symbol, Value};
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

#[derive(Parse, Print)]
#[format(pattern = "{self}")]
pub enum FCvtIntFmt {
    W,
    WU,
    L,
    LU,
}

impl fmt::Display for FCvtIntFmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FCvtIntFmt::W => write!(f, "w"),
            FCvtIntFmt::WU => write!(f, "wu"),
            FCvtIntFmt::L => write!(f, "l"),
            FCvtIntFmt::LU => write!(f, "lu"),
        }
    }
}

impl TryFrom<&str> for FCvtIntFmt {
    type Error = InvalidFloatFmtError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "w" => Ok(FCvtIntFmt::W),
            "wu" => Ok(FCvtIntFmt::WU),
            "l" => Ok(FCvtIntFmt::L),
            "lu" => Ok(FCvtIntFmt::LU),
            _ => Err(InvalidFloatFmtError(value.to_string())),
        }
    }
}

/// Float to int conversion instruction.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv_f.fcvt.f2i"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, OperandTysAre<FReg>, ResultTysAre<IReg>
)]
#[format(pattern = "{from} to {to} {operand}", kind = "op", num_results = 1)]
pub struct FCvtF2IOp {
    #[metadata]
    metadata: OpMetadata,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The format of the floating point number.
    from: FloatFmt,
    /// The format of the integer number.
    to: FCvtIntFmt,
    /// The operand to convert.
    #[operand(0)]
    operand: ArenaPtr<Value>,
}

/// Int to float conversion instruction.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv_f.fcvt.i2f"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, OperandTysAre<IReg>, ResultTysAre<FReg>
)]
#[format(pattern = "{from} to {to} {operand}", kind = "op", num_results = 1)]
pub struct FCvtI2FOp {
    #[metadata]
    metadata: OpMetadata,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The format of the integer number.
    from: FCvtIntFmt,
    /// The format of the floating point number.
    to: FloatFmt,
    /// The operand to convert.
    #[operand(0)]
    operand: ArenaPtr<Value>,
}

/// Float to float conversion instruction.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv_f.fcvt.f2f"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, OperandTysAre<FReg>, ResultTysAre<FReg>
)]
#[format(pattern = "{from} to {to} {operand}", kind = "op", num_results = 1)]
pub struct FCvtF2FOp {
    #[metadata]
    metadata: OpMetadata,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The format of the floating point number.
    from: FloatFmt,
    /// The format of the floating point number.
    to: FloatFmt,
    /// The operand to convert.
    #[operand(0)]
    operand: ArenaPtr<Value>,
}

#[derive(Parse, Print)]
#[format(pattern = "{self}")]
pub enum FMvFmt {
    H,
    W,
    D,
    /// The `fmv.x.q` and `fmv.q.x` are stated in the manual as below:
    /// > FMV.X.Q and FMV.Q.X instructions are not provided in RV32 or RV64, so
    /// > quad-precision bit patterns must be moved to the integer registers via
    /// > memory.
    /// ---
    /// > RV128 will support FMV.X.Q and FMV.Q.X in the Q extension.
    Q,
}

impl fmt::Display for FMvFmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FMvFmt::H => write!(f, "h"),
            FMvFmt::W => write!(f, "w"),
            FMvFmt::D => write!(f, "d"),
            FMvFmt::Q => write!(f, "q"),
        }
    }
}

impl TryFrom<&str> for FMvFmt {
    type Error = InvalidFloatFmtError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "h" => Ok(FMvFmt::H),
            "w" => Ok(FMvFmt::W),
            "d" => Ok(FMvFmt::D),
            "q" => Ok(FMvFmt::Q),
            _ => Err(InvalidFloatFmtError(value.to_string())),
        }
    }
}

/// Float move to integer instruction.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv_f.fmv.f2i"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, OperandTysAre<FReg>, ResultTysAre<IReg>
)]
#[format(pattern = "{from} {operand}", kind = "op", num_results = 1)]
pub struct FMvF2IOp {
    #[metadata]
    metadata: OpMetadata,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The format of the floating point number.
    from: FMvFmt,
    /// The operand to convert.
    #[operand(0)]
    operand: ArenaPtr<Value>,
}

/// Integer move to float instruction.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv_f.fmv.i2f"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, OperandTysAre<IReg>, ResultTysAre<FReg>
)]
#[format(pattern = "{to} {operand}", kind = "op", num_results = 1)]
pub struct FMvI2FOp {
    #[metadata]
    metadata: OpMetadata,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The format of the floating point number.
    to: FMvFmt,
    /// The operand to convert.
    #[operand(0)]
    operand: ArenaPtr<Value>,
}

#[derive(Parse, Print)]
#[format(pattern = "{self}")]
pub enum FLoadPredicate {
    Lh,
    Ls,
    Ld,
    Lq,
}

impl fmt::Display for FLoadPredicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FLoadPredicate::Lh => write!(f, "lh"),
            FLoadPredicate::Ls => write!(f, "ls"),
            FLoadPredicate::Ld => write!(f, "ld"),
            FLoadPredicate::Lq => write!(f, "lq"),
        }
    }
}

impl TryFrom<&str> for FLoadPredicate {
    type Error = InvalidFloatFmtError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "lh" => Ok(FLoadPredicate::Lh),
            "ls" => Ok(FLoadPredicate::Ls),
            "ld" => Ok(FLoadPredicate::Ld),
            "lq" => Ok(FLoadPredicate::Lq),
            _ => Err(InvalidFloatFmtError(value.to_string())),
        }
    }
}

/// Float load instruction.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv_f.fload"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, OperandTysAre<IReg>, ResultTysAre<FReg>
)]
#[format(pattern = "{pred} {addr}, {offset}", kind = "op", num_results = 1)]
pub struct FLoadOp {
    #[metadata]
    metadata: OpMetadata,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The predicate of the load.
    pred: FLoadPredicate,
    /// The address to load.
    #[operand(0)]
    addr: ArenaPtr<Value>,
    /// The offset to load.
    offset: ApInt,
}

#[derive(Parse, Print)]
#[format(pattern = "{self}")]
pub enum FStorePredicate {
    Sh,
    Ss,
    Sd,
    Sq,
}

impl fmt::Display for FStorePredicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FStorePredicate::Sh => write!(f, "sh"),
            FStorePredicate::Ss => write!(f, "ss"),
            FStorePredicate::Sd => write!(f, "sd"),
            FStorePredicate::Sq => write!(f, "sq"),
        }
    }
}

impl TryFrom<&str> for FStorePredicate {
    type Error = InvalidFloatFmtError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "sh" => Ok(FStorePredicate::Sh),
            "ss" => Ok(FStorePredicate::Ss),
            "sd" => Ok(FStorePredicate::Sd),
            "sq" => Ok(FStorePredicate::Sq),
            _ => Err(InvalidFloatFmtError(value.to_string())),
        }
    }
}

/// Float store instruction.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv_f.fstore"]
#[verifiers(
    NumResults<0>, NumOperands<2>, NumRegions<0>,
    SameOperandTys, OperandTysAre<FReg>
)]
#[format(
    pattern = "{pred} {value}, {base}, {offset}",
    kind = "op",
    num_results = 0
)]
pub struct FStoreOp {
    #[metadata]
    metadata: OpMetadata,
    /// The predicate of the store.
    pred: FStorePredicate,
    /// The value to store.
    #[operand(0)]
    value: ArenaPtr<Value>,
    /// The base address to store.
    #[operand(1)]
    base: ArenaPtr<Value>,
    /// The offset to store.
    offset: ApInt,
}

/// Load float from symbol
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv_f.fload.symbol"]
#[verifiers(
    NumResults<1>, NumOperands<0>, NumRegions<0>,
    SameResultTys, ResultTysAre<FReg>
)]
#[format(pattern = "{pred} {symbol}", kind = "op", num_results = 1)]
pub struct FLoadSymbolOp {
    #[metadata]
    metadata: OpMetadata,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The predicate of the load.
    pred: FLoadPredicate,
    /// The symbol to load.
    symbol: Symbol,
}

/// Store float to symbol
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv_f.fstore.symbol"]
#[verifiers(
    NumResults<0>, NumOperands<1>, NumRegions<0>,
    SameOperandTys, OperandTysAre<FReg>
)]
#[format(pattern = "{pred} {value}, {symbol}", kind = "op", num_results = 0)]
pub struct FStoreSymbolOp {
    #[metadata]
    metadata: OpMetadata,
    /// The predicate of the store.
    pred: FStorePredicate,
    /// The value to store.
    #[operand(0)]
    value: ArenaPtr<Value>,
    /// The symbol to store.
    symbol: Symbol,
}

pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new("rv_f".into());
    ctx.register_dialect(dialect);

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

    FCvtF2IOp::register(ctx, FCvtF2IOp::parse);
    FCvtI2FOp::register(ctx, FCvtI2FOp::parse);
    FCvtF2FOp::register(ctx, FCvtF2FOp::parse);

    FMvF2IOp::register(ctx, FMvF2IOp::parse);
    FMvI2FOp::register(ctx, FMvI2FOp::parse);

    FLoadOp::register(ctx, FLoadOp::parse);
    FStoreOp::register(ctx, FStoreOp::parse);
    FLoadSymbolOp::register(ctx, FLoadSymbolOp::parse);
    FStoreSymbolOp::register(ctx, FStoreSymbolOp::parse);
}
