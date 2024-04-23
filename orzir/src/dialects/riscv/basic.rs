use std::fmt::{self, Write};

use orzir_core::{
    apint::ApInt, verification_error, ArenaPtr, Context, Dialect, Op, OpMetadata, Parse,
    RunVerifiers, Successor, Ty, Value, Verify,
};
use orzir_macros::{ControlFlow, DataFlow, Op, Parse, Print, RegionInterface, Verify};
use thiserror::Error;

use super::regs::IReg;
use crate::{
    dialects::std::builtin::Symbol,
    verifiers::{control_flow::*, *},
};

/// The immediate out of range error.
#[derive(Debug, Error)]
#[error("expected an immediate with width at most {0}, but got {1}")]
pub struct ImmOutOfRangeErr(pub usize, pub usize);

/// Implement a RISC-V immediate operation.
macro_rules! rv_immediate {
    ($mnemonic:literal, $name:ident, $imm_width:literal) => {
        #[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print)]
        #[mnemonic = $mnemonic]
        #[verifiers(
            NumResults<1>, NumOperands<1>, NumRegions<0>, SameResultTys, SameOperandTys,
            SameOperandAndResultTys, IntegerLikeOperands, OperandTysAre<IReg>, ResultTysAre<IReg>
        )]
        #[format(pattern = "{lhs}, {imm}", kind = "op", num_results = 1)]
        pub struct $name {
            #[metadata]
            metadata: OpMetadata,
            /// The result of the operation.
            #[result(0)]
            result: ArenaPtr<Value>,
            /// The left-hand side operand.
            #[operand(0)]
            lhs: ArenaPtr<Value>,
            /// The right-hand side immediate.
            imm: ApInt,
        }

        impl Verify for $name {
            fn verify(&self, ctx: &Context) -> orzir_core::VerificationResult<()> {
                self.run_verifiers(ctx)?;

                // verify the width of the immediate
                if self.imm.width() > $imm_width {
                    return verification_error!(ImmOutOfRangeErr($imm_width, self.imm.width()))
                        .into();
                }

                Ok(())
            }
        }
    };
}

rv_immediate!("rv.addi", AddiOp, 12);
rv_immediate!("rv.addiw", AddiwOp, 12);
rv_immediate!("rv.slli", SlliOp, 12);
rv_immediate!("rv.slliw", SlliwOp, 5);
rv_immediate!("rv.srli", SrliOp, 12);
rv_immediate!("rv.srliw", SrliwOp, 5);
rv_immediate!("rv.srai", SraiOp, 12);
rv_immediate!("rv.sraiw", SraiwOp, 5);
rv_immediate!("rv.xori", XoriOp, 12);
rv_immediate!("rv.ori", OriOp, 12);
rv_immediate!("rv.andi", AndiOp, 12);
rv_immediate!("rv.slti", SltiOp, 12);
rv_immediate!("rv.sltiu", SltiuOp, 12);

/// Represents the `zero` or `x0` register.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv.zero"]
#[verifiers(
    NumResults<1>, NumOperands<0>, NumRegions<0>,
    SameResultTys, ResultTysAre<IReg>
)]
#[format(pattern = "", kind = "op", num_results = 1)]
pub struct ZeroOp {
    #[metadata]
    metadata: OpMetadata,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
}

/// The jump instruction.
///
/// This does not correspond to a real RISC-V instruction, the most similar is
/// `j` pseudo instruction.
///
/// In a valid assembly code, there is no semantic for block arguments,
/// but the RISC-V dialect is designed to optimize the pre-register
/// allocation form of the code (which is still in SSA form), and thus
/// the successor can have a block argument.
///
/// However, when emitting the corresponding machine code, the block
/// argument should eliminated/hoisted.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv.jump"]
#[verifiers(NumResults<0>, NumOperands<0>, NumRegions<0>, NumSuccessors<1>, IsTerminator)]
#[format(pattern = "{succ}", kind = "op", num_results = 0)]
pub struct JumpOp {
    #[metadata]
    metadata: OpMetadata,

    /// The successor of the jump operation.
    #[successor(0)]
    succ: Successor,
}

#[derive(Parse, Print)]
#[format(pattern = "{self}")]
pub enum LoadPredicate {
    Lb,
    Lh,
    Lw,
    Lbu,
    Lhu,
    Ld,
    Lwu,
}

impl fmt::Display for LoadPredicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LoadPredicate::Lb => write!(f, "lb"),
            LoadPredicate::Lh => write!(f, "lh"),
            LoadPredicate::Lw => write!(f, "lw"),
            LoadPredicate::Lbu => write!(f, "lbu"),
            LoadPredicate::Lhu => write!(f, "lhu"),
            LoadPredicate::Ld => write!(f, "ld"),
            LoadPredicate::Lwu => write!(f, "lwu"),
        }
    }
}

#[derive(Debug, Error)]
#[error("invalid load predicate: {0}")]
pub struct InvalidLoadPredicateErr(String);

impl TryFrom<&str> for LoadPredicate {
    type Error = InvalidLoadPredicateErr;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "lb" => Ok(LoadPredicate::Lb),
            "lh" => Ok(LoadPredicate::Lh),
            "lw" => Ok(LoadPredicate::Lw),
            "lbu" => Ok(LoadPredicate::Lbu),
            "lhu" => Ok(LoadPredicate::Lhu),
            "ld" => Ok(LoadPredicate::Ld),
            "lwu" => Ok(LoadPredicate::Lwu),
            _ => Err(InvalidLoadPredicateErr(value.into())),
        }
    }
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv.load"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands,
    OperandTysAre<IReg>, ResultTysAre<IReg>
)]
#[format(pattern = "{pred} {base}, {offset}", kind = "op", num_results = 1)]
pub struct LoadOp {
    #[metadata]
    metadata: OpMetadata,
    /// The predicate of the load operation.
    pred: LoadPredicate,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The base address of the load operation.
    #[operand(0)]
    base: ArenaPtr<Value>,
    /// The offset immediate of the load operation.
    offset: ApInt,
}

/// Load symbol address pseudo instruction.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv.load.symbol_addr"]
#[verifiers(
    NumResults<1>, NumOperands<0>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands,
    OperandTysAre<IReg>, ResultTysAre<IReg>
)]
#[format(pattern = "{symbol}", kind = "op", num_results = 1)]
pub struct LoadSymbolAddrOp {
    #[metadata]
    metadata: OpMetadata,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The symbol to load the address of.
    symbol: Symbol,
}

/// Get address of a `memref` value.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv.load_addr"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys,
    OperandTysAre<crate::dialects::std::builtin::MemRefTy>,
    ResultTysAre<IReg>
)]
#[format(pattern = "{value}", kind = "op", num_results = 1)]
pub struct LoadAddrOp {
    #[metadata]
    metadata: OpMetadata,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The value to get the address of.
    #[operand(0)]
    value: ArenaPtr<Value>,
}

/// Load from symbol pseudo instruction.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv.load.symbol"]
#[verifiers(
    NumResults<1>, NumOperands<0>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands,
    OperandTysAre<IReg>, ResultTysAre<IReg>
)]
#[format(pattern = "{pred} {symbol}", kind = "op", num_results = 1)]
pub struct LoadSymbolOp {
    #[metadata]
    metadata: OpMetadata,
    /// The predicate of the load operation.
    pred: LoadPredicate,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The symbol to load from.
    symbol: Symbol,
}

#[derive(Parse, Print)]
#[format(pattern = "{self}")]
pub enum StorePredicate {
    Sb,
    Sh,
    Sw,
    Sd,
}

impl fmt::Display for StorePredicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StorePredicate::Sb => write!(f, "sb"),
            StorePredicate::Sh => write!(f, "sh"),
            StorePredicate::Sw => write!(f, "sw"),
            StorePredicate::Sd => write!(f, "sd"),
        }
    }
}

#[derive(Debug, Error)]
#[error("invalid store predicate: {0}")]
pub struct InvalidStorePredicateErr(String);

impl TryFrom<&str> for StorePredicate {
    type Error = InvalidStorePredicateErr;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "sb" => Ok(StorePredicate::Sb),
            "sh" => Ok(StorePredicate::Sh),
            "sw" => Ok(StorePredicate::Sw),
            "sd" => Ok(StorePredicate::Sd),
            _ => Err(InvalidStorePredicateErr(value.into())),
        }
    }
}

/// The store instruction.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv.store"]
#[verifiers(
    NumResults<0>, NumOperands<2>, NumRegions<0>,
    SameOperandTys, IntegerLikeOperands,
    OperandTysAre<IReg>, ResultTysAre<IReg>
)]
#[format(
    pattern = "{pred} {value}, {base}, {offset}",
    kind = "op",
    num_results = 0
)]
pub struct StoreOp {
    #[metadata]
    metadata: OpMetadata,
    /// The predicate of the store operation.
    pred: StorePredicate,
    /// The value to store.
    #[operand(0)]
    value: ArenaPtr<Value>,
    /// The base address of the store operation.
    #[operand(1)]
    base: ArenaPtr<Value>,
    /// The offset immediate of the store operation.
    offset: ApInt,
}

/// Store symbol pseudo instruction.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv.store.symbol"]
#[verifiers(
    NumResults<0>, NumOperands<1>, NumRegions<0>,
    SameOperandTys, IntegerLikeOperands,
    OperandTysAre<IReg>, ResultTysAre<IReg>
)]
#[format(pattern = "{pred} {value}, {symbol}", kind = "op", num_results = 0)]
pub struct StoreSymbolOp {
    #[metadata]
    metadata: OpMetadata,
    /// The predicate of the store operation.
    pred: StorePredicate,
    /// The value to store.
    #[operand(0)]
    value: ArenaPtr<Value>,
    /// The symbol to store to.
    symbol: Symbol,
}

#[derive(Parse, Print)]
#[format(pattern = "{self}")]
pub enum BranchPredicate {
    Beq,
    Bne,
    Blt,
    Bge,
    Bltu,
    Bgeu,
}

impl fmt::Display for BranchPredicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BranchPredicate::Beq => write!(f, "beq"),
            BranchPredicate::Bne => write!(f, "bne"),
            BranchPredicate::Blt => write!(f, "blt"),
            BranchPredicate::Bge => write!(f, "bge"),
            BranchPredicate::Bltu => write!(f, "bltu"),
            BranchPredicate::Bgeu => write!(f, "bgeu"),
        }
    }
}

#[derive(Debug, Error)]
#[error("invalid branch predicate: {0}")]
pub struct InvalidBranchPredicateErr(String);

impl TryFrom<&str> for BranchPredicate {
    type Error = InvalidBranchPredicateErr;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "beq" => Ok(BranchPredicate::Beq),
            "bne" => Ok(BranchPredicate::Bne),
            "blt" => Ok(BranchPredicate::Blt),
            "bge" => Ok(BranchPredicate::Bge),
            "bltu" => Ok(BranchPredicate::Bltu),
            "bgeu" => Ok(BranchPredicate::Bgeu),
            _ => Err(InvalidBranchPredicateErr(value.into())),
        }
    }
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv.br"]
#[verifiers(
    NumResults<0>, NumOperands<2>, NumRegions<0>, NumSuccessors<2>, IsTerminator
)]
#[format(
    pattern = "{pred} {lhs}, {rhs}, {then_succ}, {else_succ}",
    kind = "op",
    num_results = 0
)]
pub struct BranchOp {
    #[metadata]
    metadata: OpMetadata,
    /// The predicate of the branch operation.
    pred: BranchPredicate,
    /// The left-hand side operand.
    #[operand(0)]
    lhs: ArenaPtr<Value>,
    /// The right-hand side operand.
    #[operand(1)]
    rhs: ArenaPtr<Value>,
    /// The successor if the branch is taken.
    #[successor(0)]
    then_succ: Successor,
    /// The successor if the branch is not taken.
    #[successor(1)]
    else_succ: Successor,
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv.li"]
#[verifiers(NumResults<1>, NumOperands<0>, NumRegions<0>, SameResultTys, ResultTysAre<IReg>)] // IntegerLikeResults
#[format(pattern = "{value}", kind = "op", num_results = 1)]
pub struct LiOp {
    #[metadata]
    metadata: OpMetadata,
    /// The result of the operation.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The value of the integer constant.
    value: ApInt,
}

/// Implement a RISC-V binary operation.
macro_rules! rv_binary {
    ($mnemonic:literal, $name:ident) => {
        #[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
        #[mnemonic = $mnemonic]
        #[verifiers(
            NumResults<1>, NumOperands<2>, NumRegions<0>, SameResultTys, SameOperandTys,
            SameOperandAndResultTys, IntegerLikeOperands, OperandTysAre<IReg>, ResultTysAre<IReg>
        )]
        #[format(pattern = "{lhs}, {rhs}", kind = "op", num_results = 1)]
        pub struct $name {
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
    };
}

rv_binary!("rv.add", AddOp);
rv_binary!("rv.addw", AddwOp);
rv_binary!("rv.sub", SubOp);
rv_binary!("rv.subw", SubwOp);
rv_binary!("rv.sll", SllOp);
rv_binary!("rv.sllw", SllwOp);
rv_binary!("rv.srl", SrlOp);
rv_binary!("rv.srlw", SrlwOp);
rv_binary!("rv.sra", SraOp);
rv_binary!("rv.sraw", SrawOp);
rv_binary!("rv.xor", XorOp);
rv_binary!("rv.or", OrOp);
rv_binary!("rv.and", AndOp);
rv_binary!("rv.slt", SltOp);
rv_binary!("rv.sltu", SltuOp);

pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new("rv".into());
    ctx.dialects.insert("rv".into(), dialect);

    ZeroOp::register(ctx, ZeroOp::parse);

    LoadOp::register(ctx, LoadOp::parse);
    LoadAddrOp::register(ctx, LoadAddrOp::parse);
    LoadSymbolAddrOp::register(ctx, LoadSymbolAddrOp::parse);
    LoadSymbolOp::register(ctx, LoadSymbolOp::parse);

    StoreOp::register(ctx, StoreOp::parse);
    StoreSymbolOp::register(ctx, StoreSymbolOp::parse);

    AddiOp::register(ctx, AddiOp::parse);
    JumpOp::register(ctx, JumpOp::parse);
    LiOp::register(ctx, LiOp::parse);
    AddiwOp::register(ctx, AddiwOp::parse);
    SlliOp::register(ctx, SlliOp::parse);
    SlliwOp::register(ctx, SlliwOp::parse);
    SrliOp::register(ctx, SrliOp::parse);
    SrliwOp::register(ctx, SrliwOp::parse);
    SraiOp::register(ctx, SraiOp::parse);
    SraiwOp::register(ctx, SraiwOp::parse);
    XoriOp::register(ctx, XoriOp::parse);
    OriOp::register(ctx, OriOp::parse);
    AndiOp::register(ctx, AndiOp::parse);
    SltiOp::register(ctx, SltiOp::parse);
    SltiuOp::register(ctx, SltiuOp::parse);

    AddOp::register(ctx, AddOp::parse);
    AddwOp::register(ctx, AddwOp::parse);
    SubOp::register(ctx, SubOp::parse);
    SubwOp::register(ctx, SubwOp::parse);
    SllOp::register(ctx, SllOp::parse);
    SllwOp::register(ctx, SllwOp::parse);
    SrlOp::register(ctx, SrlOp::parse);
    SrlwOp::register(ctx, SrlwOp::parse);
    SraOp::register(ctx, SraOp::parse);
    SrawOp::register(ctx, SrawOp::parse);
    XorOp::register(ctx, XorOp::parse);
    OrOp::register(ctx, OrOp::parse);
    AndOp::register(ctx, AndOp::parse);
    SltOp::register(ctx, SltOp::parse);
    SltuOp::register(ctx, SltuOp::parse);

    BranchOp::register(ctx, BranchOp::parse);

    IReg::register(ctx, IReg::parse);
}

#[cfg(test)]
mod tests {
    use orzir_core::{Context, OpObj, Parse, ParseState, Print, PrintState, TokenStream};

    use crate::dialects::{riscv::basic, std::register_std_dialects};

    #[test]
    fn test_0() {
        let src = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../examples/rv.orzir"));

        let stream = TokenStream::new(src);
        let mut state = ParseState::new(stream);
        let mut ctx = Context::default();

        basic::register(&mut ctx);
        register_std_dialects(&mut ctx);

        let op = OpObj::parse(&mut ctx, &mut state).unwrap();
        let mut state = PrintState::new("    ");
        op.deref(&ctx.ops).as_ref().verify(&ctx).unwrap();
        op.deref(&ctx.ops).print(&ctx, &mut state).unwrap();
        println!("{}", state.buffer);
    }
}
