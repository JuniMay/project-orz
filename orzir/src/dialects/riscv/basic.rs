use std::fmt::{self, Write};

use orzir_core::{
    apint::ApInt, parse_error, token_wildcard, verification_error, ArenaPtr, Context, Dialect, Op,
    OpMetadata, Parse, ParseErrorKind, ParseResult, ParseState, Print, PrintResult, PrintState,
    RunVerifiers, Successor, TokenKind, Ty, Value, Verify,
};
use orzir_macros::{ControlFlow, DataFlow, Op, Parse, Print, RegionInterface, Verify};
use thiserror::Error;

use super::regs::IReg;
use crate::verifiers::{control_flow::*, *};

#[derive(Debug, Error)]
#[error("expected an immediate with width at most {0}, but got {1}")]
pub struct ImmOutOfRangeErr(pub usize, pub usize);

/// Implement a RISC-V immediate operation.
macro_rules! rv_immediate {
    ($mnemonic:literal, $name:ident, $imm_width:literal) => {
        #[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print)]
        #[mnemonic = $mnemonic]
        #[verifiers(
                            NumResults<1>, NumOperands<1>, NumRegions<0>,
                            SameResultTys, SameOperandTys, SameOperandAndResultTys,
                            IntegerLikeOperands, OperandTysAre<IReg>, ResultTysAre<IReg>
                        )]
        #[format(pattern = "{lhs} , {imm}", kind = "op", num_results = 1)]
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

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv.jmp"]
#[verifiers(NumResults<0>, NumOperands<0>, NumRegions<0>, NumSuccessors<1>, IsTerminator)]
#[format(pattern = "{succ}", kind = "op", num_results = 0)]
pub struct JmpOp {
    #[metadata]
    metadata: OpMetadata,

    /// The successor of the jump operation.
    ///
    /// In a valid assembly code, there is no semantic for block arguments,
    /// but the RISC-V dialect is designed to optimize the pre-register
    /// allocation form of the code (which is still in SSA form), and thus
    /// the successor can have a block argument.
    ///
    /// However, when emitting the corresponding machine code, the block
    /// argument should eliminated/hoisted.
    #[successor(0)]
    succ: Successor,
}

pub enum LoadPredicate {
    LB,
    LH,
    LW,
    LBU,
    LHU,
    LD,
    LWU,
}

impl fmt::Display for LoadPredicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LoadPredicate::LB => write!(f, "lb"),
            LoadPredicate::LH => write!(f, "lh"),
            LoadPredicate::LW => write!(f, "lw"),
            LoadPredicate::LBU => write!(f, "lbu"),
            LoadPredicate::LHU => write!(f, "lhu"),
            LoadPredicate::LD => write!(f, "ld"),
            LoadPredicate::LWU => write!(f, "lwu"),
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
            "lb" => Ok(LoadPredicate::LB),
            "lh" => Ok(LoadPredicate::LH),
            "lw" => Ok(LoadPredicate::LW),
            "lbu" => Ok(LoadPredicate::LBU),
            "lhu" => Ok(LoadPredicate::LHU),
            "ld" => Ok(LoadPredicate::LD),
            "lwu" => Ok(LoadPredicate::LWU),
            _ => Err(InvalidLoadPredicateErr(value.into())),
        }
    }
}

impl Parse for LoadPredicate {
    type Item = Self;

    fn parse(_: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        let token = state.stream.consume()?;
        if let TokenKind::Tokenized(s) = token.kind {
            let pred =
                LoadPredicate::try_from(s.as_str()).map_err(|e| parse_error!(token.span, e))?;
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

impl Print for LoadPredicate {
    fn print(&self, _: &Context, state: &mut PrintState) -> PrintResult<()> {
        write!(state.buffer, "{}", self)?;
        Ok(())
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
#[format(pattern = "{pred} , {base} , {offset}", kind = "op", num_results = 1)]
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

pub enum StorePredicate {
    SB,
    SH,
    SW,
    SD,
}

impl fmt::Display for StorePredicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StorePredicate::SB => write!(f, "sb"),
            StorePredicate::SH => write!(f, "sh"),
            StorePredicate::SW => write!(f, "sw"),
            StorePredicate::SD => write!(f, "sd"),
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
            "sb" => Ok(StorePredicate::SB),
            "sh" => Ok(StorePredicate::SH),
            "sw" => Ok(StorePredicate::SW),
            "sd" => Ok(StorePredicate::SD),
            _ => Err(InvalidStorePredicateErr(value.into())),
        }
    }
}

impl Parse for StorePredicate {
    type Item = Self;

    fn parse(_: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        let token = state.stream.consume()?;
        if let TokenKind::Tokenized(s) = token.kind {
            let pred =
                StorePredicate::try_from(s.as_str()).map_err(|e| parse_error!(token.span, e))?;
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

impl Print for StorePredicate {
    fn print(&self, _: &Context, state: &mut PrintState) -> PrintResult<()> {
        write!(state.buffer, "{}", self)?;
        Ok(())
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
    pattern = "{pred} , {value} , {base} , {offset}",
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

pub enum BranchPredicate {
    BEQ,
    BNE,
    BLT,
    BGE,
    BLTU,
    BGEU,
}

impl fmt::Display for BranchPredicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BranchPredicate::BEQ => write!(f, "beq"),
            BranchPredicate::BNE => write!(f, "bne"),
            BranchPredicate::BLT => write!(f, "blt"),
            BranchPredicate::BGE => write!(f, "bge"),
            BranchPredicate::BLTU => write!(f, "bltu"),
            BranchPredicate::BGEU => write!(f, "bgeu"),
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
            "beq" => Ok(BranchPredicate::BEQ),
            "bne" => Ok(BranchPredicate::BNE),
            "blt" => Ok(BranchPredicate::BLT),
            "bge" => Ok(BranchPredicate::BGE),
            "bltu" => Ok(BranchPredicate::BLTU),
            "bgeu" => Ok(BranchPredicate::BGEU),
            _ => Err(InvalidBranchPredicateErr(value.into())),
        }
    }
}

impl Parse for BranchPredicate {
    type Item = Self;

    fn parse(_: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        let token = state.stream.consume()?;
        if let TokenKind::Tokenized(s) = token.kind {
            let pred =
                BranchPredicate::try_from(s.as_str()).map_err(|e| parse_error!(token.span, e))?;
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

impl Print for BranchPredicate {
    fn print(&self, _: &Context, state: &mut PrintState) -> PrintResult<()> {
        write!(state.buffer, "{}", self)?;
        Ok(())
    }
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv.br"]
#[verifiers(
    NumResults<0>, NumOperands<2>, NumRegions<0>, NumSuccessors<2>, IsTerminator
)]
#[format(
    pattern = "{pred} , {lhs} , {rhs} , {then_succ} , {else_succ}",
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
                            NumResults<1>, NumOperands<2>, NumRegions<0>,
                            SameResultTys, SameOperandTys, SameOperandAndResultTys,
                            IntegerLikeOperands, OperandTysAre<IReg>, ResultTysAre<IReg>
                        )]
        #[format(pattern = "{lhs} , {rhs}", kind = "op", num_results = 1)]
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

    AddiOp::register(ctx, AddiOp::parse);
    JmpOp::register(ctx, JmpOp::parse);
    LoadOp::register(ctx, LoadOp::parse);
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
