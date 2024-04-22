use std::fmt::{self, Write};

use orzir_core::{parse_error, token_wildcard, ParseErrorKind, Print, PrintResult, PrintState, TokenKind, Ty};
use orzir_core::{
    apint::ApInt, verification_error, ArenaPtr, Context, Dialect, Op, OpMetadata, Parse,
    RunVerifiers, Value, Verify, Successor, ParseState, ParseResult
};
use orzir_macros::{ControlFlow, DataFlow, Op, Parse, Print, RegionInterface, Verify};
use thiserror::Error;

use super::regs::IReg;
use crate::verifiers::*;
use crate::verifiers::control_flow::*;

#[derive(Debug, Error)]
#[error("expected an immediate with width at most {0}, but got {1}")]
pub struct ImmOutOfRangeErr(pub usize, pub usize);

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print)]
#[mnemonic = "rv.addi"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands,
    OperandTysAre<IReg>, ResultTysAre<IReg>
)]
#[format(pattern = "{lhs} , {imm}", kind = "op", num_results = 1)]
pub struct AddiOp {
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

impl Verify for AddiOp {
    fn verify(&self, ctx: &Context) -> orzir_core::VerificationResult<()> {
        self.run_verifiers(ctx)?;

        // verify the width of the immediate
        if self.imm.width() != 12 {
            return verification_error!(ImmOutOfRangeErr(12, self.imm.width())).into();
        }

        Ok(())
    }
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print)]
#[mnemonic = "rv.addiw"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands,
    OperandTysAre<IReg>, ResultTysAre<IReg>
)]
#[format(pattern = "{lhs} , {imm}", kind = "op", num_results = 1)]
pub struct AddiwOp {
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

impl Verify for AddiwOp {
    fn verify(&self, ctx: &Context) -> orzir_core::VerificationResult<()> {
        self.run_verifiers(ctx)?;

        // verify the width of the immediate
        if self.imm.width() != 12 {
            return verification_error!(ImmOutOfRangeErr(12, self.imm.width())).into();
        }

        Ok(())
    }
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print)]
#[mnemonic = "rv.slli"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands,
    OperandTysAre<IReg>, ResultTysAre<IReg>
)]
#[format(pattern = "{lhs} , {imm}", kind = "op", num_results = 1)]
pub struct SlliOp {
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

impl Verify for SlliOp {
    fn verify(&self, ctx: &Context) -> orzir_core::VerificationResult<()> {
        self.run_verifiers(ctx)?;

        // verify the width of the immediate
        if self.imm.width() > 12 {
            return verification_error!(ImmOutOfRangeErr(7, self.imm.width())).into();
        }

        Ok(())
    }
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print)]
#[mnemonic = "rv.slliw"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands,
    OperandTysAre<IReg>, ResultTysAre<IReg>
)]
#[format(pattern = "{lhs} , {imm}", kind = "op", num_results = 1)]
pub struct SlliwOp {
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

impl Verify for SlliwOp {
    fn verify(&self, ctx: &Context) -> orzir_core::VerificationResult<()> {
        self.run_verifiers(ctx)?;

        // verify the width of the immediate
        if self.imm.width() != 5 {
            return verification_error!(ImmOutOfRangeErr(5, self.imm.width())).into();
        }

        Ok(())
    }
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print)]
#[mnemonic = "rv.srli"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands,
    OperandTysAre<IReg>, ResultTysAre<IReg>
)]
#[format(pattern = "{lhs} , {imm}", kind = "op", num_results = 1)]
pub struct SrliOp {
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

impl Verify for SrliOp {
    fn verify(&self, ctx: &Context) -> orzir_core::VerificationResult<()> {
        self.run_verifiers(ctx)?;

        // verify the width of the immediate
        if self.imm.width() > 7 {
            return verification_error!(ImmOutOfRangeErr(7, self.imm.width())).into();
        }

        Ok(())
    }
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print)]
#[mnemonic = "rv.srliw"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands,
    OperandTysAre<IReg>, ResultTysAre<IReg>
)]
#[format(pattern = "{lhs} , {imm}", kind = "op", num_results = 1)]
pub struct SrliwOp {
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

impl Verify for SrliwOp {
    fn verify(&self, ctx: &Context) -> orzir_core::VerificationResult<()> {
        self.run_verifiers(ctx)?;

        // verify the width of the immediate
        if self.imm.width() != 5 {
            return verification_error!(ImmOutOfRangeErr(5, self.imm.width())).into();
        }

        Ok(())
    }
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print)]
#[mnemonic = "rv.srai"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands,
    OperandTysAre<IReg>, ResultTysAre<IReg>
)]
#[format(pattern = "{lhs} , {imm}", kind = "op", num_results = 1)]
pub struct SraiOp {
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

impl Verify for SraiOp {
    fn verify(&self, ctx: &Context) -> orzir_core::VerificationResult<()> {
        self.run_verifiers(ctx)?;

        // verify the width of the immediate
        if self.imm.width() > 7 {
            return verification_error!(ImmOutOfRangeErr(7, self.imm.width())).into();
        }

        Ok(())
    }
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print)]
#[mnemonic = "rv.sraiw"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands,
    OperandTysAre<IReg>, ResultTysAre<IReg>
)]
#[format(pattern = "{lhs} , {imm}", kind = "op", num_results = 1)]
pub struct SraiwOp {
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

impl Verify for SraiwOp {
    fn verify(&self, ctx: &Context) -> orzir_core::VerificationResult<()> {
        self.run_verifiers(ctx)?;

        // verify the width of the immediate
        if self.imm.width() != 5 {
            return verification_error!(ImmOutOfRangeErr(5, self.imm.width())).into();
        }

        Ok(())
    }
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print)]
#[mnemonic = "rv.xori"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands,
    OperandTysAre<IReg>, ResultTysAre<IReg>
)]
#[format(pattern = "{lhs} , {imm}", kind = "op", num_results = 1)]
pub struct XoriOp {
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

impl Verify for XoriOp {
    fn verify(&self, ctx: &Context) -> orzir_core::VerificationResult<()> {
        self.run_verifiers(ctx)?;

        // verify the width of the immediate
        if self.imm.width() != 12 {
            return verification_error!(ImmOutOfRangeErr(12, self.imm.width())).into();
        }

        Ok(())
    }
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print)]
#[mnemonic = "rv.ori"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands,
    OperandTysAre<IReg>, ResultTysAre<IReg>
)]
#[format(pattern = "{lhs} , {imm}", kind = "op", num_results = 1)]
pub struct OriOp {
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

impl Verify for OriOp {
    fn verify(&self, ctx: &Context) -> orzir_core::VerificationResult<()> {
        self.run_verifiers(ctx)?;

        // verify the width of the immediate
        if self.imm.width() != 12 {
            return verification_error!(ImmOutOfRangeErr(12, self.imm.width())).into();
        }

        Ok(())
    }
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print)]
#[mnemonic = "rv.andi"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands,
    OperandTysAre<IReg>, ResultTysAre<IReg>
)]
#[format(pattern = "{lhs} , {imm}", kind = "op", num_results = 1)]
pub struct AndiOp {
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

impl Verify for AndiOp {
    fn verify(&self, ctx: &Context) -> orzir_core::VerificationResult<()> {
        self.run_verifiers(ctx)?;

        // verify the width of the immediate
        if self.imm.width() != 12 {
            return verification_error!(ImmOutOfRangeErr(12, self.imm.width())).into();
        }

        Ok(())
    }
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print)]
#[mnemonic = "rv.slti"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands,
    OperandTysAre<IReg>, ResultTysAre<IReg>
)]
#[format(pattern = "{lhs} , {imm}", kind = "op", num_results = 1)]
pub struct SltiOp {
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

impl Verify for SltiOp {
    fn verify(&self, ctx: &Context) -> orzir_core::VerificationResult<()> {
        self.run_verifiers(ctx)?;

        // verify the width of the immediate
        if self.imm.width() != 12 {
            return verification_error!(ImmOutOfRangeErr(12, self.imm.width())).into();
        }

        Ok(())
    }
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print)]
#[mnemonic = "rv.sltiu"]
#[verifiers(
    NumResults<1>, NumOperands<1>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys,
    IntegerLikeOperands,
    OperandTysAre<IReg>, ResultTysAre<IReg>
)]
#[format(pattern = "{lhs} , {imm}", kind = "op", num_results = 1)]
pub struct SltiuOp {
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

impl Verify for SltiuOp {
    fn verify(&self, ctx: &Context) -> orzir_core::VerificationResult<()> {
        self.run_verifiers(ctx)?;

        // verify the width of the immediate
        if self.imm.width() != 12 {
            return verification_error!(ImmOutOfRangeErr(12, self.imm.width())).into();
        }

        Ok(())
    }
}



#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "rv.jmp"]
#[verifiers(
    NumResults<0>, NumOperands<0>, NumRegions<0>, NumSuccessors<1>, IsTerminator
)]
#[format(pattern = "{succ}", kind = "op", num_results = 0)]
pub struct JmpOp {
    #[metadata]
    metadata: OpMetadata,
    #[successor(0)]
    succ: Successor,
}

// TODO: Verifier for JmpOp

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
            let pred = LoadPredicate::try_from(s.as_str()).map_err(|e| parse_error!(token.span, e))?;
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
    pred: LoadPredicate,
    #[result(0)]
    result: ArenaPtr<Value>,
    #[operand(0)]
    base: ArenaPtr<Value>,
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
            let pred = BranchPredicate::try_from(s.as_str()).map_err(|e| parse_error!(token.span, e))?;
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
#[format(pattern = "{pred} , {lhs} , {rhs} , {then_succ} , {else_succ}", kind = "op", num_results = 0)]
pub struct BranchOp {
    #[metadata]
    metadata: OpMetadata,
    pred: BranchPredicate,
    #[operand(0)]
    lhs: ArenaPtr<Value>,
    #[operand(1)]
    rhs: ArenaPtr<Value>,
    #[successor(0)]
    then_succ: Successor,
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

macro_rules! rv_binary {
    ($mnemonic:literal, $name:ident) => {
        #[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
        #[mnemonic = $mnemonic]
        #[verifiers(
            NumResults<1>, NumOperands<2>, NumRegions<0>,
            SameResultTys, SameOperandTys, SameOperandAndResultTys,
            IntegerLikeOperands,
            OperandTysAre<IReg>, ResultTysAre<IReg>
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
    use orzir_core::{
        Context, OpObj, Parse, ParseState, Print, PrintState, TokenStream
    };

    use crate::dialects::{riscv::basic, std::register_std_dialects};

    fn test_parse_print(src: &str, expected: &str) {
        let stream = TokenStream::new(src);
        let mut state = ParseState::new(stream);
        let mut ctx = Context::default();
        basic::register(&mut ctx);
        let item = OpObj::parse(&mut ctx, &mut state).unwrap();
        let mut state = PrintState::new("");
        item.deref(&ctx.ops).as_ref().verify(&ctx).unwrap();
        item.deref(&ctx.ops).print(&ctx, &mut state).unwrap();
        assert_eq!(state.buffer, expected);
    }

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