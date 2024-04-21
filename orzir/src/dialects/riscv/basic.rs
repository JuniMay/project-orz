use std::fmt::Write;

use orzir_core::{
    apint::ApInt, verification_error, ArenaPtr, Context, Dialect, Op, OpMetadata, Parse,
    RunVerifiers, Value, Verify,
};
use orzir_macros::{ControlFlow, DataFlow, Op, Parse, Print, RegionInterface};
use thiserror::Error;

use super::regs::IReg;
use crate::verifiers::*;

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
        if self.imm.width() > 12 {
            return verification_error!(ImmOutOfRangeErr(12, self.imm.width())).into();
        }

        Ok(())
    }
}

pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new("rv".into());
    ctx.dialects.insert("rv".into(), dialect);

    AddiOp::register(ctx, AddiOp::parse);
}
