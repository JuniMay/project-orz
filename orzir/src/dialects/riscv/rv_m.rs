use std::fmt::Write;

use orzir_core::{ArenaPtr, Context, Dialect, Op, OpMetadata, Parse, Value};
use orzir_macros::{ControlFlow, DataFlow, Op, Parse, Print, RegionInterface, Verify};

use super::regs::IReg;
use crate::verifiers::*;

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

rv_binary!("rv_m.mul", MulOp);
rv_binary!("rv_m.mulw", MulwOp);
rv_binary!("rv_m.mulh", MulhOp);
rv_binary!("rv_m.mulhsu", MulhsuOp);
rv_binary!("rv_m.mulhu", MulhuOp);
rv_binary!("rv_m.div", DivOp);
rv_binary!("rv_m.divu", DivuOp);
rv_binary!("rv_m.divw", DivwOp);
rv_binary!("rv_m.divuw", DivuwOp);
rv_binary!("rv_m.rem", RemOp);
rv_binary!("rv_m.remu", RemuOp);
rv_binary!("rv_m.remw", RemwOp);
rv_binary!("rv_m.remuw", RemuwOp);

pub fn register(ctx: &mut Context) {
    ctx.dialects
        .insert("rv_m".into(), Dialect::new("rv_m".into()));

    MulOp::register(ctx, MulOp::parse);
    MulwOp::register(ctx, MulwOp::parse);
    MulhOp::register(ctx, MulhOp::parse);
    MulhsuOp::register(ctx, MulhsuOp::parse);
    MulhuOp::register(ctx, MulhuOp::parse);
    DivOp::register(ctx, DivOp::parse);
    DivuOp::register(ctx, DivuOp::parse);
    DivwOp::register(ctx, DivwOp::parse);
    DivuwOp::register(ctx, DivuwOp::parse);
    RemOp::register(ctx, RemOp::parse);
    RemuOp::register(ctx, RemuOp::parse);
    RemwOp::register(ctx, RemwOp::parse);
    RemuwOp::register(ctx, RemuwOp::parse);
}
