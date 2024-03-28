use std::fmt::Write;

use anyhow::{Ok, Result};
use orzir_core::{
    ArenaPtr, Context, Dialect, Hold, HoldVec, Op, OpMetadata, OpObj, OpResultBuilder, Parse,
    ParseState, Print, PrintState, Region, RegionKind, TokenKind, TyObj, Value, Verify,
    VerifyInterfaces,
};
use orzir_macros::Op;

use super::builtin::FunctionTy;
use crate::{
    interfaces::*,
    verifiers::{control_flow::*, *},
};

#[derive(Op)]
#[mnemonic = "func.func"]
#[interfaces(RegionKindInterface)]
#[verifiers(IsIsolatedFromAbove, NumRegions<1>, NumResults<0>)]
pub struct FuncOp {
    #[metadata]
    metadata: OpMetadata,

    #[region(0)]
    region: Hold<ArenaPtr<Region>>,

    symbol: String,

    ty: ArenaPtr<TyObj>,
}

impl RegionKindInterface for FuncOp {}

impl Verify for FuncOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        self.verify_interfaces(ctx)?;
        self.ty.deref(&ctx.tys).as_ref().verify(ctx)?;
        self.get_region(0).unwrap().deref(&ctx.regions).verify(ctx)?;
        Ok(())
    }
}

impl Parse for FuncOp {
    type Arg = Vec<OpResultBuilder<false, false, true>>;
    type Item = ArenaPtr<OpObj>;

    fn parse(arg: Self::Arg, ctx: &mut Context, state: &mut ParseState) -> Result<Self::Item> {
        let result_builders = arg;
        let parent_block = state.curr_block();
        assert!(result_builders.is_empty());

        let symbol = if let TokenKind::SymbolName(s) = state.stream.consume()?.kind {
            s
        } else {
            anyhow::bail!("expected symbol name");
        };
        let ty = FunctionTy::parse((), ctx, state)?;
        let op = FuncOp::new(ctx, symbol.clone(), ty);
        op.deref_mut(&mut ctx.ops).as_mut().set_parent_block(parent_block)?;

        // register the symbol in the parent region.
        parent_block
            .expect("FuncOp should be embraced by a region.")
            .deref(&ctx.blocks)
            .parent_region()
            .deref_mut(&mut ctx.regions)
            .register_symbol(symbol, op);

        state.enter_region_from(op, RegionKind::SsaCfg, 0);
        let _region = Region::parse((), ctx, state)?;
        state.exit_region();

        Ok(op)
    }
}

impl Print for FuncOp {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        write!(state.buffer, " @{}", self.symbol)?;
        let func_ty = self.ty.deref(&ctx.tys).as_a::<FunctionTy>().unwrap();
        func_ty.print(ctx, state)?;
        write!(state.buffer, " ")?;
        self.get_region(0).unwrap().deref(&ctx.regions).print(ctx, state)?;
        Ok(())
    }
}

#[derive(Op)]
#[mnemonic = "func.return"]
#[verifiers(NumResults<0>, VariadicOperands, NumRegions<0>, IsTerminator)]
pub struct ReturnOp {
    #[metadata]
    metadata: OpMetadata,

    #[operand(...)]
    operands: HoldVec<ArenaPtr<Value>>,
}

impl Verify for ReturnOp {}

impl Parse for ReturnOp {
    type Arg = Vec<OpResultBuilder<false, false, true>>;
    type Item = ArenaPtr<OpObj>;

    fn parse(arg: Self::Arg, ctx: &mut Context, state: &mut ParseState) -> Result<Self::Item> {
        // func.return %1, %2
        // func.return
        let result_builders = arg;
        let parent_block = state.curr_block();
        assert!(result_builders.is_empty());

        let op = ReturnOp::new(ctx);

        let mut cnt = 0;
        while let TokenKind::ValueName(_) = state.stream.peek()?.kind {
            let operand = Value::parse((), ctx, state)?;

            op.deref_mut(&mut ctx.ops).as_mut().set_operand(cnt, operand)?;
            cnt += 1;

            if let TokenKind::Char(',') = state.stream.peek()?.kind {
                state.stream.consume()?;
            } else {
                break;
            }
        }

        op.deref_mut(&mut ctx.ops).as_mut().set_parent_block(parent_block)?;

        Ok(op)
    }
}

impl Print for ReturnOp {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        let operations = self.operands();
        if !operations.is_empty() {
            write!(state.buffer, " ")?;
            for (i, operand) in operations.iter().enumerate() {
                if i > 0 {
                    write!(state.buffer, ", ")?;
                }
                operand.deref(&ctx.values).print(ctx, state)?;
            }
        }

        Ok(())
    }
}

/// A direct call operation.
///
/// Format (example):
/// ```text
/// %result = func.call @callee(%arg1, %arg2) : int<32>
/// ```
#[derive(Op)]
#[mnemonic = "func.call"]
#[verifiers(VariadicResults, VariadicOperands, NumRegions<0>)]
pub struct CallOp {
    #[metadata]
    metadata: OpMetadata,

    #[result(...)]
    results: HoldVec<ArenaPtr<Value>>,

    #[operand(...)]
    operands: HoldVec<ArenaPtr<Value>>,

    callee: String,
    ret_ty: ArenaPtr<TyObj>,
}

impl Verify for CallOp {}

impl Parse for CallOp {
    type Arg = Vec<OpResultBuilder<false, false, true>>;
    type Item = ArenaPtr<OpObj>;

    fn parse(arg: Self::Arg, ctx: &mut Context, state: &mut ParseState) -> Result<Self::Item> {
        let result_builders = arg;
        let parent_block = state.curr_block();

        let token = state.stream.consume()?;
        let callee = if let TokenKind::SymbolName(s) = token.kind {
            s
        } else {
            anyhow::bail!("expected symbol name");
        };

        state.stream.expect(TokenKind::Char('('))?;

        let mut operands = Vec::new();

        while let TokenKind::ValueName(_) = state.stream.peek()?.kind {
            let operand = Value::parse((), ctx, state)?;
            operands.push(operand);

            if let TokenKind::Char(',') = state.stream.peek()?.kind {
                state.stream.consume()?;
            } else {
                break;
            }
        }

        state.stream.expect(TokenKind::Char(')'))?;
        state.stream.expect(TokenKind::Char(':'))?;
        let ret_ty = TyObj::parse((), ctx, state)?;

        let op = CallOp::new(ctx, callee, ret_ty);

        for (i, operand) in operands.iter().enumerate() {
            op.deref_mut(&mut ctx.ops).as_mut().set_operand(i, *operand)?;
        }

        for result_builder in result_builders {
            // the value will be added to the parent operation when building the result
            let _result = result_builder.op(op).ty(ret_ty).build(ctx)?;
        }

        op.deref_mut(&mut ctx.ops).as_mut().set_parent_block(parent_block)?;

        Ok(op)
    }
}

impl Print for CallOp {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        write!(state.buffer, " @{}", self.callee)?;
        write!(state.buffer, "(")?;
        let operands = self.operands();
        for (i, operand) in operands.iter().enumerate() {
            operand.deref(&ctx.values).print(ctx, state)?;
            if i != operands.len() - 1 {
                write!(state.buffer, ", ")?;
            }
        }
        write!(state.buffer, ") : ")?;
        self.ret_ty.deref(&ctx.tys).print(ctx, state)?;
        Ok(())
    }
}

pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new("func".into());
    ctx.dialects.insert("func".into(), dialect);

    FuncOp::register(ctx, FuncOp::parse);
    ReturnOp::register(ctx, ReturnOp::parse);
    CallOp::register(ctx, CallOp::parse);
}

#[cfg(test)]
mod tests {
    use orzir_core::{
        Context, Op, OpObj, Parse, ParseState, Print, PrintState, RegionKind, TokenStream,
    };

    use crate::dialects::{
        arith,
        builtin::{self, ModuleOp},
        cf,
        func::{self, RegionKindInterface},
    };

    #[test]
    fn test_func_op() {
        let src = r#"
        module {
            func.func @foo () -> (int<32>, float) {
            ^entry:
                %x = arith.iconst 123 : int<32>
                %y = arith.iconst 123 : int<32>
            ^return:
                func.return %x, %y
            ^single:
                func.return %x
            ^null:
                func.return
            }
        }
        "#;

        let stream = TokenStream::new(src);
        let mut state = ParseState::new(stream);
        let mut ctx = Context::default();

        builtin::register(&mut ctx);
        func::register(&mut ctx);
        arith::register(&mut ctx);

        let op = OpObj::parse(None, &mut ctx, &mut state).unwrap();
        let mut state = PrintState::new("    ");
        op.deref(&ctx.ops).print(&ctx, &mut state).unwrap();
        println!("{}", state.buffer);

        let module_op = op.deref(&ctx.ops).as_a::<ModuleOp>().unwrap();

        assert!(module_op
            .get_region(0)
            .unwrap()
            .deref(&ctx.regions)
            .lookup_symbol("foo")
            .is_some());
    }

    #[test]
    fn test_call_op() {
        let src = r#"
        module {
            func.func @bar(int<32>) -> int<32> {
            ^entry(%0 : int<32>):
                func.return %0
            }

            func.func @foo () -> (int<32>, int<32>) {
            ^entry:
                %x = arith.iconst 123 : int<32>
                %y = arith.iconst 123 : int<32>
                %z = func.call @bar(%x) : int<32>
                cf.jump ^return(%x, %y)
            ^return:
                func.return %x, %y
            }
        }
        "#;

        let stream = TokenStream::new(src);
        let mut state = ParseState::new(stream);
        let mut ctx = Context::default();

        builtin::register(&mut ctx);
        func::register(&mut ctx);
        cf::register(&mut ctx);
        arith::register(&mut ctx);

        let op = OpObj::parse(None, &mut ctx, &mut state).unwrap();
        let mut state = PrintState::new("    ");
        op.deref(&ctx.ops).print(&ctx, &mut state).unwrap();
        println!("{}", state.buffer);

        let module_op = op.deref(&ctx.ops).as_a::<ModuleOp>().unwrap();

        assert!(module_op
            .get_region(0)
            .unwrap()
            .deref(&ctx.regions)
            .lookup_symbol("foo")
            .is_some());

        assert!(module_op
            .get_region(0)
            .unwrap()
            .deref(&ctx.regions)
            .lookup_symbol("bar")
            .is_some());

        assert!(module_op.get_region_kind(&ctx, 0) == RegionKind::Graph);
    }
}
