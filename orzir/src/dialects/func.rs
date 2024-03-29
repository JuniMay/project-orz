use std::fmt::Write;

use anyhow::{Ok, Result};
use orzir_core::{
    ArenaPtr, Context, DataFlow, Dialect, Mnemonic, Op, OpMetadata, OpObj, Parse, ParseState,
    Print, PrintState, Region, RegionInterface, RegionKind, RunVerifiers, TokenKind, TyObj, Value,
    Verify,
};
use orzir_macros::{ControlFlow, DataFlow, Op, RegionInterface};

use super::builtin::{FunctionTy, Symbol};
use crate::verifiers::{control_flow::*, *};

#[derive(Op, DataFlow, RegionInterface, ControlFlow)]
#[mnemonic = "func.func"]
// #[interfaces(RegionKindInterface)]
#[verifiers(IsIsolatedFromAbove, NumRegions<1>, NumResults<0>)]
pub struct FuncOp {
    #[metadata]
    metadata: OpMetadata,

    #[region(0)]
    region: ArenaPtr<Region>,

    symbol: Symbol,

    ty: ArenaPtr<TyObj>,
}

// impl RegionKindInterface for FuncOp {}

impl Verify for FuncOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        self.run_verifiers(ctx)?;
        self.ty.deref(&ctx.tys).as_ref().verify(ctx)?;
        self.get_region(0)
            .unwrap()
            .deref(&ctx.regions)
            .verify(ctx)?;
        Ok(())
    }
}

impl Parse for FuncOp {
    type Item = ArenaPtr<OpObj>;

    fn parse(ctx: &mut Context, state: &mut ParseState) -> Result<Self::Item> {
        let op = ctx.ops.reserve();

        state.enter_component_from(op);
        let symbol = Symbol::parse(ctx, state)?;
        state.exit_component();

        // just make the process canonical
        let mnemonic = Mnemonic::new("builtin", "fn");
        let parse_fn = ctx
            .dialects
            .get(mnemonic.primary())
            .unwrap_or_else(|| panic!("dialect {} not found", mnemonic.primary().as_str()))
            .get_ty_parse_fn(&mnemonic)
            .unwrap_or_else(|| {
                panic!(
                    "parse function for {}.{} not found",
                    mnemonic.primary().as_str(),
                    mnemonic.secondary().as_str()
                )
            });

        let ty = parse_fn(ctx, state)?;

        state.enter_region_from(op, RegionKind::SsaCfg, 0);
        let region = Region::parse(ctx, state)?;
        state.exit_region();

        let result_names = state.pop_result_names();
        if !result_names.is_empty() {
            anyhow::bail!("expected 0 result name, got {}", result_names.len());
        }

        let op = FuncOp::new(ctx, op, region, symbol, ty);

        Ok(op)
    }
}

impl Print for FuncOp {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        write!(state.buffer, " ")?;
        self.symbol.print(ctx, state)?;
        let func_ty = self.ty.deref(&ctx.tys).as_a::<FunctionTy>().unwrap();
        func_ty.print(ctx, state)?;
        write!(state.buffer, " ")?;
        self.get_region(0)
            .unwrap()
            .deref(&ctx.regions)
            .print(ctx, state)?;
        Ok(())
    }
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow)]
#[mnemonic = "func.return"]
#[verifiers(NumResults<0>, VariadicOperands, NumRegions<0>, IsTerminator)]
pub struct ReturnOp {
    #[metadata]
    metadata: OpMetadata,

    #[operand(...)]
    operands: Vec<ArenaPtr<Value>>,
}

impl Verify for ReturnOp {}

impl Parse for ReturnOp {
    type Item = ArenaPtr<OpObj>;

    fn parse(ctx: &mut Context, state: &mut ParseState) -> Result<Self::Item> {
        // func.return %1, %2
        // func.return
        let op = ctx.ops.reserve();

        let mut operands = Vec::new();
        while let TokenKind::ValueName(_) = state.stream.peek()?.kind {
            let operand = Value::parse(ctx, state)?;
            operands.push(operand);

            if let TokenKind::Char(',') = state.stream.peek()?.kind {
                state.stream.consume()?;
            } else {
                break;
            }
        }

        let result_names = state.pop_result_names();

        if !result_names.is_empty() {
            anyhow::bail!("expected 0 result name, got {}", result_names.len());
        }

        let op = ReturnOp::new(ctx, op, operands);

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
#[derive(Op, DataFlow, RegionInterface, ControlFlow)]
#[mnemonic = "func.call"]
#[verifiers(VariadicResults, VariadicOperands, NumRegions<0>)]
pub struct CallOp {
    #[metadata]
    metadata: OpMetadata,

    #[result(...)]
    results: Vec<ArenaPtr<Value>>,

    #[operand(...)]
    operands: Vec<ArenaPtr<Value>>,

    callee: String,
    ret_ty: Vec<ArenaPtr<TyObj>>,
}

impl Verify for CallOp {}

impl Parse for CallOp {
    type Item = ArenaPtr<OpObj>;

    fn parse(ctx: &mut Context, state: &mut ParseState) -> Result<Self::Item> {
        let token = state.stream.consume()?;
        let callee = if let TokenKind::SymbolName(s) = token.kind {
            s
        } else {
            anyhow::bail!("expected symbol name");
        };

        state.stream.expect(TokenKind::Char('('))?;

        let mut operands = Vec::new();

        while let TokenKind::ValueName(_) = state.stream.peek()?.kind {
            let operand = Value::parse(ctx, state)?;
            operands.push(operand);

            if let TokenKind::Char(',') = state.stream.peek()?.kind {
                state.stream.consume()?;
            } else {
                break;
            }
        }

        state.stream.expect(TokenKind::Char(')'))?;
        state.stream.expect(TokenKind::Char(':'))?;

        let mut ret_tys = Vec::new();

        // (tys...) or ty
        if let TokenKind::Char('(') = state.stream.peek()?.kind {
            state.stream.consume()?;
            loop {
                let ty = TyObj::parse(ctx, state)?;
                ret_tys.push(ty);

                if let TokenKind::Char(')') = state.stream.peek()?.kind {
                    state.stream.consume()?;
                    break;
                } else {
                    state.stream.expect(TokenKind::Char(','))?;
                }
            }
        } else {
            let ty = TyObj::parse(ctx, state)?;
            ret_tys.push(ty);
        }

        let op = ctx.ops.reserve();

        let mut result_names = state.pop_result_names();
        let mut results = Vec::new();

        if !result_names.len() == ret_tys.len() {
            anyhow::bail!(
                "expected {} result name, got {}",
                ret_tys.len(),
                result_names.len()
            );
        }

        for (i, (result_name, ret_ty)) in result_names.drain(..).zip(ret_tys.iter()).enumerate() {
            let result = Value::new_op_result(ctx, *ret_ty, op, i, Some(result_name))?;
            results.push(result);
        }

        let op = CallOp::new(ctx, op, results, operands, callee, ret_tys);
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

        if self.ret_ty.len() > 1 {
            write!(state.buffer, "(")?;
        }

        for (i, ty) in self.ret_ty.iter().enumerate() {
            ty.deref(&ctx.tys).print(ctx, state)?;
            if i != self.ret_ty.len() - 1 {
                write!(state.buffer, ", ")?;
            }
        }

        if self.ret_ty.len() > 1 {
            write!(state.buffer, ")")?;
        }

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
        Context, OpObj, Parse, ParseState, Print, PrintState, RegionInterface, RegionKind,
        TokenStream,
    };

    use crate::dialects::{
        arith,
        builtin::{self, ModuleOp},
        cf,
        func::{self},
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

        let op = OpObj::parse(&mut ctx, &mut state).unwrap();
        let mut state = PrintState::new("    ");
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

        let op = OpObj::parse(&mut ctx, &mut state).unwrap();
        let mut state = PrintState::new("    ");
        op.deref(&ctx.ops).print(&ctx, &mut state).unwrap();
        println!("{}", state.buffer);

        let module_op = op.deref(&ctx.ops).as_a::<ModuleOp>().unwrap();

        assert!(module_op
            .get_region(0)
            .unwrap()
            .deref(&ctx.regions)
            .lookup_symbol(&ctx, "foo")
            .is_some());

        assert!(module_op
            .get_region(0)
            .unwrap()
            .deref(&ctx.regions)
            .lookup_symbol(&ctx, "bar")
            .is_some());

        assert!(module_op.get_region_kind(&ctx, 0) == RegionKind::Graph);
    }
}
