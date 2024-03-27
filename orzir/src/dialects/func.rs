use std::fmt::Write;

use anyhow::{Ok, Result};
use orzir_core::{
    ArenaPtr, Block, Context, Dialect, Op, OpBase, OpObj, OpResultBuilder, Parse, Print,
    PrintState, Region, RegionKind, TokenKind, TokenStream, TyObj, Value, Verify, VerifyInterfaces,
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
    #[base]
    op_base: OpBase,
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
    type Arg = (Vec<OpResultBuilder>, Option<ArenaPtr<Block>>);
    type Item = ArenaPtr<OpObj>;

    fn parse(arg: Self::Arg, ctx: &mut Context, stream: &mut TokenStream) -> Result<Self::Item> {
        let (result_builders, parent_block) = arg;
        assert!(result_builders.is_empty());

        let symbol = if let TokenKind::SymbolName(s) = stream.consume()?.kind {
            s
        } else {
            anyhow::bail!("expected symbol name");
        };
        let ty = FunctionTy::parse((), ctx, stream)?;
        let op = FuncOp::new(ctx, symbol.clone(), ty);

        // parse the region.
        let region_builder = Region::builder().parent_op(op).kind(RegionKind::SsaCfg);
        let _region = Region::parse(region_builder, ctx, stream)?;

        op.deref_mut(&mut ctx.ops).as_mut().set_parent_block(parent_block);
        // register the symbol in the parent region.
        parent_block
            .expect("FuncOp should be embraced by a region.")
            .deref(&ctx.blocks)
            .parent_region()
            .deref_mut(&mut ctx.regions)
            .register_symbol(symbol, op);

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
    #[base]
    op_base: OpBase,
}

impl Verify for ReturnOp {}

impl Parse for ReturnOp {
    type Arg = (Vec<OpResultBuilder>, Option<ArenaPtr<Block>>);
    type Item = ArenaPtr<OpObj>;

    fn parse(arg: Self::Arg, ctx: &mut Context, stream: &mut TokenStream) -> Result<Self::Item> {
        // func.return %1, %2
        // func.return
        let (result_builders, parent_block) = arg;
        assert!(result_builders.is_empty());

        let op = ReturnOp::new(ctx);

        while let TokenKind::ValueName(_) = stream.peek()?.kind {
            let operand = Value::parse((), ctx, stream)?;
            op.deref_mut(&mut ctx.ops).as_mut().add_operand(operand);

            if let TokenKind::Char(',') = stream.peek()?.kind {
                stream.consume()?;
            } else {
                break;
            }
        }

        op.deref_mut(&mut ctx.ops).as_mut().set_parent_block(parent_block);

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
    #[base]
    op_base: OpBase,
    callee: String,
    ret_ty: ArenaPtr<TyObj>,
}

impl Verify for CallOp {}

impl Parse for CallOp {
    type Arg = (Vec<OpResultBuilder>, Option<ArenaPtr<Block>>);
    type Item = ArenaPtr<OpObj>;

    fn parse(arg: Self::Arg, ctx: &mut Context, stream: &mut TokenStream) -> Result<Self::Item> {
        let (result_builders, parent_block) = arg;

        let token = stream.consume()?;
        let callee = if let TokenKind::SymbolName(s) = token.kind {
            s
        } else {
            anyhow::bail!("expected symbol name");
        };

        stream.expect(TokenKind::Char('('))?;

        let mut operands = Vec::new();

        while let TokenKind::ValueName(_) = stream.peek()?.kind {
            let operand = Value::parse((), ctx, stream)?;
            operands.push(operand);

            if let TokenKind::Char(',') = stream.peek()?.kind {
                stream.consume()?;
            } else {
                break;
            }
        }

        stream.expect(TokenKind::Char(')'))?;
        stream.expect(TokenKind::Char(':'))?;
        let ret_ty = TyObj::parse((), ctx, stream)?;

        let op = CallOp::new(ctx, callee, ret_ty);

        for operand in operands {
            op.deref_mut(&mut ctx.ops).as_mut().add_operand(operand);
        }

        for result_builder in result_builders {
            // the value will be added to the parent operation when building the result
            let _result = result_builder.op(op).ty(ret_ty).build(ctx)?;
        }

        op.deref_mut(&mut ctx.ops).as_mut().set_parent_block(parent_block);

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
    use orzir_core::{Context, Op, OpObj, Parse, Print, PrintState, TokenStream};

    use crate::dialects::{
        arith,
        builtin::{self, ModuleOp},
        cf, func,
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

        let mut stream = TokenStream::new(src);
        let mut ctx = Context::default();

        builtin::register(&mut ctx);
        func::register(&mut ctx);
        arith::register(&mut ctx);

        let op = OpObj::parse(None, &mut ctx, &mut stream).unwrap();
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

        let mut stream = TokenStream::new(src);
        let mut ctx = Context::default();

        builtin::register(&mut ctx);
        func::register(&mut ctx);
        cf::register(&mut ctx);
        arith::register(&mut ctx);

        let op = OpObj::parse(None, &mut ctx, &mut stream).unwrap();
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
    }
}
