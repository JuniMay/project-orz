use std::fmt::Write;

use anyhow::{anyhow, Result};
use num_bigint::BigInt;
use orzir_core::{
    ArenaPtr, Context, Dialect, Hold, Op, OpMetadata, OpObj, OpResultBuilder, Parse, ParseState,
    Print, PrintState, TokenKind, TyObj, Value, Verify,
};
use orzir_macros::Op;

use crate::verifiers::*;

fn parse_binary(
    arg: Vec<OpResultBuilder>,
    ctx: &mut Context,
    state: &mut ParseState,
    op: ArenaPtr<OpObj>,
) -> Result<ArenaPtr<OpObj>> {
    let mut result_builders = arg;
    let parent_block = state.curr_block();

    let lhs = Value::parse((), ctx, state)?;
    state.stream.expect(TokenKind::Char(','))?;
    let rhs = Value::parse((), ctx, state)?;
    state.stream.expect(TokenKind::Char(':'))?;
    let ty = TyObj::parse((), ctx, state)?;

    assert!(result_builders.len() == 1);
    let result_builder = result_builders.pop().unwrap();
    // the result will be added to the parent operation when building the result
    let _result = result_builder.op(op).ty(ty).build(ctx)?;

    let op_inner = op.deref_mut(&mut ctx.ops).as_mut();

    op_inner.set_operand(0, lhs)?;
    op_inner.set_operand(1, rhs)?;
    op_inner.set_parent_block(parent_block)?;

    Ok(op)
}

fn print_binary(ctx: &Context, state: &mut PrintState, op_inner: &dyn Op) -> Result<()> {
    op_inner.get_operand(0).unwrap().deref(&ctx.values).print(ctx, state)?;
    write!(state.buffer, ", ")?;
    op_inner.get_operand(1).unwrap().deref(&ctx.values).print(ctx, state)?;
    write!(state.buffer, ": ")?;
    let result_tys = op_inner.result_tys(ctx);
    assert!(result_tys.len() == 1);
    result_tys[0].deref(&ctx.tys).print(ctx, state)?;
    Ok(())
}

#[derive(Op)]
#[mnemonic = "arith.iconst"]
#[verifiers(NumResults<1>, NumOperands<0>, NumRegions<0>, SameResultTys)]
pub struct IConstOp {
    #[metadata]
    metadata: OpMetadata,

    #[result(0)]
    result: Hold<ArenaPtr<Value>>,

    value: BigInt,
}

impl Verify for IConstOp {}

impl Parse for IConstOp {
    type Arg = Vec<OpResultBuilder>;
    type Item = ArenaPtr<OpObj>;

    fn parse(arg: Self::Arg, ctx: &mut Context, state: &mut ParseState) -> Result<Self::Item> {
        let mut result_builders = arg;
        let parent_block = state.curr_block();

        let neg = state.stream.consume_if(TokenKind::Char('-'))?.is_some();
        let token = state.stream.consume()?;
        let value = if let TokenKind::Tokenized(s) = token.kind {
            if s == "true" {
                BigInt::from(1)
            } else if s == "false" {
                BigInt::from(0)
            } else if s.starts_with("0x") {
                BigInt::parse_bytes(&s.as_bytes()[2..], 16)
                    .ok_or_else(|| anyhow!("invalid hex literal"))?
            } else if s.starts_with("0b") {
                BigInt::parse_bytes(&s.as_bytes()[2..], 2)
                    .ok_or_else(|| anyhow!("invalid binary literal"))?
            } else if s.starts_with("0o") {
                BigInt::parse_bytes(&s.as_bytes()[2..], 8)
                    .ok_or_else(|| anyhow!("invalid octal literal"))?
            } else {
                BigInt::parse_bytes(s.as_bytes(), 10)
                    .ok_or_else(|| anyhow!("invalid decimal literal"))?
            }
        } else {
            anyhow::bail!("invalid token: {:?}", token.kind);
        };

        let value = value * if neg { -1 } else { 1 };

        state.stream.expect(TokenKind::Char(':'))?;
        let ty = TyObj::parse((), ctx, state)?;

        let op = IConstOp::new(ctx, value);

        assert!(result_builders.len() == 1);
        let result_builder = result_builders.pop().unwrap();
        let _result = result_builder.op(op).ty(ty).build(ctx)?;

        op.deref_mut(&mut ctx.ops).as_mut().set_parent_block(parent_block)?;

        Ok(op)
    }
}

impl Print for IConstOp {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        write!(state.buffer, " {} : ", self.value)?;
        let result_tys = self.result_tys(ctx);
        assert!(result_tys.len() == 1);
        result_tys[0].deref(&ctx.tys).print(ctx, state)?;
        Ok(())
    }
}

#[derive(Op)]
#[mnemonic = "arith.iadd"]
#[verifiers(
    NumResults<1>, NumOperands<2>, NumRegions<0>,
    SameResultTys, SameOperandTys, SameOperandAndResultTys
)]
pub struct IAddOp {
    #[metadata]
    metadata: OpMetadata,

    #[result(0)]
    result: Hold<ArenaPtr<Value>>,

    #[operand(0)]
    lhs: Hold<ArenaPtr<Value>>,

    #[operand(1)]
    rhs: Hold<ArenaPtr<Value>>,
}

impl Verify for IAddOp {}

impl Parse for IAddOp {
    type Arg = Vec<OpResultBuilder>;
    type Item = ArenaPtr<OpObj>;

    fn parse(arg: Self::Arg, ctx: &mut Context, state: &mut ParseState) -> Result<Self::Item> {
        let op = IAddOp::new(ctx);
        parse_binary(arg, ctx, state, op)
    }
}

impl Print for IAddOp {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        write!(state.buffer, " ")?;
        let op_base = self;
        print_binary(ctx, state, op_base)
    }
}

pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new("arith".into());
    ctx.dialects.insert("arith".into(), dialect);

    IConstOp::register(ctx, IConstOp::parse);
    IAddOp::register(ctx, IAddOp::parse);
}

#[cfg(test)]
mod tests {
    use orzir_core::{Context, Op, OpObj, Parse, ParseState, Print, PrintState, TokenStream};

    use crate::dialects::{
        arith,
        builtin::{self, ModuleOp},
        func,
    };

    fn test_parse_print(src: &str, expected: &str) {
        let stream = TokenStream::new(src);
        let mut state = ParseState::new(stream);
        let mut ctx = Context::default();
        builtin::register(&mut ctx);
        arith::register(&mut ctx);
        let item = OpObj::parse(None, &mut ctx, &mut state).unwrap();
        let mut state = PrintState::new("");
        item.deref(&ctx.ops).print(&ctx, &mut state).unwrap();
        assert_eq!(state.buffer, expected);
    }

    #[test]
    fn test_iconst_op() {
        let src = "%x = arith.iconst 123 : int<32>";
        let expected = "%x = arith.iconst 123 : int<32>";
        test_parse_print(src, expected);
    }

    #[test]
    fn test_0() {
        let src = r#"
        module {
            func.func @foo () -> (int<32>, float) {
            ^entry:
                // nothing here
                %0 = arith.iconst true : int<32>
                %1 = arith.iconst false : int<32>
                %2 = arith.iadd %0, %1 : int<32>

                %aaaa = arith.iconst -0x123 : int<32>

                %b = arith.iconst 0b101 : int<32>
                %c = arith.iconst 0o123 : int<32>
                %d = arith.iconst 123 : int<32>
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
}
