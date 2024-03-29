use std::fmt::Write;

use anyhow::{anyhow, Result};
use num_bigint::BigInt;
use orzir_core::{
    ArenaPtr, Context, Dialect, Op, OpMetadata, OpObj, Parse, ParseState, Print, PrintState,
    TokenKind, TyObj, Value, Verify,
};
use orzir_macros::Op;

use crate::verifiers::*;

fn parse_binary(
    ctx: &mut Context,
    state: &mut ParseState,
) -> Result<(ArenaPtr<Value>, ArenaPtr<Value>, ArenaPtr<TyObj>)> {
    let lhs = Value::parse(ctx, state)?;
    state.stream.expect(TokenKind::Char(','))?;
    let rhs = Value::parse(ctx, state)?;
    state.stream.expect(TokenKind::Char(':'))?;
    let ty = TyObj::parse(ctx, state)?;
    Ok((lhs, rhs, ty))
}

fn print_binary(ctx: &Context, state: &mut PrintState, op_inner: &dyn Op) -> Result<()> {
    op_inner
        .get_operand(0)
        .unwrap()
        .deref(&ctx.values)
        .print(ctx, state)?;
    write!(state.buffer, ", ")?;
    op_inner
        .get_operand(1)
        .unwrap()
        .deref(&ctx.values)
        .print(ctx, state)?;
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
    result: ArenaPtr<Value>,

    value: BigInt,
}

impl Verify for IConstOp {}

impl Parse for IConstOp {
    type Item = ArenaPtr<OpObj>;

    fn parse(ctx: &mut Context, state: &mut ParseState) -> Result<Self::Item> {
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
        let ty = TyObj::parse(ctx, state)?;

        let op = ctx.ops.reserve();

        let mut result_names = state.pop_result_names();

        if result_names.len() != 1 {
            anyhow::bail!("expected 1 result name, got {}", result_names.len());
        }

        let result = Value::new_op_result(ctx, ty, op, 0, result_names.pop())?;

        let op = IConstOp::new(ctx, op, result, value);

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
    result: ArenaPtr<Value>,

    #[operand(0)]
    lhs: ArenaPtr<Value>,

    #[operand(1)]
    rhs: ArenaPtr<Value>,
}

impl Verify for IAddOp {}

impl Parse for IAddOp {
    type Item = ArenaPtr<OpObj>;

    fn parse(ctx: &mut Context, state: &mut ParseState) -> Result<Self::Item> {
        let op = ctx.ops.reserve();
        let (lhs, rhs, ty) = parse_binary(ctx, state)?;
        let mut result_names = state.pop_result_names();
        let result = Value::new_op_result(ctx, ty, op, 0, result_names.pop())?;
        let op = IAddOp::new(ctx, op, result, lhs, rhs);
        Ok(op)
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
        let item = OpObj::parse(&mut ctx, &mut state).unwrap();
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
}
