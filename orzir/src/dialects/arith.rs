use std::fmt::Write;

use num_bigint::BigInt;
use orzir_core::{
    parse_error, token, ArenaPtr, Context, DataFlow, Dialect, Op, OpMetadata, OpObj, Parse,
    ParseErrorKind, ParseResult, ParseState, Print, PrintResult, PrintState, Span, TokenKind,
    TyObj, Value, Verify,
};
use orzir_macros::{ControlFlow, DataFlow, Op, RegionInterface};
use thiserror::Error;

use crate::verifiers::*;

fn parse_binary(
    ctx: &mut Context,
    state: &mut ParseState,
) -> ParseResult<(ArenaPtr<Value>, ArenaPtr<Value>, ArenaPtr<TyObj>)> {
    let lhs = Value::parse(ctx, state)?;
    state.stream.expect(token!(','))?;
    let rhs = Value::parse(ctx, state)?;
    state.stream.expect(token!(':'))?;
    let ty = TyObj::parse(ctx, state)?;
    Ok((lhs, rhs, ty))
}

fn print_binary(ctx: &Context, state: &mut PrintState, op_inner: &dyn Op) -> PrintResult<()> {
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

#[derive(Op, DataFlow, RegionInterface, ControlFlow)]
#[mnemonic = "arith.iconst"]
#[verifiers(NumResults<1>, NumOperands<0>, NumRegions<0>, SameResultTys)]
pub struct IConstOp {
    #[metadata]
    metadata: OpMetadata,

    #[result(0)]
    result: ArenaPtr<Value>,

    value: IntLiteral,
}

impl Verify for IConstOp {}

pub struct IntLiteral(pub BigInt);

#[derive(Debug, Error)]
#[error("invalid int literal: {0}")]
struct InvalidIntLiteral(String);

impl Parse for IntLiteral {
    type Item = IntLiteral;

    fn parse(_: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        let neg_token = state.stream.consume_if(TokenKind::Char('-'))?;
        let neg = neg_token.is_some();

        let token = state.stream.consume()?;

        let value = if let TokenKind::Tokenized(s) = token.kind {
            let s = s.unwrap();
            if s == "true" {
                BigInt::from(1)
            } else if s == "false" {
                BigInt::from(0)
            } else if s.starts_with("0x") {
                BigInt::parse_bytes(&s.as_bytes()[2..], 16)
                    .ok_or_else(|| parse_error!(token.span, InvalidIntLiteral(s)))?
            } else if s.starts_with("0b") {
                BigInt::parse_bytes(&s.as_bytes()[2..], 2)
                    .ok_or_else(|| parse_error!(token.span, InvalidIntLiteral(s)))?
            } else if s.starts_with("0o") {
                BigInt::parse_bytes(&s.as_bytes()[2..], 8)
                    .ok_or_else(|| parse_error!(token.span, InvalidIntLiteral(s)))?
            } else {
                BigInt::parse_bytes(s.as_bytes(), 10)
                    .ok_or_else(|| parse_error!(token.span, InvalidIntLiteral(s)))?
            }
        } else {
            return parse_error!(
                token.span,
                ParseErrorKind::InvalidToken(vec![token!("...")].into(), token.kind)
            )
            .into();
        };

        Ok(IntLiteral(if neg { -value } else { value }))
    }
}

impl Print for IntLiteral {
    fn print(&self, _: &Context, state: &mut PrintState) -> PrintResult<()> {
        write!(state.buffer, "{}", self.0)?;
        Ok(())
    }
}

impl Parse for IConstOp {
    type Item = ArenaPtr<OpObj>;

    fn parse(ctx: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        let pos = state.stream.peek()?.span.start;

        let value = IntLiteral::parse(ctx, state)?;
        state.stream.expect(token!(':'))?;
        let ty = TyObj::parse(ctx, state)?;
        let op = ctx.ops.reserve();
        let mut result_names = state.pop_result_names();
        if result_names.len() != 1 {
            if result_names.is_empty() {
                return parse_error!(
                    Span::new(pos, pos),
                    ParseErrorKind::InvalidResultNumber(1, 0)
                )
                .into();
            }

            let mut span = result_names[0].span;
            for name in result_names.iter().skip(1) {
                span = span.merge(&name.span);
            }

            return parse_error!(
                span,
                ParseErrorKind::InvalidResultNumber(1, result_names.len())
            )
            .into();
        }
        let result_name = result_names.pop().unwrap().unwrap_value_name();
        let result = Value::new_op_result(ctx, ty, op, 0, Some(result_name));
        let op = IConstOp::new(ctx, op, result, value);

        Ok(op)
    }
}

impl Print for IConstOp {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> PrintResult<()> {
        write!(state.buffer, " ")?;
        self.value.print(ctx, state)?;
        write!(state.buffer, " : ")?;
        let result_tys = self.result_tys(ctx);
        assert!(result_tys.len() == 1);
        result_tys[0].deref(&ctx.tys).print(ctx, state)?;
        Ok(())
    }
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow)]
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

    fn parse(ctx: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        let op = ctx.ops.reserve();
        let (lhs, rhs, ty) = parse_binary(ctx, state)?;
        let mut result_names = state.pop_result_names();
        let result_name = result_names.pop().unwrap().unwrap_value_name();
        let result = Value::new_op_result(ctx, ty, op, 0, Some(result_name));
        let op = IAddOp::new(ctx, op, result, lhs, rhs);
        Ok(op)
    }
}

impl Print for IAddOp {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> PrintResult<()> {
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
    use orzir_core::{
        Context, OpObj, Parse, ParseState, Print, PrintState, RegionInterface, TokenStream,
    };

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
