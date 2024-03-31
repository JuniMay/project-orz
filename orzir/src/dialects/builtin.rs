use std::fmt::Write;

use orzir_core::{
    parse_error, token, ArenaPtr, Context, Dialect, Op, OpMetadata, OpObj, Parse, ParseErrorKind,
    ParseResult, ParseState, Print, PrintResult, PrintState, Region, RegionInterface, RegionKind,
    RunVerifiers, TokenKind, Ty, TyObj, VerificationResult, Verify,
};
use orzir_macros::{ControlFlow, DataFlow, Op, RegionInterface, Ty};
use thiserror::Error;

use crate::verifiers::{control_flow::*, *};

#[derive(Debug, Default, Clone)]
pub struct Symbol(String);

impl Parse for Symbol {
    type Item = Self;

    fn parse(ctx: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        let token = state.stream.consume()?;
        if let TokenKind::SymbolName(name) = token.kind {
            let name = name.unwrap();
            let op = state.curr_op();
            // register the symbol
            let region = state.curr_region();
            region
                .deref_mut(&mut ctx.regions)
                .register_symbol(name.clone(), op);
            // construct and return.
            let symbol = Self(name);
            Ok(symbol)
        } else {
            parse_error!(
                token.span,
                ParseErrorKind::InvalidToken(vec![token!("@...")].into(), token.kind)
            )
            .into()
        }
    }
}

impl Print for Symbol {
    fn print(&self, _: &Context, state: &mut PrintState) -> PrintResult<()> {
        write!(state.buffer, "@{}", self.0)?;
        Ok(())
    }
}

impl From<String> for Symbol {
    fn from(s: String) -> Self {
        if let Some(s) = s.strip_prefix('@') {
            Self(s.to_string())
        } else {
            Self(s)
        }
    }
}

impl From<&str> for Symbol {
    fn from(s: &str) -> Self {
        if let Some(s) = s.strip_prefix('@') {
            Self(s.to_string())
        } else {
            Self(s.to_string())
        }
    }
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow)]
#[mnemonic = "builtin.module"]
// #[interfaces(RegionKindInterface)]
#[verifiers(IsIsolatedFromAbove, NumRegions<1>, NumResults<0>, NoTerminator)]
pub struct ModuleOp {
    #[metadata]
    metadata: OpMetadata,

    #[region(0)]
    region: ArenaPtr<Region>,

    symbol: Option<Symbol>,
}

// impl RegionKindInterface for ModuleOp {}

impl Verify for ModuleOp {
    fn verify(&self, ctx: &Context) -> VerificationResult<()> {
        self.run_verifiers(ctx)?;
        self.get_region(0)
            .unwrap()
            .deref(&ctx.regions)
            .verify(ctx)?;
        Ok(())
    }
}

impl Parse for ModuleOp {
    type Item = ArenaPtr<OpObj>;

    fn parse(ctx: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        let op = ctx.ops.reserve();
        state.enter_component_from(op);
        let _start_pos = state.stream.curr_pos()?;

        let symbol = Option::<Symbol>::parse(ctx, state)?;

        state.enter_region_with(RegionKind::Graph, 0);
        let region = Region::parse(ctx, state)?;
        state.exit_region();

        let _end_pos = state.stream.curr_pos()?;
        state.exit_component();

        let result_names = state.pop_result_names();
        if !result_names.is_empty() {
            let mut span = result_names[0].span;
            for name in result_names.iter().skip(1) {
                span = span.merge(&name.span);
            }

            return parse_error!(
                span,
                ParseErrorKind::InvalidResultNumber(0, result_names.len())
            )
            .into();
        }

        let op = ModuleOp::new(ctx, op, region, symbol);

        Ok(op)
    }
}

impl Print for ModuleOp {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> PrintResult<()> {
        if let Some(symbol) = &self.symbol {
            symbol.print(ctx, state)?;
            write!(state.buffer, " ")?;
        }
        self.get_region(0)
            .unwrap()
            .deref(&ctx.regions)
            .print(ctx, state)?;

        Ok(())
    }
}

#[derive(Debug, Error)]
#[error("invalid size literal")]
struct InvalidSizeLiteral;

#[derive(Debug, Hash, PartialEq, Eq, Ty)]
#[mnemonic = "builtin.int"]
#[verifiers(IntegerLikeTy)]
pub struct IntTy(usize);

impl Verify for IntTy {}

impl Parse for IntTy {
    type Item = ArenaPtr<TyObj>;

    fn parse(ctx: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        state.stream.expect(token!('<'))?;
        let token = state.stream.consume()?;
        let size = if let TokenKind::Tokenized(s) = token.kind {
            s.unwrap()
                .parse::<usize>()
                .map_err(|_| parse_error!(token.span, InvalidSizeLiteral))?
        } else {
            return parse_error!(
                token.span,
                ParseErrorKind::InvalidToken(vec![token!("...")].into(), token.kind)
            )
            .into();
        };
        state.stream.expect(token!('>'))?;
        Ok(IntTy::get(ctx, size))
    }
}

impl Print for IntTy {
    fn print(&self, _: &Context, state: &mut PrintState) -> PrintResult<()> {
        write!(state.buffer, "<{}>", self.0)?;
        Ok(())
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Ty)]
#[mnemonic = "builtin.float"]
#[verifiers(FloatLikeTy)]
pub struct FloatTy;

impl Verify for FloatTy {}

impl Parse for FloatTy {
    type Item = ArenaPtr<TyObj>;

    fn parse(ctx: &mut Context, _: &mut ParseState) -> ParseResult<Self::Item> {
        Ok(FloatTy::get(ctx))
    }
}

impl Print for FloatTy {
    fn print(&self, _: &Context, _: &mut PrintState) -> PrintResult<()> { Ok(()) }
}

#[derive(Debug, Hash, PartialEq, Eq, Ty)]
#[mnemonic = "builtin.double"]
#[verifiers(FloatLikeTy)]
pub struct DoubleTy;

impl Verify for DoubleTy {}

impl Parse for DoubleTy {
    type Item = ArenaPtr<TyObj>;

    fn parse(ctx: &mut Context, _: &mut ParseState) -> ParseResult<Self::Item> {
        Ok(DoubleTy::get(ctx))
    }
}

impl Print for DoubleTy {
    fn print(&self, _: &Context, _: &mut PrintState) -> PrintResult<()> { Ok(()) }
}

#[derive(Debug, Hash, PartialEq, Eq, Ty)]
#[mnemonic = "builtin.tuple"]
pub struct TupleTy {
    elems: Vec<ArenaPtr<TyObj>>,
}

impl Verify for TupleTy {}

impl Parse for TupleTy {
    type Item = ArenaPtr<TyObj>;

    fn parse(ctx: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        state.stream.expect(token!('<'))?;
        let mut elems = Vec::new();
        loop {
            let ty = TyObj::parse(ctx, state)?;
            elems.push(ty);
            let token = state.stream.consume()?;
            match token.kind {
                TokenKind::Char(',') => {}
                TokenKind::Char('>') => break,
                _ => {
                    return parse_error!(
                        token.span,
                        ParseErrorKind::InvalidToken(
                            vec![token!(','), token!('>')].into(),
                            token.kind
                        )
                    )
                    .into();
                }
            }
        }
        Ok(TupleTy::get(ctx, elems))
    }
}

impl Print for TupleTy {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> PrintResult<()> {
        write!(state.buffer, "<")?;
        for (i, ty) in self.elems.iter().enumerate() {
            ty.deref(&ctx.tys).print(ctx, state)?;
            if i != self.elems.len() - 1 {
                write!(state.buffer, ", ")?;
            }
        }
        write!(state.buffer, ">")?;
        Ok(())
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Ty)]
#[mnemonic = "builtin.fn"]
pub struct FunctionTy {
    args: Vec<ArenaPtr<TyObj>>,
    rets: Vec<ArenaPtr<TyObj>>,
}

impl Verify for FunctionTy {}

impl Parse for FunctionTy {
    type Item = ArenaPtr<TyObj>;

    fn parse(ctx: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        state.stream.expect(token!('('))?;
        let mut args = Vec::new();
        loop {
            if state.stream.peek()?.kind == TokenKind::Char(')') {
                state.stream.consume()?;
                break;
            }
            let ty = TyObj::parse(ctx, state)?;
            args.push(ty);
            let token = state.stream.consume()?;
            match token.kind {
                TokenKind::Char(',') => {}
                TokenKind::Char(')') => break,
                _ => {
                    return parse_error!(
                        token.span,
                        ParseErrorKind::InvalidToken(
                            vec![token!(','), token!(')')].into(),
                            token.kind
                        )
                    )
                    .into();
                }
            }
        }

        state.stream.expect(token!("->"))?;

        let mut rets = Vec::new();
        if state.stream.peek()?.kind != TokenKind::Char('(') {
            let ty = TyObj::parse(ctx, state)?;
            rets.push(ty);
        } else {
            state.stream.consume()?;
            loop {
                let ty = TyObj::parse(ctx, state)?;
                rets.push(ty);
                let token = state.stream.consume()?;
                match token.kind {
                    TokenKind::Char(',') => {}
                    TokenKind::Char(')') => break,
                    _ => {
                        return parse_error!(
                            token.span,
                            ParseErrorKind::InvalidToken(
                                vec![token!(','), token!(')')].into(),
                                token.kind
                            )
                        )
                        .into();
                    }
                }
            }
        }

        Ok(FunctionTy::get(ctx, args, rets))
    }
}

impl Print for FunctionTy {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> PrintResult<()> {
        write!(state.buffer, "(")?;
        for (i, ty) in self.args.iter().enumerate() {
            ty.deref(&ctx.tys).print(ctx, state)?;
            if i != self.args.len() - 1 {
                write!(state.buffer, ", ")?;
            }
        }
        write!(state.buffer, ") -> ")?;
        if self.rets.len() > 1 {
            write!(state.buffer, "(")?;
        }
        for (i, ty) in self.rets.iter().enumerate() {
            ty.deref(&ctx.tys).print(ctx, state)?;
            if i != self.rets.len() - 1 {
                write!(state.buffer, ", ")?;
            }
        }
        if self.rets.len() > 1 {
            write!(state.buffer, ")")?;
        }
        Ok(())
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Ty)]
#[mnemonic = "builtin.memref"]
pub struct MemRefTy {
    shape: Vec<usize>,
    elem: ArenaPtr<TyObj>,
}

impl Verify for MemRefTy {}

impl Parse for MemRefTy {
    type Item = ArenaPtr<TyObj>;

    fn parse(ctx: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        state.stream.expect(token!('<'))?;
        let mut shape = Vec::new();
        let mut elem = None;
        loop {
            let token = state.stream.peek()?;
            match &token.kind {
                TokenKind::Tokenized(s) if s.as_ref().unwrap() == "x" => {
                    state.stream.consume()?;
                }
                TokenKind::Tokenized(s) => {
                    let dim = s.as_ref().unwrap().parse::<usize>().ok();
                    if let Some(dim) = dim {
                        state.stream.consume()?;
                        shape.push(dim);
                    } else {
                        elem = Some(TyObj::parse(ctx, state)?);
                    }
                }
                TokenKind::Char('>') => {
                    state.stream.consume()?;
                    break;
                }
                _ => {
                    return parse_error!(
                        token.span,
                        ParseErrorKind::InvalidToken(
                            vec![
                                token!("..."),
                                token!('>'),
                                TokenKind::Tokenized(Some("x".into()))
                            ]
                            .into(),
                            token.kind.clone()
                        )
                    )
                    .into();
                }
            }
        }

        Ok(MemRefTy::get(ctx, shape, elem.unwrap()))
    }
}

impl Print for MemRefTy {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> PrintResult<()> {
        write!(state.buffer, "<")?;
        for dim in self.shape.iter() {
            write!(state.buffer, "{}", dim)?;
            write!(state.buffer, " x ")?;
        }
        self.elem.deref(&ctx.tys).print(ctx, state)?;
        write!(state.buffer, ">")?;
        Ok(())
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Ty)]
#[mnemonic = "builtin.unit"]
pub struct UnitTy;

impl Verify for UnitTy {}

impl Parse for UnitTy {
    type Item = ArenaPtr<TyObj>;

    fn parse(ctx: &mut Context, _: &mut ParseState) -> ParseResult<Self::Item> {
        Ok(UnitTy::get(ctx))
    }
}

impl Print for UnitTy {
    fn print(&self, _: &Context, _: &mut PrintState) -> PrintResult<()> { Ok(()) }
}

pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new("builtin".into());
    ctx.dialects.insert("builtin".into(), dialect);

    ModuleOp::register(ctx, ModuleOp::parse);

    UnitTy::register(ctx, UnitTy::parse);
    IntTy::register(ctx, IntTy::parse);
    FloatTy::register(ctx, FloatTy::parse);
    DoubleTy::register(ctx, DoubleTy::parse);
    TupleTy::register(ctx, TupleTy::parse);
    FunctionTy::register(ctx, FunctionTy::parse);
    MemRefTy::register(ctx, MemRefTy::parse);
}

#[cfg(test)]
mod tests {
    use orzir_core::{Context, OpObj, Parse, ParseState, Print, PrintState, TokenStream, TyObj};

    use crate::dialects::builtin::{self, DoubleTy, FloatTy, FunctionTy, IntTy, MemRefTy, TupleTy};

    #[test]
    fn test_tys_cmp() {
        let mut ctx = Context::default();

        let int0 = IntTy::get(&mut ctx, 32);
        let int1 = IntTy::get(&mut ctx, 64);
        let int2 = IntTy::get(&mut ctx, 32);
        let float0 = FloatTy::get(&mut ctx);
        let float1 = FloatTy::get(&mut ctx);

        let double0 = DoubleTy::get(&mut ctx);
        let double1 = DoubleTy::get(&mut ctx);

        assert_ne!(int0, float0);
        assert_ne!(int0, int1);
        assert_eq!(int0, int2);
        assert_eq!(float0, float1);
        assert_ne!(float0, double0);
        assert_eq!(double0, double1);

        let tuple0 = TupleTy::get(&mut ctx, vec![int0, float0]);
        let tuple1 = TupleTy::get(&mut ctx, vec![int0, float0]);
        let tuple2 = TupleTy::get(&mut ctx, vec![int0, float0, double0]);

        assert_eq!(tuple0, tuple1);
        assert_ne!(tuple0, tuple2);

        let fn0 = FunctionTy::get(&mut ctx, vec![int0, float0], vec![double0]);
        let fn1 = FunctionTy::get(&mut ctx, vec![int0, float0], vec![double0]);
        let fn2 = FunctionTy::get(&mut ctx, vec![int0, float0], vec![double0, int0]);

        assert_eq!(fn0, fn1);
        assert_ne!(fn0, fn2);

        let memref0 = MemRefTy::get(&mut ctx, vec![1, 2, 3], int0);
        let memref1 = MemRefTy::get(&mut ctx, vec![1, 2, 3], int0);
        let memref2 = MemRefTy::get(&mut ctx, vec![1, 2, 3], int1);
        let memref3 = MemRefTy::get(&mut ctx, vec![6, 6, 6], int1);

        assert_eq!(memref0, memref1);
        assert_ne!(memref0, memref2);
        assert_ne!(memref0, memref3);
    }

    fn test_ty_parse_print(ty: &str, expected: &str) {
        let stream = TokenStream::new(ty);
        let mut state = ParseState::new(stream);
        let mut ctx = Context::default();
        builtin::register(&mut ctx);
        let ty = TyObj::parse(&mut ctx, &mut state).unwrap();

        let mut state = PrintState::new("");
        ty.deref(&ctx.tys).print(&ctx, &mut state).unwrap();
        assert_eq!(state.buffer, expected);
    }

    #[test]
    fn test_int_parse() { test_ty_parse_print("int<32>", "int<32>"); }

    #[test]
    fn test_float_parse() { test_ty_parse_print("float", "float"); }

    #[test]
    fn test_double_parse() { test_ty_parse_print("double", "double"); }

    #[test]
    fn test_tuple_parse() { test_ty_parse_print("tuple<int<32>, float>", "tuple<int<32>, float>"); }

    #[test]
    fn test_func_parse_0() {
        test_ty_parse_print(
            "fn(int<32>, float) -> double",
            "fn(int<32>, float) -> double",
        );
    }

    #[test]
    fn test_func_parse_1() {
        test_ty_parse_print(
            "fn(int<32>, float) -> tuple<int<32>, float>",
            "fn(int<32>, float) -> tuple<int<32>, float>",
        );
    }

    #[test]
    fn test_func_parse_2() {
        test_ty_parse_print(
            "fn(int<32>, float) -> (int<32>, float)",
            "fn(int<32>, float) -> (int<32>, float)",
        );
    }

    #[test]
    fn test_memref_parse() {
        test_ty_parse_print("memref<1 x 2 x 3 x int<32>>", "memref<1 x 2 x 3 x int<32>>");
    }

    #[test]
    fn test_module_op() {
        let src = r#"
            module {
                module @named_module {

                }
            }
        "#;

        let stream = TokenStream::new(src);
        let mut state = ParseState::new(stream);
        let mut ctx = Context::default();

        builtin::register(&mut ctx);

        let op = OpObj::parse(&mut ctx, &mut state).unwrap();

        let mut state = PrintState::new("    ");
        op.deref(&ctx.ops).print(&ctx, &mut state).unwrap();
        println!("{}", state.buffer);
    }
}
