use std::fmt::Write;

use orzir_core::{
    delimiter, parse_error, token_wildcard, ArenaPtr, Context, Dialect, Op, OpMetadata, Parse,
    ParseErrorKind, ParseResult, ParseState, Print, PrintResult, PrintState, Region,
    RegionInterface, RegionKind, RunVerifiers, TokenKind, Ty, TyObj, VerificationResult, Verify,
};
use orzir_macros::{ControlFlow, DataFlow, Op, Parse, Print, RegionInterface, Ty, Verify};

use crate::verifiers::{control_flow::*, *};

/// A symbol.
///
/// This is currently a simple wrapper around a string, just with implementation
/// of [Parse] and [Print].
#[derive(Debug, Default, Clone)]
pub struct Symbol(String);

impl Parse for Symbol {
    type Item = Self;

    fn parse(ctx: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        let token = state.stream.consume()?;
        if let TokenKind::SymbolName(name) = token.kind {
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
                ParseErrorKind::InvalidToken(vec![token_wildcard!("@...")].into(), token.kind)
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

/// The module operation.
///
/// This is usually the top level operation. And if this is at the top level, it
/// cannot have the symbol field.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print)]
#[mnemonic = "builtin.module"]
#[verifiers(IsIsolatedFromAbove, NumRegions<1>, NumResults<0>, NoTerminator)]
#[format(pattern = "{symbol} {region}", kind = "op", num_results = 0)]
pub struct ModuleOp {
    #[metadata]
    metadata: OpMetadata,
    /// The region of the module.
    #[region(0, kind = RegionKind::Graph)]
    region: ArenaPtr<Region>,
    /// The symbol of the module (optional).
    symbol: Option<Symbol>,
}

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

#[derive(Debug, Hash, PartialEq, Eq, Ty, Parse, Print, Verify)]
#[mnemonic = "builtin.int"]
#[verifiers(IntegerLikeTy)]
#[format(pattern = "< {0} >", kind = "ty")]
pub struct IntTy(usize);

#[derive(Debug, Hash, PartialEq, Eq, Ty, Parse, Print, Verify)]
#[mnemonic = "builtin.index"]
#[verifiers(IntegerLikeTy)]
#[format(pattern = "", kind = "ty")]
pub struct IndexTy;

#[derive(Debug, Hash, PartialEq, Eq, Ty, Parse, Print, Verify)]
#[mnemonic = "builtin.float"]
#[verifiers(FloatLikeTy)]
#[format(pattern = "", kind = "ty")]
pub struct FloatTy;

#[derive(Debug, Hash, PartialEq, Eq, Ty, Parse, Print, Verify)]
#[mnemonic = "builtin.double"]
#[verifiers(FloatLikeTy)]
#[format(pattern = "", kind = "ty")]
pub struct DoubleTy;

#[derive(Debug, Hash, PartialEq, Eq, Ty, Parse, Print, Verify)]
#[mnemonic = "builtin.tuple"]
#[format(pattern = "{elems}", kind = "ty")]
pub struct TupleTy {
    #[repeat(sep = ",", leading = "<", trailing = ">")]
    elems: Vec<ArenaPtr<TyObj>>,
}

#[derive(Debug, Hash, PartialEq, Eq, Ty, Verify)]
#[mnemonic = "builtin.fn"]
pub struct FunctionTy {
    args: Vec<ArenaPtr<TyObj>>,
    rets: Vec<ArenaPtr<TyObj>>,
}

impl Parse for FunctionTy {
    type Item = ArenaPtr<TyObj>;

    fn parse(ctx: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        state.stream.expect(delimiter!('('))?;
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
                            vec![delimiter!(','), delimiter!(')')].into(),
                            token.kind
                        )
                    )
                    .into();
                }
            }
        }

        state.stream.expect(delimiter!("->"))?;

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
                                vec![delimiter!(','), delimiter!(')')].into(),
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

#[derive(Debug, Hash, PartialEq, Eq, Ty, Verify, Parse, Print)]
#[mnemonic = "builtin.memref"]
#[format(pattern = "< {elem} , {shape} >", kind = "ty")]
pub struct MemRefTy {
    #[repeat(sep = "*", leading = "[", trailing = "]")]
    shape: Vec<usize>,
    elem: ArenaPtr<TyObj>,
}

#[derive(Debug, Hash, PartialEq, Eq, Ty, Parse, Print, Verify)]
#[mnemonic = "builtin.unit"]
#[format(pattern = "", kind = "ty")]
pub struct UnitTy;

pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new("builtin".into());
    ctx.dialects.insert("builtin".into(), dialect);

    ModuleOp::register(ctx, ModuleOp::parse);

    UnitTy::register(ctx, UnitTy::parse);
    IntTy::register(ctx, IntTy::parse);
    IndexTy::register(ctx, IndexTy::parse);
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
        test_ty_parse_print(
            "memref<int<32>, [1 * 2 * 3]>",
            "memref<int<32>, [1 * 2 * 3]>",
        );
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
