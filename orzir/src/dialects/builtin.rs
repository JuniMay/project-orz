use std::fmt::Write;

use anyhow::Result;
use orzir_core::{
    ArenaPtr, Block, Context, Dialect, Op, OpBase, OpObj, OpResultBuilder, Parse, Print,
    PrintState, Region, RegionKind, TokenKind, TokenStream, Type, TypeObj, Verify,
    VerifyInterfaces,
};
use orzir_macros::{Op, Type};

use crate::interfaces::{control_flow::*, *};

#[derive(Op)]
#[mnemonic = "builtin.module"]
#[verifiers(IsIsolatedFromAbove, NumRegions<1>, NumResults<0>, NoTerminator)]
pub struct ModuleOp {
    #[base]
    op_base: OpBase,
    symbol: Option<String>,
}

impl Verify for ModuleOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        self.verify_interfaces(ctx)?;
        self.as_base().get_region(0).unwrap().deref(&ctx.regions).verify(ctx)?;
        Ok(())
    }
}

impl Parse for ModuleOp {
    type Arg = (Vec<OpResultBuilder>, Option<ArenaPtr<Block>>);
    type Item = ArenaPtr<OpObj>;

    fn parse(arg: Self::Arg, ctx: &mut Context, stream: &mut TokenStream) -> Result<Self::Item> {
        let (result_builders, parent_block) = arg;

        if !result_builders.is_empty() {
            anyhow::bail!("ModuleOp does not have any results");
        }

        let token = stream.peek()?;
        let symbol = if let TokenKind::ValueName(symbol) = &token.kind {
            let symbol = symbol.clone();
            stream.consume()?;
            Some(symbol)
        } else {
            None
        };

        let op = ModuleOp::new(ctx, symbol);
        op.deref_mut(&mut ctx.ops)
            .as_inner_mut()
            .as_base_mut()
            .set_parent_block(parent_block);

        let region_builder = Region::builder().parent_op(op).kind(RegionKind::Graph);
        // the region will be added in the parser.
        let _region = Region::parse(region_builder, ctx, stream)?;

        Ok(op)
    }
}

impl Print for ModuleOp {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        if let Some(symbol) = &self.symbol {
            write!(state.buffer, "@{}", symbol)?;
        }
        write!(state.buffer, " ")?;
        self.as_base().get_region(0).unwrap().deref(&ctx.regions).print(ctx, state)?;

        Ok(())
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Type)]
#[mnemonic = "builtin.int"]
#[verifiers(IntegerLikeType)]
pub struct IntType(usize);

impl Verify for IntType {}

impl Parse for IntType {
    type Arg = ();
    type Item = ArenaPtr<TypeObj>;

    fn parse(_: (), ctx: &mut Context, stream: &mut TokenStream) -> Result<Self::Item> {
        stream.expect(TokenKind::Char('<'))?;
        let token = stream.consume()?;
        let size = if let TokenKind::Tokenized(s) = token.kind {
            s.parse::<usize>()?
        } else {
            anyhow::bail!("expect a number")
        };
        stream.expect(TokenKind::Char('>'))?;
        Ok(IntType::get(ctx, size))
    }
}

impl Print for IntType {
    fn print(&self, _ct_sx: &Context, state: &mut PrintState) -> Result<()> {
        write!(state.buffer, "<{}>", self.0)?;
        Ok(())
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Type)]
#[mnemonic = "builtin.float"]
#[verifiers(FloatLikeType)]
pub struct FloatType;

impl Verify for FloatType {}

impl Parse for FloatType {
    type Arg = ();
    type Item = ArenaPtr<TypeObj>;

    fn parse(_: (), ctx: &mut Context, _: &mut TokenStream) -> Result<Self::Item> {
        Ok(FloatType::get(ctx))
    }
}

impl Print for FloatType {
    fn print(&self, _: &Context, _: &mut PrintState) -> Result<()> { Ok(()) }
}

#[derive(Debug, Hash, PartialEq, Eq, Type)]
#[mnemonic = "builtin.double"]
#[verifiers(FloatLikeType)]
pub struct DoubleType;

impl Verify for DoubleType {}

impl Parse for DoubleType {
    type Arg = ();
    type Item = ArenaPtr<TypeObj>;

    fn parse(_: (), ctx: &mut Context, _: &mut TokenStream) -> Result<Self::Item> {
        Ok(DoubleType::get(ctx))
    }
}

impl Print for DoubleType {
    fn print(&self, _: &Context, _: &mut PrintState) -> Result<()> { Ok(()) }
}

#[derive(Debug, Hash, PartialEq, Eq, Type)]
#[mnemonic = "builtin.tuple"]
pub struct TupleType {
    elems: Vec<ArenaPtr<TypeObj>>,
}

impl Verify for TupleType {}

impl Parse for TupleType {
    type Arg = ();
    type Item = ArenaPtr<TypeObj>;

    fn parse(_: (), ctx: &mut Context, stream: &mut TokenStream) -> Result<Self::Item> {
        stream.expect(TokenKind::Char('<'))?;
        let mut elems = Vec::new();
        loop {
            let ty = TypeObj::parse((), ctx, stream)?;
            elems.push(ty);
            let token = stream.consume()?;
            match token.kind {
                TokenKind::Char(',') => {}
                TokenKind::Char('>') => break,
                _ => anyhow::bail!("expect ',' or '>', got {:?}", token.kind),
            }
        }
        Ok(TupleType::get(ctx, elems))
    }
}

impl Print for TupleType {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        write!(state.buffer, "<")?;
        for (i, ty) in self.elems.iter().enumerate() {
            ty.deref(&ctx.types).print(ctx, state)?;
            if i != self.elems.len() - 1 {
                write!(state.buffer, ", ")?;
            }
        }
        write!(state.buffer, ">")?;
        Ok(())
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Type)]
#[mnemonic = "builtin.fn"]
pub struct FunctionType {
    args: Vec<ArenaPtr<TypeObj>>,
    rets: Vec<ArenaPtr<TypeObj>>,
}

impl Verify for FunctionType {}

impl Parse for FunctionType {
    type Arg = ();
    type Item = ArenaPtr<TypeObj>;

    fn parse(_: (), ctx: &mut Context, stream: &mut TokenStream) -> Result<Self::Item> {
        stream.expect(TokenKind::Char('('))?;
        let mut args = Vec::new();
        loop {
            if stream.peek()?.kind == TokenKind::Char(')') {
                stream.consume()?;
                break;
            }
            let ty = TypeObj::parse((), ctx, stream)?;
            args.push(ty);
            let token = stream.consume()?;
            match token.kind {
                TokenKind::Char(',') => {}
                TokenKind::Char(')') => break,
                _ => anyhow::bail!("expect ',' or ')', got {:?}", token.kind),
            }
        }

        stream.expect(TokenKind::Arrow)?;

        let mut rets = Vec::new();
        if stream.peek()?.kind != TokenKind::Char('(') {
            let ty = TypeObj::parse((), ctx, stream)?;
            rets.push(ty);
        } else {
            stream.consume()?;
            loop {
                let ty = TypeObj::parse((), ctx, stream)?;
                rets.push(ty);
                let token = stream.consume()?;
                match token.kind {
                    TokenKind::Char(',') => {}
                    TokenKind::Char(')') => break,
                    _ => anyhow::bail!("expect ',' or ')', got {:?}", token.kind),
                }
            }
        }

        Ok(FunctionType::get(ctx, args, rets))
    }
}

impl Print for FunctionType {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        write!(state.buffer, "(")?;
        for (i, ty) in self.args.iter().enumerate() {
            ty.deref(&ctx.types).print(ctx, state)?;
            if i != self.args.len() - 1 {
                write!(state.buffer, ", ")?;
            }
        }
        write!(state.buffer, ") -> ")?;
        if self.rets.len() > 1 {
            write!(state.buffer, "(")?;
        }
        for (i, ty) in self.rets.iter().enumerate() {
            ty.deref(&ctx.types).print(ctx, state)?;
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

#[derive(Debug, Hash, PartialEq, Eq, Type)]
#[mnemonic = "builtin.memref"]
pub struct MemRefType {
    shape: Vec<usize>,
    elem: ArenaPtr<TypeObj>,
}

impl Verify for MemRefType {}

impl Parse for MemRefType {
    type Arg = ();
    type Item = ArenaPtr<TypeObj>;

    fn parse(_: (), ctx: &mut Context, stream: &mut TokenStream) -> Result<Self::Item> {
        stream.expect(TokenKind::Char('<'))?;
        let mut shape = Vec::new();
        let mut elem = None;
        loop {
            let token = stream.peek()?;
            match &token.kind {
                TokenKind::Tokenized(s) if s == "x" => {
                    stream.consume()?;
                }
                TokenKind::Tokenized(s) => {
                    let dim = s.parse::<usize>().ok();
                    if let Some(dim) = dim {
                        stream.consume()?;
                        shape.push(dim);
                    } else {
                        elem = Some(TypeObj::parse((), ctx, stream)?);
                    }
                }
                TokenKind::Char('>') => {
                    stream.consume()?;
                    break;
                }
                _ => anyhow::bail!("expect a number or 'x', got {:?}", token.kind),
            }
        }

        Ok(MemRefType::get(ctx, shape, elem.unwrap()))
    }
}

impl Print for MemRefType {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        write!(state.buffer, "<")?;
        for dim in self.shape.iter() {
            write!(state.buffer, "{}", dim)?;
            write!(state.buffer, " x ")?;
        }
        self.elem.deref(&ctx.types).print(ctx, state)?;
        write!(state.buffer, ">")?;
        Ok(())
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Type)]
#[mnemonic = "builtin.unit"]
pub struct UnitType;

impl Verify for UnitType {}

impl Parse for UnitType {
    type Arg = ();
    type Item = ArenaPtr<TypeObj>;

    fn parse(_: (), ctx: &mut Context, _: &mut TokenStream) -> Result<Self::Item> {
        Ok(UnitType::get(ctx))
    }
}

impl Print for UnitType {
    fn print(&self, _: &Context, _: &mut PrintState) -> Result<()> { Ok(()) }
}

pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new("builtin".into());
    ctx.dialects.insert("builtin".into(), dialect);

    ModuleOp::register(ctx, ModuleOp::parse);

    UnitType::register(ctx, UnitType::parse);
    IntType::register(ctx, IntType::parse);
    FloatType::register(ctx, FloatType::parse);
    DoubleType::register(ctx, DoubleType::parse);
    TupleType::register(ctx, TupleType::parse);
    FunctionType::register(ctx, FunctionType::parse);
    MemRefType::register(ctx, MemRefType::parse);
}

#[cfg(test)]
mod tests {
    use orzir_core::{Context, Parse, Print, PrintState, TokenStream, TypeObj};

    use crate::dialects::builtin::{
        self, DoubleType, FloatType, FunctionType, IntType, MemRefType, TupleType,
    };

    #[test]
    fn test_types_cmp() {
        let mut ctx = Context::default();

        let int0 = IntType::get(&mut ctx, 32);
        let int1 = IntType::get(&mut ctx, 64);
        let int2 = IntType::get(&mut ctx, 32);
        let float0 = FloatType::get(&mut ctx);
        let float1 = FloatType::get(&mut ctx);

        let double0 = DoubleType::get(&mut ctx);
        let double1 = DoubleType::get(&mut ctx);

        assert_ne!(int0, float0);
        assert_ne!(int0, int1);
        assert_eq!(int0, int2);
        assert_eq!(float0, float1);
        assert_ne!(float0, double0);
        assert_eq!(double0, double1);

        let tuple0 = TupleType::get(&mut ctx, vec![int0, float0]);
        let tuple1 = TupleType::get(&mut ctx, vec![int0, float0]);
        let tuple2 = TupleType::get(&mut ctx, vec![int0, float0, double0]);

        assert_eq!(tuple0, tuple1);
        assert_ne!(tuple0, tuple2);

        let fn0 = FunctionType::get(&mut ctx, vec![int0, float0], vec![double0]);
        let fn1 = FunctionType::get(&mut ctx, vec![int0, float0], vec![double0]);
        let fn2 = FunctionType::get(&mut ctx, vec![int0, float0], vec![double0, int0]);

        assert_eq!(fn0, fn1);
        assert_ne!(fn0, fn2);

        let memref0 = MemRefType::get(&mut ctx, vec![1, 2, 3], int0);
        let memref1 = MemRefType::get(&mut ctx, vec![1, 2, 3], int0);
        let memref2 = MemRefType::get(&mut ctx, vec![1, 2, 3], int1);
        let memref3 = MemRefType::get(&mut ctx, vec![6, 6, 6], int1);

        assert_eq!(memref0, memref1);
        assert_ne!(memref0, memref2);
        assert_ne!(memref0, memref3);
    }

    fn test_type_parse_print(ty: &str, expected: &str) {
        let mut stream = TokenStream::new(ty);
        let mut ctx = Context::default();
        builtin::register(&mut ctx);
        let ty = TypeObj::parse((), &mut ctx, &mut stream).unwrap();
        let mut state = PrintState::new("");
        ty.deref(&ctx.types).print(&ctx, &mut state).unwrap();
        assert_eq!(state.buffer, expected);
    }

    #[test]
    fn test_int_parse() { test_type_parse_print("int<32>", "int<32>"); }

    #[test]
    fn test_float_parse() { test_type_parse_print("float", "float"); }

    #[test]
    fn test_double_parse() { test_type_parse_print("double", "double"); }

    #[test]
    fn test_tuple_parse() {
        test_type_parse_print("tuple<int<32>, float>", "tuple<int<32>, float>");
    }

    #[test]
    fn test_func_parse_0() {
        test_type_parse_print(
            "fn(int<32>, float) -> double",
            "fn(int<32>, float) -> double",
        );
    }

    #[test]
    fn test_func_parse_1() {
        test_type_parse_print(
            "fn(int<32>, float) -> tuple<int<32>, float>",
            "fn(int<32>, float) -> tuple<int<32>, float>",
        );
    }

    #[test]
    fn test_func_parse_2() {
        test_type_parse_print(
            "fn(int<32>, float) -> (int<32>, float)",
            "fn(int<32>, float) -> (int<32>, float)",
        );
    }

    #[test]
    fn test_memref_parse() {
        test_type_parse_print("memref<1 x 2 x 3 x int<32>>", "memref<1 x 2 x 3 x int<32>>");
    }
}
