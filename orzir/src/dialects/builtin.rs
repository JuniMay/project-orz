use anyhow::Result;
use orzir_core::{
    ArenaPtr, Block, Context, Dialect, Op, OpObj, OpResultBuilder, Parse, Print, PrintState,
    Region, RegionKind, TokenKind, TokenStream, Type, TypeObj,
};
use orzir_macros::{op, ty};
use std::fmt::Write;

#[op("builtin.module")]
pub struct ModuleOp {
    symbol: Option<String>,
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
        let _region = Region::parse(region_builder, ctx, stream);

        Ok(op)
    }
}

impl Print for ModuleOp {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        if let Some(symbol) = &self.symbol {
            write!(state.buffer, "@{}", symbol)?;
        }

        self.as_base()
            .get_region(0)
            .unwrap()
            .deref(&ctx.regions)
            .print(ctx, state)?;

        Ok(())
    }
}

#[derive(Debug, Hash, PartialEq, Eq)]
#[ty("builtin.int")]
pub struct IntType(usize);

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

#[derive(Debug, Hash, PartialEq, Eq)]
#[ty("builtin.float")]
pub struct FloatType;

impl Parse for FloatType {
    type Arg = ();
    type Item = ArenaPtr<TypeObj>;

    fn parse(_: (), ctx: &mut Context, _: &mut TokenStream) -> Result<Self::Item> {
        Ok(FloatType::get(ctx))
    }
}

impl Print for FloatType {
    fn print(&self, _: &Context, _: &mut PrintState) -> Result<()> {
        Ok(())
    }
}

#[derive(Debug, Hash, PartialEq, Eq)]
#[ty("builtin.double")]
pub struct DoubleType;

impl Parse for DoubleType {
    type Arg = ();
    type Item = ArenaPtr<TypeObj>;

    fn parse(_: (), ctx: &mut Context, _: &mut TokenStream) -> Result<Self::Item> {
        Ok(DoubleType::get(ctx))
    }
}

impl Print for DoubleType {
    fn print(&self, _: &Context, _: &mut PrintState) -> Result<()> {
        Ok(())
    }
}

#[derive(Debug, Hash, PartialEq, Eq)]
#[ty("builtin.tuple")]
pub struct TupleType {
    elems: Vec<ArenaPtr<TypeObj>>,
}

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

pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new("builtin".into());
    ctx.dialects.insert("builtin".into(), dialect);

    ModuleOp::register(ctx, ModuleOp::parse);

    IntType::register(ctx, IntType::parse);
    FloatType::register(ctx, FloatType::parse);
    DoubleType::register(ctx, DoubleType::parse);
    TupleType::register(ctx, TupleType::parse);
}

#[cfg(test)]
mod tests {
    use orzir_core::{Context, Parse, Print, PrintState, TokenStream, TypeObj};

    use crate::dialects::builtin::{self, DoubleType, FloatType, IntType, TupleType};

    #[test]
    fn test_types() {
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
    fn test_int_parse() {
        test_type_parse_print("int<32>", "builtin.int<32>");
    }

    #[test]
    fn test_float_parse() {
        test_type_parse_print("float", "builtin.float");
    }

    #[test]
    fn test_double_parse() {
        test_type_parse_print("double", "builtin.double");
    }

    #[test]
    fn test_tuple_parse() {
        test_type_parse_print(
            "tuple<int<32>, float>",
            "builtin.tuple<builtin.int<32>, builtin.float>",
        );
    }
}
