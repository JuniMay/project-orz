use std::fmt::Write;

use orzir_core::{
    delimiter, parse_error, token_wildcard, ArenaPtr, Context, Dialect, Op, OpMetadata, Parse,
    ParseErrorKind, Print, PrintResult, PrintState, TokenKind, TyObj, Value,
};
use orzir_macros::{ControlFlow, DataFlow, Op, Parse, Print, RegionInterface, Verify};

use super::builtin::Symbol;
use crate::verifiers::*;

pub enum GlobalInit {
    ZeroInit,
    Undef,
    Bytes(Vec<u8>),
}

impl Print for GlobalInit {
    fn print(&self, _: &Context, state: &mut PrintState) -> PrintResult<()> {
        match self {
            GlobalInit::ZeroInit => write!(state.buffer, "zeroinit")?,
            GlobalInit::Undef => write!(state.buffer, "undef")?,
            GlobalInit::Bytes(bytes) => {
                write!(state.buffer, "bytes[")?;
                for (i, byte) in bytes.iter().enumerate() {
                    if i != 0 {
                        write!(state.buffer, ", ")?;
                    }
                    // hex
                    write!(state.buffer, "{:02x}", byte)?;
                }
                write!(state.buffer, "]")?;
            }
        }
        Ok(())
    }
}

impl Parse for GlobalInit {
    type Item = Self;

    fn parse(
        _: &mut Context,
        state: &mut orzir_core::ParseState,
    ) -> orzir_core::ParseResult<Self::Item> {
        let token = state.stream.consume()?;
        match token.kind {
            TokenKind::Tokenized(ref s) => match s.as_str() {
                "zeroinit" => Ok(GlobalInit::ZeroInit),
                "undef" => Ok(GlobalInit::Undef),
                "bytes" => {
                    let mut bytes = Vec::new();
                    state.stream.expect(delimiter!('['))?;
                    loop {
                        let token = state.stream.consume()?;
                        match token.kind {
                            TokenKind::Tokenized(ref s) => {
                                // parse as hex
                                let byte = u8::from_str_radix(s, 16).map_err(|_| {
                                    parse_error!(
                                        token.span,
                                        // TODO: Better error message
                                        ParseErrorKind::InvalidToken(
                                            vec![token_wildcard!("...")].into(),
                                            token.kind
                                        )
                                    )
                                })?;
                                bytes.push(byte);
                            }
                            TokenKind::Char(']') => break,
                            TokenKind::Char(',') => continue,
                            _ => {
                                return parse_error!(
                                    token.span,
                                    ParseErrorKind::InvalidToken(
                                        vec![
                                            delimiter!(']'),
                                            delimiter!(','),
                                            token_wildcard!("...")
                                        ]
                                        .into(),
                                        token.kind
                                    )
                                )
                                .into()
                            }
                        }
                    }
                    Ok(GlobalInit::Bytes(bytes))
                }
                _ => parse_error!(
                    token.span,
                    ParseErrorKind::InvalidToken(
                        vec![
                            TokenKind::Tokenized("zeroinit".into()),
                            TokenKind::Tokenized("undef".into()),
                            TokenKind::Tokenized("bytes".into())
                        ]
                        .into(),
                        token.kind
                    )
                )
                .into(),
            },
            _ => parse_error!(
                token.span,
                ParseErrorKind::InvalidToken(vec![token_wildcard!("...")].into(), token.kind)
            )
            .into(),
        }
    }
}

/// Allocate a global memory slot.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "mem.global"]
#[verifiers(NumResults<0>, NumRegions<0>, NumOperands<0>)]
#[format(pattern = "{symbol} : {ty} = {init}", kind = "op", num_results = 0)]
pub struct GlobalOp {
    #[metadata]
    metadata: OpMetadata,
    /// The symbol of the global memory slot.
    symbol: Symbol,
    /// The type of the global memory slot.
    ty: ArenaPtr<TyObj>,
    /// The initial value of the global memory slot.
    init: GlobalInit,
}

/// Get a global slot as an SSA value.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "mem.get_global"]
#[verifiers(NumResults<1>, NumRegions<0>, NumOperands<0>)]
#[format(pattern = "{symbol}", kind = "op", num_results = 1)]
pub struct GetGlobalOp {
    #[metadata]
    metadata: OpMetadata,
    /// The symbol of the global memory slot.
    #[result(0)]
    value: ArenaPtr<Value>,
    /// The symbol of the global memory slot.
    symbol: Symbol,
}

/// Allocate a local memory slot which will be deallocated when the function
/// returns.
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "mem.alloca"]
#[verifiers(NumResults<1>, NumRegions<0>, NumOperands<0>)]
#[format(pattern = "{elem_ty}", kind = "op", num_results = 1)]
pub struct AllocaOp {
    #[metadata]
    metadata: OpMetadata,
    /// The allocated memory slot.
    #[result(0)]
    ptr: ArenaPtr<Value>,
    /// The element type inside the memory slot.
    elem_ty: ArenaPtr<TyObj>,
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "mem.load"]
#[verifiers(NumResults<1>, NumRegions<0>, VariadicOperands)]
#[format(pattern = "{ptr} {indices}", kind = "op", num_results = 1)]
pub struct LoadOp {
    #[metadata]
    metadata: OpMetadata,
    /// The loaded value.
    #[result(0)]
    value: ArenaPtr<Value>,
    /// The memory slot to load from.
    #[operand(0)]
    ptr: ArenaPtr<Value>,
    /// The indices to access the memory slot.
    #[operand(1..)]
    #[repeat(sep = ",", leading = "[", trailing = "]")]
    indices: Vec<ArenaPtr<Value>>,
}

#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "mem.store"]
#[verifiers(NumResults<0>, NumRegions<0>, VariadicOperands)]
#[format(pattern = "{value} , {ptr} {indices}", kind = "op", num_results = 0)]
pub struct StoreOp {
    #[metadata]
    metadata: OpMetadata,
    /// The value to store.
    #[operand(0)]
    value: ArenaPtr<Value>,
    /// The memory slot to store into.
    #[operand(1)]
    ptr: ArenaPtr<Value>,
    /// The indices to access the memory slot.
    #[operand(2..)]
    #[repeat(sep = ",", leading = "[", trailing = "]")]
    indices: Vec<ArenaPtr<Value>>,
}

/// Casting memory slot types
#[derive(Op, DataFlow, RegionInterface, ControlFlow, Parse, Print, Verify)]
#[mnemonic = "mem.cast"]
#[verifiers(NumResults<1>, NumRegions<0>, NumOperands<1>)]
#[format(pattern = "{ptr}", kind = "op", num_results = 1)]
pub struct CastOp {
    #[metadata]
    metadata: OpMetadata,
    /// The casted memory slot.
    #[result(0)]
    result: ArenaPtr<Value>,
    /// The memory slot to cast.
    #[operand(0)]
    ptr: ArenaPtr<Value>,
}

pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new("mem".into());
    ctx.dialects.insert("mem".into(), dialect);

    GlobalOp::register(ctx, GlobalOp::parse);
    GetGlobalOp::register(ctx, GetGlobalOp::parse);
    AllocaOp::register(ctx, AllocaOp::parse);
    LoadOp::register(ctx, LoadOp::parse);
    StoreOp::register(ctx, StoreOp::parse);
    CastOp::register(ctx, CastOp::parse);
}

#[cfg(test)]
mod tests {
    use orzir_core::{Context, OpObj, Parse, ParseState, Print, PrintState, TokenStream};

    use crate::dialects::std::{arith, builtin, cf, func, mem};

    fn test_parse_print(src: &str, expected: &str) {
        let stream = TokenStream::new(src);
        let mut state = ParseState::new(stream);
        let mut ctx = Context::default();

        builtin::register(&mut ctx);
        func::register(&mut ctx);
        arith::register(&mut ctx);
        mem::register(&mut ctx);
        cf::register(&mut ctx);

        let item = OpObj::parse(&mut ctx, &mut state).unwrap();
        let mut state = PrintState::new("");
        item.deref(&ctx.ops).print(&ctx, &mut state).unwrap();

        assert_eq!(state.buffer, expected);
    }

    #[test]
    fn test_mem_op() {
        let src = r#"
            %slot = mem.alloca int<32> : memref<int<32>, [1]>
        "#;
        let expected = r#"%slot = mem.alloca int<32> : memref<int<32>, [1]>"#;
        test_parse_print(src, expected);
    }

    #[test]
    fn test_mem_op_2() {
        let src = r#"
        module {
            mem.global @global_slot : memref<int<32>, [2]> = bytes[
                ef, be, ad, de, 
                78, 56, 34, 12,
            ]
            mem.global @global_zero : memref<int<32>, [1 * 2 * 3]> = zeroinit
            mem.global @global_undef : memref<int<32>, [114514 * 4]> = undef

            func.func @test_mem : fn() -> int<32> {
                %global_slot = mem.get_global @global_slot : memref<int<32>, [2]>
                %casted_slot = mem.cast %global_slot : memref<int<8>, [8]>

                %slot = mem.alloca int<32> : memref<int<32>, [2 * 3 * 4]>
                cf.jump ^main
            ^main:
                %a = arith.iconst 1i64 : index
                %b = arith.iconst 2i64 : index
                %c = arith.iconst 3i64 : index
                
                %val = mem.load %slot[%a, %b, %c] : int<32>

                mem.store %val, %slot[%a, %b, %c]

                func.return %val
            }
        }

        "#;
        let stream = TokenStream::new(src);
        let mut state = ParseState::new(stream);
        let mut ctx = Context::default();

        builtin::register(&mut ctx);
        func::register(&mut ctx);
        arith::register(&mut ctx);
        mem::register(&mut ctx);
        cf::register(&mut ctx);

        let item = OpObj::parse(&mut ctx, &mut state).unwrap();
        let mut state = PrintState::new("    ");
        item.deref(&ctx.ops).print(&ctx, &mut state).unwrap();

        println!("{}", state.buffer);
    }
}
