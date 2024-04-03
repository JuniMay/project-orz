use std::fmt::Write;

use orzir_core::{ArenaPtr, Context, Dialect, Op, OpMetadata, Parse, TyObj, Value};
use orzir_macros::{ControlFlow, DataFlow, Op, Parse, Print, RegionInterface, Verify};

use crate::verifiers::*;

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

pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new("mem".into());
    ctx.dialects.insert("mem".into(), dialect);

    AllocaOp::register(ctx, AllocaOp::parse);
    LoadOp::register(ctx, LoadOp::parse);
    StoreOp::register(ctx, StoreOp::parse);
}

#[cfg(test)]
mod tests {
    use orzir_core::{Context, OpObj, Parse, ParseState, Print, PrintState, TokenStream};

    use crate::dialects::{arith, builtin, cf, func, mem};

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
            func.func @test_mem : fn() -> int<32> {
                %slot = mem.alloca int<32> : memref<int<32>, [2 * 3 * 4]>
                cf.jump ^main
            ^main:
                %a = arith.iconst 1 : index
                %b = arith.iconst 2 : index
                %c = arith.iconst 3 : index
                
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
