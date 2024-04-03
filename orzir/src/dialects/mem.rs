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

pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new("mem".into());
    ctx.dialects.insert("mem".into(), dialect);

    AllocaOp::register(ctx, AllocaOp::parse);
}

#[cfg(test)]
mod tests {
    use orzir_core::{Context, OpObj, Parse, ParseState, Print, PrintState, TokenStream};

    use crate::dialects::{builtin, mem};

    fn test_parse_print(src: &str, expected: &str) {
        let stream = TokenStream::new(src);
        let mut state = ParseState::new(stream);
        let mut ctx = Context::default();

        builtin::register(&mut ctx);
        mem::register(&mut ctx);

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
}
