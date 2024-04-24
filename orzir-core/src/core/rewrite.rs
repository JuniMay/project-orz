use crate::{ArenaPtr, Context, OpObj, RewriteResult};

/// The trait for unified rewriting operations.
///
/// TODO: design a better API for this.
pub trait PatternRewriter {
    /// Erase an operation from the IR.
    fn erase_op(&self, ctx: &mut Context, op: ArenaPtr<OpObj>) -> RewriteResult<()>;

    /// Replace an operation with new operation(s)
    fn replace_op(
        &self,
        ctx: &mut Context,
        op: ArenaPtr<OpObj>,
        new_ops: Vec<ArenaPtr<OpObj>>,
    ) -> RewriteResult<()>;
}

/// A pattern for rewriting operations.
///
/// TODO: design a better API for this.
pub trait RewritePattern<Rewriter: PatternRewriter> {
    /// Try to match the pattern with the given operation.
    fn matches(&self, ctx: &Context, op: ArenaPtr<OpObj>) -> RewriteResult<()>;

    /// Rewrite the operation with the pattern.
    fn rewrite(
        &self,
        ctx: &mut Context,
        op: ArenaPtr<OpObj>,
        rewriter: &Rewriter,
    ) -> RewriteResult<()>;
}
