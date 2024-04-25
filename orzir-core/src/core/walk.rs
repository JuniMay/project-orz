/// Walker for the IR.
///
/// The walkder visits the IR and execute the callback function on each node.
/// Mutate the IR while walking/iterating/traversing it can cause some problems
/// and is hard to debug. Thus, the walker and the callback functions *cannot*
/// directly edit the IR. All the mutations can be recorded in the state and
/// perform a transaction-like operation after the walk.
///
/// For rewriting, there should be a marker for operations that are erased
/// rather than directly removing them from the IR.
///
/// The walker can be used for conversion/rewriting or analysis. This provides a
/// standard way to interact with the IR structure.
///
/// The implementation is based on the concepts in [pliron](https://github.com/vaivaswatha/pliron),
/// especially the `IrNode` and the usage of `std::ops::ControlFlow`.
use crate::{ArenaPtr, Block, Context, OpObj, Region};

/// The node in the IR to walk.
///
/// This will be passed to the callback function and the callback function
/// should decide whether to do and what to do with the node.
pub enum IrNode {
    /// An operation.
    Op(ArenaPtr<OpObj>),
    /// A region.
    Region(ArenaPtr<Region>),
    /// A block.
    Block(ArenaPtr<Block>),
}

/// The order to walk the IR.
pub enum WalkOrder {
    /// Visit the node before walking its children.
    ///
    /// If the callback function returns [`WalkResultKind::Skip`], the children
    /// will be skipped.
    Pre,
    /// Visit the node after walking its children.
    Post,
}

/// The direction to walk the children of a node.
pub enum WalkDirection {
    /// Walk the children in the forward direction.
    Forward,
    /// Walk the children in the reverse direction.
    Reverse,
}

pub struct WalkOption(pub WalkOrder, pub WalkDirection);

/// The result of the walk.
///
/// This is similar to MLIR's `WalkResult::ResultEnum`, except that the
/// `Interrupt` is represented with [`std::ops::ControlFlow::Break`].
pub enum WalkResultKind {
    /// Continue the walk.
    Continue,
    Skip,
}

/// The result of the walk.
pub type WalkResult<T> = std::ops::ControlFlow<T, WalkResultKind>;

/// The callback function for the walker.
pub type WalkCallback<State, T = ()> = fn(&Context, &mut State, IrNode) -> WalkResult<T>;

/// Interrupt the walk.
pub fn interrupt_walk<T>(t: T) -> WalkResult<T> { std::ops::ControlFlow::Break(t) }

/// Continue the walk.
pub fn continue_walk<T>() -> WalkResult<T> {
    std::ops::ControlFlow::Continue(WalkResultKind::Continue)
}

/// Skip the walk.
pub fn skip_walk<T>() -> WalkResult<T> { std::ops::ControlFlow::Continue(WalkResultKind::Skip) }

/// The walker for the IR.
///
/// This is actually a simple container for the walk options.
pub struct Walker {
    pub ops: WalkOption,
    pub regions: WalkOption,
    pub blocks: WalkOption,
}

impl Walker {
    pub fn new(ops: WalkOption, regions: WalkOption, blocks: WalkOption) -> Self {
        Self {
            ops,
            regions,
            blocks,
        }
    }

    /// Visit an operation and walk its children.
    pub fn walk_op<State, T>(
        &self,
        ctx: &Context,
        state: &mut State,
        op: ArenaPtr<OpObj>,
        callback: WalkCallback<State, T>,
    ) -> WalkResult<T> {
        if let WalkOrder::Pre = self.regions.0 {
            if let WalkResultKind::Skip = callback(ctx, state, IrNode::Op(op))? {
                return skip_walk();
            }
        }

        let op = op.deref(&ctx.ops).as_ref();
        let num_regions = op.num_regions();

        let iter = (0..num_regions).map(|i| op.get_region(i).unwrap());

        match self.regions.1 {
            WalkDirection::Forward => {
                for region in iter {
                    self.walk_region(ctx, state, region, callback)?;
                }
            }
            WalkDirection::Reverse => {
                for region in iter.rev() {
                    self.walk_region(ctx, state, region, callback)?;
                }
            }
        }

        if let WalkOrder::Post = self.regions.0 {
            callback(ctx, state, IrNode::Op(op.self_ptr()))?;
        }

        continue_walk()
    }

    /// Visit a region and walk the blocks.
    pub fn walk_region<State, T>(
        &self,
        ctx: &Context,
        state: &mut State,
        region: ArenaPtr<Region>,
        callback: WalkCallback<State, T>,
    ) -> WalkResult<T> {
        if let WalkOrder::Pre = self.blocks.0 {
            if let WalkResultKind::Skip = callback(ctx, state, IrNode::Region(region))? {
                return skip_walk();
            }
        }

        let layout = region.deref(&ctx.regions).layout();

        match self.blocks.1 {
            WalkDirection::Forward => {
                for block in layout.iter() {
                    self.walk_block(ctx, state, block, callback)?;
                }
            }
            WalkDirection::Reverse => {
                for (block, _) in layout.into_iter().rev() {
                    self.walk_block(ctx, state, block, callback)?;
                }
            }
        }

        if let WalkOrder::Post = self.blocks.0 {
            callback(ctx, state, IrNode::Region(region))?;
        }

        continue_walk()
    }

    /// Visit a block and walk the operations.
    pub fn walk_block<State, T>(
        &self,
        ctx: &Context,
        state: &mut State,
        block: ArenaPtr<Block>,
        callback: WalkCallback<State, T>,
    ) -> WalkResult<T> {
        if let WalkOrder::Pre = self.ops.0 {
            if let WalkResultKind::Skip = callback(ctx, state, IrNode::Block(block))? {
                return skip_walk();
            }
        }

        let layout = block.deref(&ctx.blocks).layout();

        match self.ops.1 {
            WalkDirection::Forward => {
                for op in layout.iter() {
                    self.walk_op(ctx, state, op, callback)?;
                }
            }
            WalkDirection::Reverse => {
                for (op, _) in layout.into_iter().rev() {
                    self.walk_op(ctx, state, op, callback)?;
                }
            }
        }

        if let WalkOrder::Post = self.ops.0 {
            callback(ctx, state, IrNode::Block(block))?;
        }

        continue_walk()
    }
}
