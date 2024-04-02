use std::collections::HashMap;

use orzir_core::{list::ListNode, ArenaPtr, Block, Context, OpObj};

#[derive(Default)]
pub struct CfgNode {
    succs: Vec<ArenaPtr<Block>>,
    preds: Vec<ArenaPtr<Block>>,
}

/// The control flow graph of a region with
/// [`RegionKind::SsaCfg`](orzir_core::RegionKind::SsaCfg).
#[derive(Default)]
pub struct Cfg {
    nodes: HashMap<ArenaPtr<Block>, CfgNode>,
}

impl Cfg {
    pub fn succs(&self, block: ArenaPtr<Block>) -> &[ArenaPtr<Block>] {
        self.nodes[&block].succs.as_slice()
    }

    pub fn preds(&self, block: ArenaPtr<Block>) -> &[ArenaPtr<Block>] {
        self.nodes[&block].preds.as_slice()
    }
}

pub struct ControlFlowAnalysis {
    /// The operation that the analysis is running on.
    op: ArenaPtr<OpObj>,
}

impl ControlFlowAnalysis {
    pub fn new(op: ArenaPtr<OpObj>) -> Self { Self { op } }

    /// Get the operation that the analysis is running on.
    pub fn op(&self) -> ArenaPtr<OpObj> { self.op }

    /// Run the control flow analysis.
    ///
    /// This will produce a map from the region index to the control flow graph.
    pub fn run(&self, ctx: &Context) -> HashMap<usize, Cfg> {
        let op = self.op.deref(&ctx.ops).as_ref();
        let mut cfgs = HashMap::new();

        for region_idx in 0..op.num_regions() {
            if !op.has_ssa_dominance(ctx, region_idx) {
                continue;
            }

            let region = op.get_region(region_idx).unwrap().deref(&ctx.regions);
            let mut cfg = Cfg::default();

            for block_ptr in region.layout().iter() {
                let block = block_ptr.deref(&ctx.blocks);

                // block should always have a terminator.
                let terminator = block.layout().back();

                if let Some(terminator) = terminator {
                    let terminator = terminator.deref(&ctx.ops).as_ref();

                    for succ in terminator.successors() {
                        cfg.nodes
                            .entry(block_ptr)
                            .or_default()
                            .succs
                            .push(succ.block());
                        cfg.nodes
                            .entry(succ.block())
                            .or_default()
                            .preds
                            .push(block_ptr);
                    }
                } else {
                    // just get next block as successor.
                    let next_block = region
                        .layout()
                        .node(block_ptr)
                        .unwrap()
                        .next()
                        .expect("block should have a successor");

                    cfg.nodes
                        .entry(block_ptr)
                        .or_default()
                        .succs
                        .push(next_block);
                    cfg.nodes
                        .entry(next_block)
                        .or_default()
                        .preds
                        .push(block_ptr);
                }
            }

            cfgs.insert(region_idx, cfg);
        }
        cfgs
    }
}
