use std::collections::HashMap;

use orzir_core::{list::ListNode, ArenaPtr, Block, Context, OpObj};

#[derive(Default, Debug)]
pub struct CfgNode {
    succs: Vec<ArenaPtr<Block>>,
    preds: Vec<ArenaPtr<Block>>,
}

/// The control flow graph of a region with
/// [`RegionKind::SsaCfg`](orzir_core::RegionKind::SsaCfg).
#[derive(Default, Debug)]
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

#[cfg(test)]
mod tests {
    use orzir_core::{Context, OpObj, Parse, ParseState, TokenStream};

    use super::ControlFlowAnalysis;
    use crate::dialects::std::{arith, builtin, cf, func};

    #[test]
    fn test_cfg() {
        let src = r#"
        module {
            func.func @foo : fn () -> int<32> {
            ^entry:
                %a = arith.iconst 123i32 : int<32>
                %b = arith.iconst 456i32 : int<32>

                %cond = arith.iconst true : int<32>

                cf.branch %cond, ^then(%a), ^else(%b)

            ^then(%x: int<32>):
                cf.jump ^return

            ^else(%y: int<32>):
                cf.jump ^return

            ^return:
                func.return %a
            }
        }
        "#;

        let stream = TokenStream::new(src);
        let mut state = ParseState::new(stream);
        let mut ctx = Context::default();

        builtin::register(&mut ctx);
        func::register(&mut ctx);
        arith::register(&mut ctx);
        cf::register(&mut ctx);

        let op = OpObj::parse(&mut ctx, &mut state).unwrap();

        let func_op = op
            .deref(&ctx.ops)
            .as_ref()
            .get_region(0)
            .unwrap()
            .deref(&ctx.regions)
            .lookup_symbol(&ctx, "foo")
            .unwrap();

        let cfa = ControlFlowAnalysis::new(func_op);
        let cfg = cfa.run(&ctx);

        dbg!(cfg);
    }
}
