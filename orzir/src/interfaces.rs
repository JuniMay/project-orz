use anyhow::Result;
use orzir_core::{Context, Op};

pub trait IsIsolatedFromAbove: Op {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let op_base = self.as_base();
        let mut pending_regions = Vec::new();
        for region in op_base.regions().iter() {
            pending_regions.push(region);

            while !pending_regions.is_empty() {
                let pending_region = pending_regions.pop().unwrap().deref(&ctx.regions);
                for op in pending_region.layout().iter_ops_chained() {
                    for operand in op.deref(&ctx.ops).as_inner().as_base().operands() {
                        let operand_region = operand.deref(&ctx.values).parent_region(ctx);
                        if !region.deref(&ctx.regions).is_ancestor(ctx, operand_region) {
                            // not isolated from above
                            anyhow::bail!("operand is not isolated from above");
                        }
                    }

                    if !op.deref(&ctx.ops).as_inner().as_base().regions().is_empty()
                        && !op.deref(&ctx.ops).impls::<dyn IsIsolatedFromAbove>()
                    {
                        for sub_region in op.deref(&ctx.ops).as_inner().as_base().regions() {
                            pending_regions.push(sub_region);
                        }
                    }
                }
            }
        }

        Ok(())
    }
}
