use orzir_core::{Context, Op, RegionKind};

pub trait RegionKindInterface: Op {
    fn get_region_kind(&self, ctx: &Context, index: usize) -> RegionKind {
        self.as_base().get_region(index).unwrap().deref(&ctx.regions).kind()
    }

    fn has_ssa_dominance(&self, ctx: &Context, index: usize) -> bool {
        self.get_region_kind(ctx, index) == RegionKind::SsaCfg
    }
}
