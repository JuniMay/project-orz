use anyhow::Result;
use orzir_core::{Context, Op};

/// Verifier `IsTerminator` for `Op`.
///
/// This verifier indicates that the operation is a terminator.
pub trait IsTerminator: Op {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let parent_region = self.as_base().parent_region(ctx);

        if parent_region.is_none() {
            anyhow::bail!("terminator must be in a region");
        }

        if parent_region
            .unwrap()
            .deref(&ctx.regions)
            .layout()
            .exit_op_at(self.as_base().parent_block().unwrap())
            != Some(self.as_base().self_ptr())
        {
            anyhow::bail!("terminator is not the last operation in the block");
        }

        Ok(())
    }
}

/// Verifier `NoTerminator` for `Op`.
///
/// This verifier indicates that the regions in the operation do not need a
/// terminator.
pub trait NoTerminator: Op {
    fn verify(&self, _ctx: &Context) -> Result<()> { Ok(()) }
}
