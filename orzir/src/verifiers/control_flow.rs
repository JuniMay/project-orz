use orzir_core::{verify_error, Context, Op, VerifyResult};
use thiserror::Error;

#[derive(Debug, Error)]
#[error("operation is not a terminator")]
struct NotTerminatorError;

/// Verifier `IsTerminator` for `Op`.
///
/// This verifier indicates that the operation is a terminator.
pub trait IsTerminator: Op {
    fn verify(&self, ctx: &Context) -> VerifyResult<()> {
        let parent_region = self.parent_region(ctx);

        if parent_region.is_none() {
            panic!("terminator is not in a region");
        }

        if self
            .parent_block()
            .unwrap()
            .deref(&ctx.blocks)
            .layout()
            .back()
            != Some(self.self_ptr())
        {
            return verify_error!(NotTerminatorError).into();
        }

        Ok(())
    }
}

/// Verifier `NoTerminator` for `Op`.
///
/// This verifier indicates that the regions in the operation do not need a
/// terminator.
pub trait NoTerminator: Op {
    fn verify(&self, _ctx: &Context) -> VerifyResult<()> { Ok(()) }
}
