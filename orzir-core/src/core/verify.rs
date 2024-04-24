use crate::{Context, VerifyResult};

pub trait Verify: RunVerifiers {
    fn verify(&self, ctx: &Context) -> VerifyResult<()> { self.run_verifiers(ctx) }
}

pub trait RunVerifiers {
    fn run_verifiers(&self, ctx: &Context) -> VerifyResult<()>;
}
