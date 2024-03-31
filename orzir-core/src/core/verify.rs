use crate::{Context, VerificationResult};

pub trait Verify: RunVerifiers {
    fn verify(&self, ctx: &Context) -> VerificationResult<()> { self.run_verifiers(ctx) }
}

pub trait RunVerifiers {
    fn run_verifiers(&self, ctx: &Context) -> VerificationResult<()>;
}
