use anyhow::Result;

use crate::Context;

pub trait Verify: RunVerifiers {
    fn verify(&self, ctx: &Context) -> Result<()> { self.run_verifiers(ctx) }
}

pub trait RunVerifiers {
    fn run_verifiers(&self, ctx: &Context) -> Result<()>;
}
