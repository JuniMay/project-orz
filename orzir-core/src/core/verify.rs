use anyhow::Result;

use crate::Context;

pub trait Verify: VerifyInterfaces {
    fn verify(&self, ctx: &Context) -> Result<()> { self.verify_interfaces(ctx) }
}

pub trait VerifyInterfaces {
    fn verify_interfaces(&self, ctx: &Context) -> Result<()>;
}
