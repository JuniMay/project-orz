use anyhow::Result;

use crate::Context;

pub trait Verify {
    fn verify(&self, ctx: &Context) -> Result<()>;
}
