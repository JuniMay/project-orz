use orzir_core::Context;

pub mod arith;
pub mod builtin;
pub mod cf;
pub mod func;
pub mod mem;

pub fn register_std_dialects(ctx: &mut Context) {
    builtin::register(ctx);
    arith::register(ctx);
    cf::register(ctx);
    func::register(ctx);
    mem::register(ctx);
}
