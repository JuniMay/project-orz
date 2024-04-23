use orzir_core::Context;

pub mod basic;
pub mod regs;
pub mod rv_f;
pub mod rv_m;

/// Register the riscv dialects according to the ISA extension name.
pub fn register_riscv_dialects(ctx: &mut Context, spec: &str) {
    let spec = spec.to_lowercase();
    let spec = spec.replace('g', "imafd_zicsr_zifencei");

    basic::register(ctx);

    if spec.contains('m') {
        rv_m::register(ctx);
    }

    if spec.contains('f') {
        rv_f::register(ctx);
        // TODO: RVF implies Zicsr extension.
    }
}
