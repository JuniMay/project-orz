use orzir_core::{Context, Dialect};

pub fn register(ctx: &mut Context) {
    ctx.dialects
        .insert("rv_f".into(), Dialect::new("rv_f".into()));
}
