use anyhow::Result;
use orzir::{
    dialects::{
        arith,
        builtin::{self, FloatType, FunctionType, IntType, ModuleOp},
        cf,
        func::{self, FuncOp},
    },
    interfaces::RegionKindInterface,
    verifiers::{IsIsolatedFromAbove, NumRegions, NumResults},
};
use orzir_core::{Block, Context, Print, PrintState, Region, RegionKind};

#[test]
fn test_basic_0() -> Result<()> {
    let mut ctx = Context::default();

    builtin::register(&mut ctx);
    func::register(&mut ctx);
    arith::register(&mut ctx);
    cf::register(&mut ctx);

    let module_op = ModuleOp::new(&mut ctx, None);

    let int = IntType::get(&mut ctx, 32);
    let float = FloatType::get(&mut ctx);
    let func_ty = FunctionType::get(&mut ctx, vec![int, float], vec![int]);
    let func_op = FuncOp::new(&mut ctx, "foo".into(), func_ty);

    let region = Region::builder().kind(RegionKind::Graph).parent_op(module_op).build(&mut ctx)?;

    let block = Block::builder().entry(true).parent_region(region).build(&mut ctx)?;
    region.deref_mut(&mut ctx.regions).layout_mut().append_block(block);
    region.deref_mut(&mut ctx.regions).layout_mut().append_op(block, func_op);

    let func_region =
        Region::builder().kind(RegionKind::SsaCfg).parent_op(func_op).build(&mut ctx)?;
    let func_block = Block::builder().entry(true).parent_region(func_region).build(&mut ctx)?;
    func_region.deref_mut(&mut ctx.regions).layout_mut().append_block(func_block);

    let mut print_state = PrintState::new("    ");
    module_op.deref(&ctx.ops).print(&ctx, &mut print_state)?;

    module_op.deref(&ctx.ops).as_inner().verify(&ctx)?;
    func_op.deref(&ctx.ops).as_inner().verify(&ctx)?;

    println!("{}", print_state.buffer);

    assert!(module_op.deref(&ctx.ops).impls::<dyn IsIsolatedFromAbove>(&ctx));
    assert!(module_op.deref(&ctx.ops).impls::<dyn NumRegions<1>>(&ctx));
    assert!(module_op.deref(&ctx.ops).impls::<dyn NumResults<0>>(&ctx));

    assert!(func_op.deref(&ctx.ops).impls::<dyn IsIsolatedFromAbove>(&ctx));
    assert!(func_op.deref(&ctx.ops).impls::<dyn NumRegions<1>>(&ctx));
    assert!(func_op.deref(&ctx.ops).impls::<dyn NumResults<0>>(&ctx));

    assert!(!func_op.deref(&ctx.ops).impls::<dyn NumResults<2>>(&ctx));

    assert!(!module_op
        .deref(&ctx.ops)
        .cast_ref::<dyn RegionKindInterface>(&ctx)
        .unwrap()
        .has_ssa_dominance(&ctx, 0));
    assert!(func_op
        .deref(&ctx.ops)
        .cast_ref::<dyn RegionKindInterface>(&ctx)
        .unwrap()
        .has_ssa_dominance(&ctx, 0));

    Ok(())
}