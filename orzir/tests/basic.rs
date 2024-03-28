use anyhow::Result;
use orzir::{
    dialects::{
        arith,
        builtin::{self, FloatTy, FunctionTy, IntTy, ModuleOp},
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

    let module_op = ctx.ops.reserve();
    let func_op = ctx.ops.reserve();

    let int = IntTy::get(&mut ctx, 32);
    let float = FloatTy::get(&mut ctx);
    let func_ty = FunctionTy::get(&mut ctx, vec![int, float], vec![int]);

    let region = Region::new(&mut ctx, RegionKind::Graph, module_op, 0);
    let block = Block::new(&mut ctx, true, region, None);
    region.deref_mut(&mut ctx.regions).layout_mut().append(block).unwrap();
    block.deref_mut(&mut ctx.blocks).layout_mut().append(func_op).unwrap();

    let module_op = ModuleOp::new(&mut ctx, module_op, region, Some("foo".to_string()));

    let func_region = Region::new(&mut ctx, RegionKind::SsaCfg, func_op, 0);
    let func_block = Block::new(&mut ctx, true, func_region, None);
    func_region.deref_mut(&mut ctx.regions).layout_mut().append(func_block).unwrap();

    let func_op = FuncOp::new(&mut ctx, func_op, func_region, "foo".to_string(), func_ty);

    let mut print_state = PrintState::new("    ");
    module_op.deref(&ctx.ops).print(&ctx, &mut print_state)?;

    module_op.deref(&ctx.ops).as_ref().verify(&ctx)?;
    func_op.deref(&ctx.ops).as_ref().verify(&ctx)?;

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

    assert!(
        module_op.deref(&ctx.ops).as_a::<ModuleOp>().unwrap().get_region_kind(&ctx, 0)
            == RegionKind::Graph
    );

    assert!(
        func_op.deref(&ctx.ops).as_a::<FuncOp>().unwrap().get_region_kind(&ctx, 0)
            == RegionKind::SsaCfg
    );

    Ok(())
}
