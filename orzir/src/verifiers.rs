use anyhow::Result;
use orzir_core::{Context, Op, Ty, Typed};

pub mod control_flow;

/// Verifier `IsIsoaltedFromAbove` for `Op`.
///
/// An verifier indicating that the operation will not refer to any SSA values
/// from above regions.
///
/// Note that symbols can be used.
pub trait IsIsolatedFromAbove: Op {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let mut pending_regions = Vec::new();
        for region in self.regions().iter() {
            pending_regions.push(region);

            while !pending_regions.is_empty() {
                let pending_region = pending_regions.pop().unwrap().deref(&ctx.regions);
                for op in pending_region.layout().iter_ops_chained() {
                    for operand in op.deref(&ctx.ops).as_inner().operands() {
                        let operand_region = operand.deref(&ctx.values).parent_region(ctx);
                        if !region.deref(&ctx.regions).is_ancestor(ctx, operand_region) {
                            // not isolated from above
                            anyhow::bail!("operand is not isolated from above");
                        }
                    }

                    if !op.deref(&ctx.ops).as_inner().regions().is_empty()
                        && !op.deref(&ctx.ops).impls::<dyn IsIsolatedFromAbove>(ctx)
                    {
                        for sub_region in op.deref(&ctx.ops).as_inner().regions() {
                            pending_regions.push(sub_region);
                        }
                    }
                }
            }
        }

        Ok(())
    }
}

/// Verifier `IsIsolatedFromBelow` for `Op`.
///
/// A verifier indicating that the operation has excatly `N` results.
pub trait NumResults<const N: usize>: Op {
    fn verify(&self, _: &Context) -> Result<()> {
        if self.num_results() != N {
            anyhow::bail!("expected {} results, got {}", N, self.num_results());
        }
        Ok(())
    }
}

/// Verifier `NumOperands` for `Op`.
///
/// A trait indicating that the operation has excatly `N` operands.
pub trait NumOperands<const N: usize>: Op {
    fn verify(&self, _: &Context) -> Result<()> {
        if self.num_operands() != N {
            anyhow::bail!("expected {} operands, got {}", N, self.num_operands());
        }
        Ok(())
    }
}

/// Verifier `NumRegions` for `Op`.
///
/// A verifier indicating that the operation has excatly `N` regions.
pub trait NumRegions<const N: usize>: Op {
    fn verify(&self, _: &Context) -> Result<()> {
        if self.regions().len() != N {
            anyhow::bail!("expected {} regions, got {}", N, self.regions().len());
        }
        Ok(())
    }
}

/// Verifier `NumSuccessors` for `Op`
///
/// A verifier indicating that the operation has exactly `N` successors.
pub trait NumSuccessors<const N: usize>: Op {
    fn verify(&self, _: &Context) -> Result<()> {
        if self.successors().len() != N {
            anyhow::bail!("expected {} successors, got {}", N, self.successors().len());
        }
        Ok(())
    }
}

/// Verifier `AtLeastNumResults` for `Op`.
///
/// A verifier indicating that the operation has at least `N` results.
pub trait AtLeastNumResults<const N: usize>: Op {
    fn verify(&self, _: &Context) -> Result<()> {
        if self.num_results() < N {
            anyhow::bail!(
                "expected at least {} results, got {}",
                N,
                self.num_results()
            );
        }
        Ok(())
    }
}

/// Verifier `AtLeastNumOperands` for `Op`.
///
/// A verifier indicating that the operation has at least `N` operands.
pub trait AtLeastNumOperands<const N: usize>: Op {
    fn verify(&self, _: &Context) -> Result<()> {
        if self.num_operands() < N {
            anyhow::bail!(
                "expected at least {} operands, got {}",
                N,
                self.num_operands()
            );
        }
        Ok(())
    }
}

/// Verifier `AtLeastNumRegions` for `Op`.
///
/// A verifier indicating that the operation has at least `N` regions.
pub trait AtLeastNumRegions<const N: usize>: Op {
    fn verify(&self, _: &Context) -> Result<()> {
        if self.regions().len() < N {
            anyhow::bail!(
                "expected at least {} regions, got {}",
                N,
                self.regions().len()
            );
        }
        Ok(())
    }
}

/// Verifier `AtLeastNumSuccessors` for `Op`.
///
/// A verifier indicating that the operation has at least `N` successors.
pub trait AtLeastNumSuccessors<const N: usize>: Op {
    fn verify(&self, _: &Context) -> Result<()> {
        if self.successors().len() < N {
            anyhow::bail!(
                "expected at least {} successors, got {}",
                N,
                self.successors().len()
            );
        }
        Ok(())
    }
}

/// Verifier `AtMostNumResults` for `Op`.
///
/// This verifier indicates that the operation has variadic operands.
pub trait VariadicOperands: Op {
    fn verify(&self, _: &Context) -> Result<()> { Ok(()) }
}

/// Verifier `VariadicResults` for `Op`.
///
/// This verifier indicates that the operation has variadic results.
pub trait VariadicResults: Op {
    fn verify(&self, _: &Context) -> Result<()> { Ok(()) }
}

/// Verifier `VariadicRegions` for `Op`.
///
/// This verifier indicates that the operation has variadic regions.
pub trait VariadicRegions: Op {
    fn verify(&self, _: &Context) -> Result<()> { Ok(()) }
}

/// Verifier `VariadicSuccessors` for `Op`.
///
/// This verifier indicates that the operation has variadic successors.
pub trait VariadicSuccessors: Op {
    fn verify(&self, _: &Context) -> Result<()> { Ok(()) }
}

/// Verifier `IsTerminator` for `Ty`.
///
/// This verifier indicates that the type is float-like.
pub trait FloatLikeTy: Ty {
    fn verify(&self, _ctx: &Context) -> Result<()> { Ok(()) }
}

/// Verifier `IsTerminator` for `Ty`.
///
/// This verifier indicates that the type is integer-like.
pub trait IntegerLikeTy: Ty {
    fn verify(&self, _ctx: &Context) -> Result<()> { Ok(()) }
}

/// Verifier `IsTerminator` for `Op`.
///
/// This verifier indicates that the operation has float-like operands.
pub trait FloatLikeOperands: Op {
    fn verify(&self, ctx: &Context) -> Result<()> {
        for operand in self.operands() {
            let operand_ty = operand.deref(&ctx.values).ty(ctx);
            if !operand_ty.deref(&ctx.tys).impls::<dyn FloatLikeTy>(ctx) {
                anyhow::bail!("operand is not a float-like type");
            }
        }
        Ok(())
    }
}

/// Verifier `IsTerminator` for `Op`.
///
/// This verifier indicates that the operation has integer-like operands.
pub trait IntegerLikeOperands: Op {
    fn verify(&self, ctx: &Context) -> Result<()> {
        for operand in self.operands() {
            let operand_ty = operand.deref(&ctx.values).ty(ctx);
            if !operand_ty.deref(&ctx.tys).impls::<dyn IntegerLikeTy>(ctx) {
                anyhow::bail!("operand is not an integer-like type");
            }
        }
        Ok(())
    }
}

/// Verifier `SameOperandTys` for `Op`
///
/// This verifier indicates that the operands are all the same types.
pub trait SameOperandTys: Op {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let operand_tys = self.operand_tys(ctx);

        if operand_tys.is_empty() {
            return Ok(());
        }

        let operand_ty = operand_tys[0];

        for ty in operand_tys {
            if ty != operand_ty {
                anyhow::bail!("operands have different types");
            }
        }

        Ok(())
    }
}

/// Verifier `SameResultTys` for `Op`
///
/// This verifier indicates that the results are all the same type.
pub trait SameResultTys: Op {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let result_tys = self.result_tys(ctx);

        if result_tys.is_empty() {
            return Ok(());
        }

        let result_ty = result_tys[0];
        for ty in result_tys {
            if ty != result_ty {
                anyhow::bail!("results have different types");
            }
        }

        Ok(())
    }
}

/// Verifier `SameOperandAndResultTys` for `Op`.
///
/// This verifier indicates that the results and the operands all share the same
/// type. Note that the numbers of results and operands are not necessarily the
/// same.
pub trait SameOperandAndResultTys: SameOperandTys + SameResultTys {
    fn verify(&self, ctx: &Context) -> Result<()> {
        <Self as SameOperandTys>::verify(self, ctx)?;
        <Self as SameResultTys>::verify(self, ctx)?;

        let operand_tys = self.operand_tys(ctx);
        let result_tys = self.result_tys(ctx);

        if operand_tys.is_empty() {
            return Ok(());
        }

        let operand_ty = operand_tys[0];

        if result_tys.is_empty() {
            return Ok(());
        }

        let result_ty = result_tys[0];

        if operand_ty != result_ty {
            anyhow::bail!("results and operands have different types")
        }

        Ok(())
    }
}

/// Verifier `SameOperandsAndResultsNum` for `Op`.
///
/// This verifier indicates that the numbers of results and operands are the
/// same.
pub trait SameOperandsAndResultsNum: Op {
    fn verify(&self, _: &Context) -> Result<()> {
        if self.num_operands() != self.num_results() {
            anyhow::bail!("results and operands have different numbers");
        }
        Ok(())
    }
}
