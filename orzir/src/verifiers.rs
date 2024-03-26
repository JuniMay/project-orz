use anyhow::Result;
use orzir_core::{Context, Op, Type, Typed};

pub mod control_flow;

/// Verifier `IsIsoaltedFromAbove` for `Op`.
///
/// An verifier indicating that the operation will not refer to any SSA values
/// from above regions.
///
/// Note that symbols can be used.
pub trait IsIsolatedFromAbove: Op {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let op_base = self.as_base();
        let mut pending_regions = Vec::new();
        for region in op_base.regions().iter() {
            pending_regions.push(region);

            while !pending_regions.is_empty() {
                let pending_region = pending_regions.pop().unwrap().deref(&ctx.regions);
                for op in pending_region.layout().iter_ops_chained() {
                    for operand in op.deref(&ctx.ops).as_inner().as_base().operands() {
                        let operand_region = operand.deref(&ctx.values).parent_region(ctx);
                        if !region.deref(&ctx.regions).is_ancestor(ctx, operand_region) {
                            // not isolated from above
                            anyhow::bail!("operand is not isolated from above");
                        }
                    }

                    if !op.deref(&ctx.ops).as_inner().as_base().regions().is_empty()
                        && !op.deref(&ctx.ops).impls::<dyn IsIsolatedFromAbove>(ctx)
                    {
                        for sub_region in op.deref(&ctx.ops).as_inner().as_base().regions() {
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
        let op_base = self.as_base();
        if op_base.results().len() != N {
            anyhow::bail!("expected {} results, got {}", N, op_base.results().len());
        }
        Ok(())
    }
}

/// Verifier `NumOperands` for `Op`.
///
/// A trait indicating that the operation has excatly `N` operands.
pub trait NumOperands<const N: usize>: Op {
    fn verify(&self, _: &Context) -> Result<()> {
        let op_base = self.as_base();
        if op_base.operands().len() != N {
            anyhow::bail!("expected {} operands, got {}", N, op_base.operands().len());
        }
        Ok(())
    }
}

/// Verifier `NumRegions` for `Op`.
///
/// A verifier indicating that the operation has excatly `N` regions.
pub trait NumRegions<const N: usize>: Op {
    fn verify(&self, _: &Context) -> Result<()> {
        let op_base = self.as_base();
        if op_base.regions().len() != N {
            anyhow::bail!("expected {} regions, got {}", N, op_base.regions().len());
        }
        Ok(())
    }
}

/// Verifier `NumSuccessors` for `Op`
///
/// A verifier indicating that the operation has exactly `N` successors.
pub trait NumSuccessors<const N: usize>: Op {
    fn verify(&self, _: &Context) -> Result<()> {
        let op_base = self.as_base();
        if op_base.successors().len() != N {
            anyhow::bail!(
                "expected {} successors, got {}",
                N,
                op_base.successors().len()
            );
        }
        Ok(())
    }
}

/// Verifier `AtLeastNumResults` for `Op`.
///
/// A verifier indicating that the operation has at least `N` results.
pub trait AtLeastNumResults<const N: usize>: Op {
    fn verify(&self, _: &Context) -> Result<()> {
        let op_base = self.as_base();
        if op_base.results().len() < N {
            anyhow::bail!(
                "expected at least {} results, got {}",
                N,
                op_base.results().len()
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
        let op_base = self.as_base();
        if op_base.operands().len() < N {
            anyhow::bail!(
                "expected at least {} operands, got {}",
                N,
                op_base.operands().len()
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
        let op_base = self.as_base();
        if op_base.regions().len() < N {
            anyhow::bail!(
                "expected at least {} regions, got {}",
                N,
                op_base.regions().len()
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
        let op_base = self.as_base();
        if op_base.successors().len() < N {
            anyhow::bail!(
                "expected at least {} successors, got {}",
                N,
                op_base.successors().len()
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

/// Verifier `IsTerminator` for `Type`.
///
/// This verifier indicates that the type is float-like.
pub trait FloatLikeType: Type {
    fn verify(&self, _ctx: &Context) -> Result<()> { Ok(()) }
}

/// Verifier `IsTerminator` for `Type`.
///
/// This verifier indicates that the type is integer-like.
pub trait IntegerLikeType: Type {
    fn verify(&self, _ctx: &Context) -> Result<()> { Ok(()) }
}

/// Verifier `IsTerminator` for `Op`.
///
/// This verifier indicates that the operation has float-like operands.
pub trait FloatLikeOperands: Op {
    fn verify(&self, ctx: &Context) -> Result<()> {
        for operand in self.as_base().operands() {
            let operand_ty = operand.deref(&ctx.values).ty(ctx);
            if !operand_ty.deref(&ctx.types).impls::<dyn FloatLikeType>(ctx) {
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
        for operand in self.as_base().operands() {
            let operand_ty = operand.deref(&ctx.values).ty(ctx);
            if !operand_ty.deref(&ctx.types).impls::<dyn IntegerLikeType>(ctx) {
                anyhow::bail!("operand is not an integer-like type");
            }
        }
        Ok(())
    }
}

/// Verifier `SameOperandsType` for `Op`
///
/// This verifier indicates that the operands are all the same types.
pub trait SameOperandsType: Op {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let operand_types = self.as_base().operand_types(ctx);

        if operand_types.is_empty() {
            return Ok(());
        }

        let operand_ty = operand_types[0];

        for ty in operand_types {
            if ty != operand_ty {
                anyhow::bail!("operands have different types");
            }
        }

        Ok(())
    }
}

/// Verifier `SameResultsType` for `Op`
///
/// This verifier indicates that the results are all the same type.
pub trait SameResultsType: Op {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let result_types = self.as_base().result_types(ctx);

        if result_types.is_empty() {
            return Ok(());
        }

        let result_ty = result_types[0];
        for ty in result_types {
            if ty != result_ty {
                anyhow::bail!("results have different types");
            }
        }

        Ok(())
    }
}

/// Verifier `SameOperandsAndResultsType` for `Op`.
///
/// This verifier indicates that the results and the operands all share the same
/// type. Note that the numbers of results and operands are not necessarily the
/// same.
pub trait SameOperandsAndResultsType: SameOperandsType + SameResultsType {
    fn verify(&self, ctx: &Context) -> Result<()> {
        <Self as SameOperandsType>::verify(self, ctx)?;
        <Self as SameResultsType>::verify(self, ctx)?;

        let operand_types = self.as_base().operand_types(ctx);
        let result_types = self.as_base().result_types(ctx);

        if operand_types.is_empty() {
            return Ok(());
        }

        let operand_type = operand_types[0];

        if result_types.is_empty() {
            return Ok(());
        }

        let result_type = result_types[0];

        if operand_type != result_type {
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
        if self.as_base().operands().len() != self.as_base().results().len() {
            anyhow::bail!("results and operands have different numbers");
        }
        Ok(())
    }
}
