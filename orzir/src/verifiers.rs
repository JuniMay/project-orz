use orzir_core::{verify_error, Context, Op, Ty, VerifyResult};
use thiserror::Error;

pub mod control_flow;

#[derive(Debug, Error)]
#[error("operand is not isolated from above")]
struct NotIsolatedFromAboveError;

/// Verifier `IsIsoaltedFromAbove` for `Op`.
///
/// An verifier indicating that the operation will not refer to any SSA values
/// from above regions.
///
/// Note that symbols can be used.
pub trait IsIsolatedFromAbove: Op {
    fn verify(&self, ctx: &Context) -> VerifyResult<()> {
        let mut pending_regions = Vec::new();
        for region in self.regions() {
            pending_regions.push(region);

            while !pending_regions.is_empty() {
                let pending_region = pending_regions.pop().unwrap().deref(&ctx.regions);
                for block in pending_region.layout().iter() {
                    for op in block.deref(&ctx.blocks).layout().iter() {
                        for operand in op.deref(&ctx.ops).as_ref().operands() {
                            let operand_region = operand.deref(&ctx.values).parent_region(ctx);
                            if !region.deref(&ctx.regions).is_ancestor(ctx, operand_region) {
                                // not isolated from above
                                return verify_error!(NotIsolatedFromAboveError).into();
                            }
                        }

                        if !op.deref(&ctx.ops).as_ref().regions().is_empty()
                            && !op.deref(&ctx.ops).impls::<dyn IsIsolatedFromAbove>(ctx)
                        {
                            for sub_region in op.deref(&ctx.ops).as_ref().regions() {
                                pending_regions.push(sub_region);
                            }
                        }
                    }
                }
            }
        }

        Ok(())
    }
}

#[derive(Debug, Error)]
#[error("invalid number of results: expected {0}, got {1}")]
struct InvalidResultNumberError(usize, usize);

/// Verifier `IsIsolatedFromBelow` for `Op`.
///
/// A verifier indicating that the operation has excatly `N` results.
pub trait NumResults<const N: usize>: Op {
    fn verify(&self, _: &Context) -> VerifyResult<()> {
        if self.num_results() != N {
            return verify_error!(InvalidResultNumberError(N, self.num_results())).into();
        }
        Ok(())
    }
}

#[derive(Debug, Error)]
#[error("invalid number of operands: expected {0}, got {1}")]
struct InvalidOperandNumberError(usize, usize);

/// Verifier `NumOperands` for `Op`.
///
/// A trait indicating that the operation has excatly `N` operands.
pub trait NumOperands<const N: usize>: Op {
    fn verify(&self, _: &Context) -> VerifyResult<()> {
        if self.num_operands() != N {
            return verify_error!(InvalidOperandNumberError(N, self.num_operands())).into();
        }
        Ok(())
    }
}

#[derive(Debug, Error)]
#[error("invalid number of regions: expected {0}, got {1}")]
struct InvalidRegionNumberError(usize, usize);

/// Verifier `NumRegions` for `Op`.
///
/// A verifier indicating that the operation has excatly `N` regions.
pub trait NumRegions<const N: usize>: Op {
    fn verify(&self, _: &Context) -> VerifyResult<()> {
        if self.num_regions() != N {
            return verify_error!(InvalidRegionNumberError(N, self.num_regions())).into();
        }
        Ok(())
    }
}

#[derive(Debug, Error)]
#[error("invalid number of successors: expected {0}, got {1}")]
struct InvalidSuccessorNumberError(usize, usize);

/// Verifier `NumSuccessors` for `Op`
///
/// A verifier indicating that the operation has exactly `N` successors.
pub trait NumSuccessors<const N: usize>: Op {
    fn verify(&self, _: &Context) -> VerifyResult<()> {
        if self.num_successors() != N {
            return verify_error!(InvalidSuccessorNumberError(N, self.num_successors())).into();
        }
        Ok(())
    }
}

#[derive(Debug, Error)]
#[error("invalid number of results: expected at least {0}, got {1}")]
struct InvalidAtLeastResultNumberError(usize, usize);

/// Verifier `AtLeastNumResults` for `Op`.
///
/// A verifier indicating that the operation has at least `N` results.
pub trait AtLeastNumResults<const N: usize>: Op {
    fn verify(&self, _: &Context) -> VerifyResult<()> {
        if self.num_results() < N {
            return verify_error!(InvalidAtLeastResultNumberError(N, self.num_results())).into();
        }
        Ok(())
    }
}

#[derive(Debug, Error)]
#[error("invalid number of operands: expected at least {0}, got {1}")]
struct InvalidAtLeastOperandNumberError(usize, usize);

/// Verifier `AtLeastNumOperands` for `Op`.
///
/// A verifier indicating that the operation has at least `N` operands.
pub trait AtLeastNumOperands<const N: usize>: Op {
    fn verify(&self, _: &Context) -> VerifyResult<()> {
        if self.num_operands() < N {
            return verify_error!(InvalidAtLeastOperandNumberError(N, self.num_operands())).into();
        }
        Ok(())
    }
}

#[derive(Debug, Error)]
#[error("invalid number of regions: expected at least {0}, got {1}")]
struct InvalidAtLeastRegionNumberError(usize, usize);

/// Verifier `AtLeastNumRegions` for `Op`.
///
/// A verifier indicating that the operation has at least `N` regions.
pub trait AtLeastNumRegions<const N: usize>: Op {
    fn verify(&self, _: &Context) -> VerifyResult<()> {
        if self.num_regions() < N {
            return verify_error!(InvalidAtLeastRegionNumberError(N, self.num_regions())).into();
        }
        Ok(())
    }
}

#[derive(Debug, Error)]
#[error("invalid number of successors: expected at least {0}, got {1}")]
struct InvalidAtLeastSuccessorNumberError(usize, usize);

/// Verifier `AtLeastNumSuccessors` for `Op`.
///
/// A verifier indicating that the operation has at least `N` successors.
pub trait AtLeastNumSuccessors<const N: usize>: Op {
    fn verify(&self, _: &Context) -> VerifyResult<()> {
        if self.num_successors() < N {
            return verify_error!(InvalidAtLeastSuccessorNumberError(N, self.num_successors()))
                .into();
        }
        Ok(())
    }
}

/// Verifier `AtMostNumResults` for `Op`.
///
/// This verifier indicates that the operation has variadic operands.
pub trait VariadicOperands: Op {
    fn verify(&self, _: &Context) -> VerifyResult<()> { Ok(()) }
}

/// Verifier `VariadicResults` for `Op`.
///
/// This verifier indicates that the operation has variadic results.
pub trait VariadicResults: Op {
    fn verify(&self, _: &Context) -> VerifyResult<()> { Ok(()) }
}

/// Verifier `VariadicRegions` for `Op`.
///
/// This verifier indicates that the operation has variadic regions.
pub trait VariadicRegions: Op {
    fn verify(&self, _: &Context) -> VerifyResult<()> { Ok(()) }
}

/// Verifier `VariadicSuccessors` for `Op`.
///
/// This verifier indicates that the operation has variadic successors.
pub trait VariadicSuccessors: Op {
    fn verify(&self, _: &Context) -> VerifyResult<()> { Ok(()) }
}

/// Verifier `IsTerminator` for `Ty`.
///
/// This verifier indicates that the type is float-like.
pub trait FloatLikeTy: Ty {
    fn verify(&self, _ctx: &Context) -> VerifyResult<()> { Ok(()) }
}

/// Verifier `IsTerminator` for `Ty`.
///
/// This verifier indicates that the type is integer-like.
pub trait IntegerLikeTy: Ty {
    fn verify(&self, _ctx: &Context) -> VerifyResult<()> { Ok(()) }
}

#[derive(Debug, Error)]
#[error("operand is not float-like")]
struct NotFloatLikeError;

/// Verifier `IsTerminator` for `Op`.
///
/// This verifier indicates that the operation has float-like operands.
pub trait FloatLikeOperands: Op {
    fn verify(&self, ctx: &Context) -> VerifyResult<()> {
        for ty in self.operand_tys(ctx) {
            if !ty.deref(&ctx.tys).impls::<dyn FloatLikeTy>(ctx) {
                return verify_error!(NotFloatLikeError).into();
            }
        }
        Ok(())
    }
}

#[derive(Debug, Error)]
#[error("operand is not integer-like")]
struct NotIntegerLikeError;

/// Verifier `IsTerminator` for `Op`.
///
/// This verifier indicates that the operation has integer-like operands.
pub trait IntegerLikeOperands: Op {
    fn verify(&self, ctx: &Context) -> VerifyResult<()> {
        for ty in self.operand_tys(ctx) {
            if !ty.deref(&ctx.tys).impls::<dyn IntegerLikeTy>(ctx) {
                return verify_error!(NotIntegerLikeError).into();
            }
        }
        Ok(())
    }
}

#[derive(Debug, Error)]
#[error("result is not float-like")]
struct NotFloatLikeResultError;

/// Verifier `IsTerminator` for `Op`.
///
/// This verifier indicates that the operation has float-like results.
pub trait FloatLikeResults: Op {
    fn verify(&self, ctx: &Context) -> VerifyResult<()> {
        for ty in self.result_tys(ctx) {
            if !ty.deref(&ctx.tys).impls::<dyn FloatLikeTy>(ctx) {
                return verify_error!(NotFloatLikeResultError).into();
            }
        }
        Ok(())
    }
}

#[derive(Debug, Error)]
#[error("result is not integer-like")]
struct NotIntegerLikeResultError;

/// Verifier `IsTerminator` for `Op`.
///
/// This verifier indicates that the operation has float-like results.
pub trait IntegerLikeResults: Op {
    fn verify(&self, ctx: &Context) -> VerifyResult<()> {
        for ty in self.result_tys(ctx) {
            if !ty.deref(&ctx.tys).impls::<dyn IntegerLikeTy>(ctx) {
                return verify_error!(NotIntegerLikeResultError).into();
            }
        }
        Ok(())
    }
}

#[derive(Debug, Error)]
#[error("operands have different types")]
struct DifferentOperandTypesError;

/// Verifier `SameOperandTys` for `Op`
///
/// This verifier indicates that the operands are all the same types.
pub trait SameOperandTys: Op {
    fn verify(&self, ctx: &Context) -> VerifyResult<()> {
        let operand_tys = self.operand_tys(ctx);

        if operand_tys.is_empty() {
            return Ok(());
        }

        let operand_ty = operand_tys[0];

        for ty in operand_tys {
            if ty != operand_ty {
                return verify_error!(DifferentOperandTypesError).into();
            }
        }

        Ok(())
    }
}

#[derive(Debug, Error)]
#[error("results have different types")]
struct DifferentResultTysError;

/// Verifier `SameResultTys` for `Op`
///
/// This verifier indicates that the results are all the same type.
pub trait SameResultTys: Op {
    fn verify(&self, ctx: &Context) -> VerifyResult<()> {
        let result_tys = self.result_tys(ctx);

        if result_tys.is_empty() {
            return Ok(());
        }

        let result_ty = result_tys[0];
        for ty in result_tys {
            if ty != result_ty {
                return verify_error!(DifferentResultTysError).into();
            }
        }

        Ok(())
    }
}

#[derive(Debug, Error)]
#[error("results and operands have different types")]
struct DifferentOperandAndResultTysError;

/// Verifier `SameOperandAndResultTys` for `Op`.
///
/// This verifier indicates that the results and the operands all share the same
/// type. Note that the numbers of results and operands are not necessarily the
/// same.
pub trait SameOperandAndResultTys: SameOperandTys + SameResultTys {
    fn verify(&self, ctx: &Context) -> VerifyResult<()> {
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
            return verify_error!(DifferentOperandAndResultTysError).into();
        }

        Ok(())
    }
}

#[derive(Debug, Error)]
#[error("results and operands have different numbers")]
struct DifferentOperandAndResultNumberError;

/// Verifier `SameOperandsAndResultsNum` for `Op`.
///
/// This verifier indicates that the numbers of results and operands are the
/// same.
pub trait SameOperandsAndResultsNum: Op {
    fn verify(&self, _: &Context) -> VerifyResult<()> {
        if self.num_operands() != self.num_results() {
            return verify_error!(DifferentOperandAndResultNumberError).into();
        }
        Ok(())
    }
}

#[derive(Debug, Error)]
#[error("invalid operand type, expected {0}")]
pub struct InvalidOperandTyError(String);

pub trait OperandTysAre<T: Ty>: Op {
    fn verify(&self, ctx: &Context) -> VerifyResult<()> {
        for ty in self.operand_tys(ctx) {
            if !ty.deref(&ctx.tys).is_a::<T>() {
                return verify_error!(InvalidOperandTyError(T::mnemonic_static().to_string()))
                    .into();
            }
        }
        Ok(())
    }
}

#[derive(Debug, Error)]
#[error("invalid result type, expected {0}")]
pub struct InvalidResultTyError(String);

pub trait ResultTysAre<T: Ty>: Op {
    fn verify(&self, ctx: &Context) -> VerifyResult<()> {
        for ty in self.result_tys(ctx) {
            if !ty.deref(&ctx.tys).is_a::<T>() {
                return verify_error!(InvalidResultTyError(T::mnemonic_static().to_string()))
                    .into();
            }
        }
        Ok(())
    }
}
