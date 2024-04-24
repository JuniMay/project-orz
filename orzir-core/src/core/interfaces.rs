/// Builtin interfaces.
///
/// This module provides builtin interfaces for regions, values, successors.
///
/// These interfaces can be derived with the macro and are mandatory for all
/// operations.
use crate::{ArenaPtr, Context, Region, RegionKind, Successor, TyObj, Typed, Value};

/// Builtin region interface.
///
/// This trait provides methods to interact with regions. This is set to be a
/// mandatory interface for all operations for performance reasons.
pub trait RegionInterface {
    /// Get the number of regions.
    fn num_regions(&self) -> usize;

    /// Get the region at the given index.
    fn get_region(&self, index: usize) -> Option<ArenaPtr<Region>>;

    /// Set the region at the given index and return the old region (if any).
    fn set_region(&mut self, index: usize, region: ArenaPtr<Region>) -> Option<ArenaPtr<Region>>;

    /// Get all regions.
    fn regions(&self) -> Vec<ArenaPtr<Region>> {
        (0..self.num_regions())
            .filter_map(|index| self.get_region(index))
            .collect()
    }

    /// Get the region kind at the given index.
    fn get_region_kind(&self, ctx: &Context, index: usize) -> RegionKind {
        self.get_region(index).unwrap().deref(&ctx.regions).kind()
    }

    /// Check if the region has SSA dominance.
    fn has_ssa_dominance(&self, ctx: &Context, index: usize) -> bool {
        self.get_region_kind(ctx, index) == RegionKind::SsaCfg
    }
}

/// Builtin value interface.
///
/// This trait provides methods to interact with values. This is set to be a
/// mandatory interface for all operations for performance reasons.
pub trait DataFlow {
    /// Get the number of operands.
    ///
    /// This is also the number of uses of the operation.
    fn num_operands(&self) -> usize;

    /// Get the number of results.
    ///
    /// This is also the number of definitions of the operation.
    fn num_results(&self) -> usize;

    /// Get the operand at the given index.
    fn get_operand(&self, index: usize) -> Option<ArenaPtr<Value>>;

    /// Get the result at the given index.
    fn get_result(&self, index: usize) -> Option<ArenaPtr<Value>>;

    /// Set the operand at the given index and return the old operand (if any).
    fn set_operand(&mut self, index: usize, operand: ArenaPtr<Value>) -> Option<ArenaPtr<Value>>;

    /// Set the result at the given index and return the old result (if any).
    fn set_result(&mut self, index: usize, result: ArenaPtr<Value>) -> Option<ArenaPtr<Value>>;

    /// Get all operands.
    fn operands(&self) -> Vec<ArenaPtr<Value>> {
        (0..self.num_operands())
            .filter_map(|index| self.get_operand(index))
            .collect()
    }

    /// Get all results.
    fn results(&self) -> Vec<ArenaPtr<Value>> {
        (0..self.num_results())
            .filter_map(|index| self.get_result(index))
            .collect()
    }

    /// Get all operand types.
    fn operand_tys(&self, ctx: &Context) -> Vec<ArenaPtr<TyObj>> {
        self.operands()
            .iter()
            .map(|operand| operand.deref(&ctx.values).ty(ctx))
            .collect()
    }

    /// Get all result types.
    fn result_tys(&self, ctx: &Context) -> Vec<ArenaPtr<TyObj>> {
        self.results()
            .iter()
            .map(|result| result.deref(&ctx.values).ty(ctx))
            .collect()
    }
}

/// Builtin type interface.
///
/// This trait provides methods to interact with types. This is set to be a
/// mandatory interface for all operations for performance reasons.
pub trait ControlFlow {
    /// Get the number of successors.
    fn num_successors(&self) -> usize;

    /// Get the successor at the given index.
    fn get_successor(&self, index: usize) -> Option<&Successor>;

    /// Set the successor at the given index and return the old successor (if
    /// any).
    fn set_successor(&mut self, index: usize, successor: Successor) -> Option<Successor>;

    /// Get all successors.
    fn successors(&self) -> Vec<&Successor> {
        (0..self.num_successors())
            .filter_map(|index| self.get_successor(index))
            .collect()
    }
}
