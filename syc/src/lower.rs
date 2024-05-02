/// Lowering the AST into the std dialects(`arith`, `builtin`, `cf`, `func`,
/// `mem`)
///
/// TODO: This needs to be implemented.
/// 

use orzir_core::{ArenaPtr, Context, OpObj};

use crate::ast::CompUnit;

/// Convert the ast into a `builtin.module` operation with a given context.
pub fn lower(ast: &CompUnit, ctx: &mut Context) -> ArenaPtr<OpObj> { todo!() }
