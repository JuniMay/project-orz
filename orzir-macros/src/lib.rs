use cast::{caster_impl, register_caster_impl};
use proc_macro::TokenStream;
use ty::derive_ty;

use crate::operation::derive_op;

mod cast;
mod operation;
mod ty;

/// Implement a [Op](orzir_core::Op) for the given struct.
#[proc_macro_derive(Op, attributes(mnemonic, base, verifiers, interfaces))]
pub fn op(item: TokenStream) -> TokenStream { derive_op(item.into()).unwrap().into() }

/// Implement a [Type](orzir_core::Type) for the given struct.
#[proc_macro_derive(Type, attributes(mnemonic, verifiers, interfaces))]
pub fn ty(item: TokenStream) -> TokenStream { derive_ty(item.into()).unwrap().into() }

/// Create a caster for casting from one type to another.
#[proc_macro]
pub fn caster(input: TokenStream) -> TokenStream { caster_impl(input.into()).unwrap().into() }

/// Register a trait object caster in the context.
///
/// This is used if the interface/trait is not defined in the same crate as the
/// operation/type.
#[proc_macro]
pub fn register_caster(input: TokenStream) -> TokenStream {
    register_caster_impl(input.into()).unwrap().into()
}
