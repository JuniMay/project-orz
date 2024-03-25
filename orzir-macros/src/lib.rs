use proc_macro::TokenStream;
use ty::derive_ty;

use crate::operation::derive_op;

mod operation;
mod ty;

/// Implement a [Op](orzir_core::Op) for the given struct.
#[proc_macro_derive(Op, attributes(mnemonic, base))]
pub fn op(item: TokenStream) -> TokenStream { derive_op(item) }

/// Implement a [Type](orzir_core::Type) for the given struct.
#[proc_macro_derive(Type, attributes(mnemonic))]
pub fn ty(item: TokenStream) -> TokenStream { derive_ty(item) }
