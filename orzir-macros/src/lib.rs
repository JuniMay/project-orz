use proc_macro::TokenStream;
use ty::derive_ty;

use crate::operation::derive_op;

mod operation;
mod ty;

/// Implement a [Op](orzir_core::Op) for the given struct.
#[proc_macro_attribute]
pub fn op(attr: TokenStream, item: TokenStream) -> TokenStream { derive_op(attr, item) }

/// Implement a [Type](orzir_core::Type) for the given struct.
#[proc_macro_attribute]
pub fn ty(attr: TokenStream, item: TokenStream) -> TokenStream { derive_ty(attr, item) }
