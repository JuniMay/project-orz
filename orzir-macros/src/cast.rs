use proc_macro::TokenStream;
use quote::{quote, ToTokens};

fn caster(from: &impl ToTokens, to: &impl ToTokens) -> TokenStream {
    let result = quote! {
        ::orzir_core::Caster::<dyn #to> {
            cast_ref: |any| any.downcast_ref::<#from>().unwrap() as &dyn #to,
            cast_mut: |any| any.downcast_mut::<#from>().unwrap() as &mut dyn #to,
        }
    };
    result.into()
}
