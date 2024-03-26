use proc_macro2::TokenStream;
use quote::quote;

/// A cast info for [`caster`](super::caster) proc-macro.
struct CastInfo {
    from: syn::Type,
    to: syn::Path,
}

impl syn::parse::Parse for CastInfo {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let from = input.parse()?;
        input.parse::<syn::Token![=>]>()?;
        let to = input.parse()?;
        Ok(Self { from, to })
    }
}

pub fn caster_impl(input: TokenStream) -> syn::Result<TokenStream> {
    let CastInfo { from, to } = syn::parse2(input)?;

    let result = quote! {
        ::orzir_core::Caster::<dyn #to>::new(
            |any| any.downcast_ref::<#from>().unwrap() as &dyn #to,
            |any| any.downcast_mut::<#from>().unwrap() as &mut dyn #to,
        )
    };

    Ok(result)
}

struct CastRegisterInfo {
    ctx: syn::Ident,
    from: syn::Type,
    to: syn::Path,
}

impl syn::parse::Parse for CastRegisterInfo {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let ctx = input.parse()?;
        input.parse::<syn::Token![,]>()?;
        let from = input.parse()?;
        input.parse::<syn::Token![=>]>()?;
        let to = input.parse()?;
        Ok(Self { ctx, from, to })
    }
}

pub fn register_caster_impl(input: TokenStream) -> syn::Result<TokenStream> {
    let CastRegisterInfo { ctx, from, to } = syn::parse2(input)?;

    let result = quote! {
        #ctx.casters.register::<#from, dyn #to>(
            ::orzir_core::Caster::<dyn #to>::new(
                |any| any.downcast_ref::<#from>().unwrap() as &dyn #to,
                |any| any.downcast_mut::<#from>().unwrap() as &mut dyn #to,
            )
        )
    };

    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_caster_impl() {
        let input = quote! { ModuleOp => IsIsolatedFromAbove };
        let result = caster_impl(input);
        let expected = quote! {
            ::orzir_core::Caster::<dyn IsIsolatedFromAbove>::new(
                |any| any.downcast_ref::<ModuleOp>().unwrap() as &dyn IsIsolatedFromAbove,
                |any| any.downcast_mut::<ModuleOp>().unwrap() as &mut dyn IsIsolatedFromAbove,
            )
        };
        assert_eq!(result.unwrap().to_string(), expected.to_string());
    }

    #[test]
    fn test_register_caster_impl() {
        let input = quote! { ctx, ModuleOp => IsIsolatedFromAbove };
        let result = register_caster_impl(input);
        let expected = quote! {
            ctx.casters.register::<ModuleOp, dyn IsIsolatedFromAbove>(
                ::orzir_core::Caster::<dyn IsIsolatedFromAbove>::new(
                    |any| any.downcast_ref::<ModuleOp>().unwrap() as &dyn IsIsolatedFromAbove,
                    |any| any.downcast_mut::<ModuleOp>().unwrap() as &mut dyn IsIsolatedFromAbove,
                )
            )
        };
        assert_eq!(result.unwrap().to_string(), expected.to_string());
    }
}
