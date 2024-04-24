use proc_macro2::TokenStream;
use quote::quote;
use syn::spanned::Spanned;

fn derive_struct_ctor(data_struct: &syn::DataStruct) -> syn::Result<TokenStream> {
    let mut ctor_args = Vec::new();

    let is_unnamed = match &data_struct.fields {
        syn::Fields::Named(_) => false,
        syn::Fields::Unnamed(_) => true,
        syn::Fields::Unit => true,
    };

    for (idx, field) in data_struct.fields.iter().enumerate() {
        let ident = field
            .ident
            .clone()
            .unwrap_or_else(|| syn::Ident::new(&format!("arg_{}", idx), field.span()));

        ctor_args.push((ident, field.ty.clone()));
    }

    let ctor_arg_tokens = ctor_args
        .iter()
        .map(|(ident, ty)| {
            quote! { #ident: #ty }
        })
        .collect::<Vec<_>>();

    let mut ctor_body = TokenStream::new();
    for (ident, _) in ctor_args.iter() {
        ctor_body.extend(quote! { #ident, });
    }

    let ctor_body = if ctor_args.is_empty() {
        if is_unnamed {
            quote! {
                Self
            }
        } else {
            quote! {
                Self {}
            }
        }
    } else if is_unnamed {
        quote! {
            Self(#ctor_body)
        }
    } else {
        quote! {
            Self { #ctor_body }
        }
    };

    let ctor_body = quote! {
        fn get(
            ctx: &mut ::orzir_core::Context,
            #(#ctor_arg_tokens),*
        ) -> ::orzir_core::ArenaPtr<::orzir_core::TyObj> {
            let instance = #ctor_body;
            let obj = ::orzir_core::TyObj::from(instance);
            <::orzir_core::UniqueArena<
                ::orzir_core::TyObj
            > as ::orzir_core::ArenaBase<
                ::orzir_core::TyObj
            >>::alloc(&mut ctx.tys, obj)
        }
    };

    Ok(ctor_body)
}

pub fn derive_impl(ast: &syn::DeriveInput) -> syn::Result<TokenStream> {
    let mut mnemonic = None;
    let mut verifiers = Vec::new();
    let mut interfaces = Vec::new();

    for attr in ast.attrs.iter() {
        if let Some(ident) = attr.path().get_ident() {
            match ident.to_string().as_str() {
                "mnemonic" => {
                    // #[mnemonic = "xxx.xxx"]
                    if let syn::Meta::NameValue(ref meta) = attr.meta {
                        if let syn::Expr::Lit(ref lit) = meta.value {
                            if let syn::Lit::Str(ref lit) = lit.lit {
                                if mnemonic.is_some() {
                                    return Err(syn::Error::new(
                                        lit.span(),
                                        "duplicate mnemonic attribute",
                                    ));
                                }
                                mnemonic = Some(lit.value());
                            }
                        }
                    }
                    if mnemonic.is_none() {
                        return Err(syn::Error::new(attr.span(), "invalid mnemonic attribute"));
                    }
                }
                "verifiers" => {
                    if let syn::Meta::List(ref list) = attr.meta {
                        let paths = list.parse_args_with(
                            syn::punctuated::Punctuated::<syn::Path, syn::Token![,]>::parse_terminated,
                        )?;
                        verifiers.extend(paths);
                    }
                }
                "interfaces" => {
                    if let syn::Meta::List(ref list) = attr.meta {
                        let paths = list.parse_args_with(
                            syn::punctuated::Punctuated::<syn::Path, syn::Token![,]>::parse_terminated,
                        )?;
                        interfaces.extend(paths);
                    }
                }
                _ => {}
            }
        }
    }

    if mnemonic.is_none() {
        return Err(syn::Error::new(
            ast.ident.span(),
            "missing mnemonic attribute",
        ));
    }

    let mnemonic = mnemonic.unwrap();
    let (primary, secondary) = mnemonic.split_once('.').ok_or_else(|| {
        syn::Error::new(
            ast.ident.span(),
            "invalid mnemonic format, expected `<primary>.<secondary>`",
        )
    })?;

    let ctor_body = if let syn::Data::Struct(ref data_struct) = ast.data {
        derive_struct_ctor(data_struct)?
    } else {
        unimplemented!("items other than structs are not supported yet")
    };

    let ident = &ast.ident;

    let interface_register_casters = interfaces
        .iter()
        .map(|path| {
            quote! { ::orzir_macros::register_caster!(ctx, #ident => #path); }
        })
        .collect::<TokenStream>();

    let verifier_register_casters = verifiers
        .iter()
        .map(|path| {
            quote! { ::orzir_macros::register_caster!(ctx, #ident => #path); }
        })
        .collect::<TokenStream>();

    let verifier_impls = verifiers
        .iter()
        .map(|path| {
            quote! { impl #path for #ident {} }
        })
        .collect::<TokenStream>();

    let verifier_calls = verifiers
        .iter()
        .map(|path| {
            quote! { <Self as #path>::verify(self, ctx)?; }
        })
        .collect::<TokenStream>();

    let output = quote! {
        impl #ident {
            pub #ctor_body
        }

        impl ::orzir_core::Ty for #ident {
            fn mnemonic(&self) -> ::orzir_core::Mnemonic {
                ::orzir_core::Mnemonic::new(#primary, #secondary)
            }

            fn mnemonic_static() -> ::orzir_core::Mnemonic {
                ::orzir_core::Mnemonic::new(#primary, #secondary)
            }

            fn eq(&self, other: &dyn ::orzir_core::Ty) -> bool {
                if let Some(other) = other.downcast_ref::<Self>() {
                    self == other
                } else {
                    false
                }
            }

            fn register(ctx: &mut ::orzir_core::Context, parse_fn: ::orzir_core::TyParseFn)
            where
                Self: Sized
            {
                let mnemonic = Self::mnemonic_static();
                ctx.dialects.get_mut(mnemonic.primary()).unwrap().add_ty(mnemonic, parse_fn);

                #interface_register_casters
                #verifier_register_casters
            }

        }

        #verifier_impls

        impl ::orzir_core::RunVerifiers for #ident {
            fn run_verifiers(&self, ctx: &::orzir_core::Context) -> ::orzir_core::VerifyResult<()> {
                #verifier_calls
                Ok(())
            }
        }
    };

    Ok(output)
}

#[cfg(test)]
mod tests {
    use quote::quote;

    use crate::ty::derive_impl;

    #[test]
    fn test_0() {
        let src = quote! {
            #[mnemonic = "builtin.float"]
            #[verifiers(FloatLikeTy)]
            pub struct FloatTy;
        };

        let ast = syn::parse2::<syn::DeriveInput>(src).unwrap();
        let output = derive_impl(&ast).unwrap();
        println!("{}", output);
        let ast = syn::parse_file(&output.to_string()).unwrap();
        let ast = prettyplease::unparse(&ast);
        println!("{}", ast);
    }
}
