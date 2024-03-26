use proc_macro2::TokenStream;
use quote::quote;
use syn::{
    punctuated::Punctuated, spanned::Spanned, Data, DeriveInput, Expr, Fields, Lit, Meta, Path,
};

pub fn derive_ty(item: TokenStream) -> syn::Result<TokenStream> {
    let ast = syn::parse2::<DeriveInput>(item)?;
    let ident = ast.ident.clone();

    // get the arguments of the `get` constructor
    let get_ctor = match &ast.data {
        Data::Struct(s) => match &s.fields {
            Fields::Named(fields) => {
                let fn_args = fields
                    .named
                    .iter()
                    .map(|field| {
                        let ident = field.ident.clone().unwrap();
                        let ty = field.ty.clone();
                        quote! {
                            #ident: #ty
                        }
                    })
                    .collect::<Vec<_>>();
                let fn_arg_names = fields.named.iter().map(|field| field.ident.clone().unwrap());
                quote! {
                    fn get(
                        ctx: &mut ::orzir_core::Context,
                        #(#fn_args),*
                    ) -> ::orzir_core::ArenaPtr<::orzir_core::TypeObj> {
                        let instance = Self {
                            #(#fn_arg_names),*
                        };
                        let instance = ::orzir_core::TypeObj::from(instance);
                        <::orzir_core::UniqueArena<
                            ::orzir_core::TypeObj
                        > as ::orzir_core::ArenaBase<
                            ::orzir_core::TypeObj
                        >>::alloc(&mut ctx.types, instance)
                    }
                }
            }
            Fields::Unnamed(fields) => {
                let fn_args = fields
                    .unnamed
                    .iter()
                    .enumerate()
                    .map(|(i, field)| {
                        let ident = syn::Ident::new(&format!("arg_{}", i), field.span());
                        let ty = field.ty.clone();
                        quote! {
                            #ident: #ty
                        }
                    })
                    .collect::<Vec<_>>();
                let fn_arg_names = (0..fields.unnamed.len())
                    .map(|i| syn::Ident::new(&format!("arg_{}", i), ident.span()));
                quote! {
                    fn get(
                        ctx: &mut ::orzir_core::Context,
                        #(#fn_args),*
                    ) -> ::orzir_core::ArenaPtr<::orzir_core::TypeObj> {
                        let instance = Self(#(#fn_arg_names),*);
                        let instance = ::orzir_core::TypeObj::from(instance);
                        <::orzir_core::UniqueArena<
                            ::orzir_core::TypeObj
                        > as ::orzir_core::ArenaBase<
                            ::orzir_core::TypeObj
                        >>::alloc(&mut ctx.types, instance)
                    }
                }
            }
            Fields::Unit => {
                quote! {
                    fn get(
                        ctx: &mut ::orzir_core::Context
                    ) -> ::orzir_core::ArenaPtr<::orzir_core::TypeObj> {
                        let instance = ::orzir_core::TypeObj::from(Self);
                        <::orzir_core::UniqueArena<
                            ::orzir_core::TypeObj
                        > as ::orzir_core::ArenaBase<
                            ::orzir_core::TypeObj
                        >>::alloc(&mut ctx.types, instance)
                    }
                }
            }
        },
        _ => panic!("only structs are supported to derive `Type`"),
    };

    let mnemonic = ast.attrs.iter().find(|attr| attr.path().is_ident("mnemonic"));

    if mnemonic.is_none() {
        panic!("`mnemonic` attribute is required to derive `Type`");
    }

    // parse as `mnemonic = "xxxx.xxx"`, which is a name-value style attribute.
    let mnemonic = if let Meta::NameValue(ref meta) = mnemonic.unwrap().meta {
        if let Expr::Lit(lit) = &meta.value {
            if let Lit::Str(lit) = &lit.lit {
                lit.value()
            } else {
                panic!("mnemonic must be a string literal.")
            }
        } else {
            panic!("mnemonic must be a string literal.")
        }
    } else {
        panic!("mnemonic must be specified using a key-value style attribute.")
    };
    let (primary, secondary) = mnemonic.split_once('.').unwrap();

    // generate the register_caster calls for the interfaces
    let interfaces = ast.attrs.iter().find(|attr| attr.path().is_ident("interfaces"));
    let interfaces = if let Some(interfaces) = interfaces {
        if let Meta::List(list) = &interfaces.meta {
            let paths =
                list.parse_args_with(Punctuated::<Path, syn::Token![,]>::parse_terminated)?;
            // iter to generate the register_caster macro calls
            let register_caster_calls = paths.into_iter().map(|path| {
                quote! {
                    ::orzir_macros::register_caster!(ctx, #ident => #path);
                }
            });
            register_caster_calls.collect::<Vec<_>>()
        } else {
            panic!("expect list inside the `interfaces` attribute");
        }
    } else {
        Vec::new()
    };

    let verifiers = ast.attrs.iter().find(|attr| attr.path().is_ident("verifiers"));
    // generate the register_caster calls for the verifiers
    let verifier_register_casters = if let Some(verifiers) = verifiers {
        if let Meta::List(list) = &verifiers.meta {
            let paths =
                list.parse_args_with(Punctuated::<Path, syn::Token![,]>::parse_terminated)?;
            // iter to generate the register_caster macro calls
            let register_caster_calls = paths.into_iter().map(|path| {
                quote! {
                    ::orzir_macros::register_caster!(ctx, #ident => #path);
                }
            });
            register_caster_calls.collect::<Vec<_>>()
        } else {
            panic!("expect list inside the `verifiers` attribute");
        }
    } else {
        Vec::new()
    };
    // call the verifier to implement
    // [`VerifyInterfaces`](orzir_core::VerifyInterfaces) trait.
    let verifier_calls = if let Some(verifiers) = verifiers {
        if let Meta::List(list) = &verifiers.meta {
            let paths =
                list.parse_args_with(Punctuated::<Path, syn::Token![,]>::parse_terminated)?;
            // iter to generate the register_caster macro calls
            let calls = paths.into_iter().map(|path| {
                quote! {
                    <Self as #path>::verify(self, ctx)?;
                }
            });
            calls.collect::<Vec<_>>()
        } else {
            panic!("expect list inside the `verifiers` attribute");
        }
    } else {
        Vec::new()
    };

    let verifier_calls = quote! {
        impl ::orzir_core::VerifyInterfaces for #ident {
            fn verify_interfaces(&self, ctx: &::orzir_core::Context) -> ::anyhow::Result<()> {
                #(#verifier_calls)*
                Ok(())
            }
        }
    };

    let result = quote! {
        impl #ident {
            pub #get_ctor
        }

        impl ::orzir_core::Type for #ident {
            fn mnemonic(&self) -> ::orzir_core::Mnemonic {
                ::orzir_core::Mnemonic::new(#primary, #secondary)
            }

            fn mnemonic_static() -> ::orzir_core::Mnemonic
            where
                Self: Sized
            {
                ::orzir_core::Mnemonic::new(#primary, #secondary)
            }

            fn eq(&self, other: &dyn ::orzir_core::Type) -> bool {
                if let Some(other) = other.downcast_ref::<Self>() {
                    self == other
                } else {
                    false
                }
            }

            fn register(ctx: &mut ::orzir_core::Context, parse_fn: ::orzir_core::TypeParseFn)
            where
                Self: Sized
            {
                let mnemonic = Self::mnemonic_static();
                ctx.dialects.get_mut(mnemonic.primary()).unwrap().add_type(mnemonic, parse_fn);

                #(#interfaces)*
                #(#verifier_register_casters)*
            }
        }

        #verifier_calls
    };

    Ok(result)
}
