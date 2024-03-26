use proc_macro2::TokenStream;
use quote::quote;
use syn::{punctuated::Punctuated, Data, DeriveInput, Expr, Fields, Lit, Meta, Path};

pub fn derive_op(item: TokenStream) -> syn::Result<TokenStream> {
    let ast = syn::parse2::<DeriveInput>(item)?;

    let ident = ast.ident;

    let (ctor, base_field) = match &ast.data {
        Data::Struct(s) => match &s.fields {
            Fields::Named(fields) => {
                let mut base_field = None;
                for field in fields.named.iter() {
                    for attr in field.attrs.iter() {
                        if attr.path().is_ident("base") {
                            base_field = Some(field.ident.clone().unwrap());
                            break;
                        }
                    }
                }

                if base_field.is_none() {
                    panic!("no field for `OpBase` member.")
                }

                let base_field = base_field.unwrap();

                let fn_args = fields
                    .named
                    .iter()
                    .filter(|field| field.ident.as_ref().unwrap() != &base_field)
                    .map(|field| {
                        let ident = field.ident.clone().unwrap();
                        let ty = field.ty.clone();
                        quote! {
                            #ident: #ty
                        }
                    })
                    .collect::<Vec<_>>();

                let fn_arg_names = fields
                    .named
                    .iter()
                    .filter(|field| field.ident.as_ref().unwrap() != &base_field)
                    .map(|field| field.ident.clone().unwrap());

                let ctor = quote! {
                    fn new(
                        ctx: &mut ::orzir_core::Context,
                        #(#fn_args),*
                    ) -> ::orzir_core::ArenaPtr<::orzir_core::OpObj> {
                        let instance = Self {
                            #base_field: ::orzir_core::OpBase::default(),
                            #(#fn_arg_names),*
                        };
                        let instance = ::orzir_core::OpObj::from(instance);
                        <::orzir_core::Arena<
                            ::orzir_core::OpObj
                        > as ::orzir_core::ArenaBase<
                            ::orzir_core::OpObj
                        >>::alloc(&mut ctx.ops, instance)
                    }
                };

                let base_field = quote! {
                    #base_field
                };

                (ctor, base_field)
            }
            Fields::Unnamed(_) => {
                panic!("unnamed fields are not supported.")
            }
            Fields::Unit => {
                panic!("no field for `OpBase` member.")
            }
        },
        _ => panic!("only structs are supported to derive `Op`"),
    };

    let mnemonic = ast.attrs.iter().find(|attr| attr.path().is_ident("mnemonic"));

    if mnemonic.is_none() {
        panic!("no mnemonic specified.")
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
            pub #ctor
        }

        impl ::orzir_core::Op for #ident {
            fn mnemonic(&self) -> ::orzir_core::Mnemonic {
                ::orzir_core::Mnemonic::new(#primary, #secondary)
            }

            fn mnemonic_static() -> ::orzir_core::Mnemonic
            where
                Self: Sized
            {
                ::orzir_core::Mnemonic::new(#primary, #secondary)
            }

            fn as_base(&self) -> &::orzir_core::OpBase {
                &self.#base_field
            }

            fn as_base_mut(&mut self) -> &mut ::orzir_core::OpBase {
                &mut self.#base_field
            }

            fn register(ctx: &mut ::orzir_core::Context, parse_fn: ::orzir_core::OpParseFn)
            where
                Self: Sized
            {
                let mnemonic = Self::mnemonic_static();
                ctx.dialects.get_mut(mnemonic.primary()).unwrap().add_op(mnemonic, parse_fn);

                #(#interfaces)*
                #(#verifier_register_casters)*
            }
        }

        #verifier_calls
    };

    Ok(result)
}
