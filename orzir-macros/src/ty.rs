use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, spanned::Spanned, Data, DeriveInput, Fields, LitStr};

pub fn derive_ty(item: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(item as DeriveInput);
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

    let mnemonic = match mnemonic.unwrap().parse_args::<LitStr>() {
        Ok(mnemonic) => mnemonic.value(),
        Err(err) => panic!("failed to parse `mnemonic` attribute: {}", err),
    };

    let (primary, secondary) = mnemonic.split_once('.').unwrap();

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
        }
    };

    result.into()
}
