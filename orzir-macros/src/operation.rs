use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, spanned::Spanned, Data, DeriveInput, Fields, Index, LitStr};

pub fn derive_op(attr: TokenStream, item: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(item as DeriveInput);

    let vis = ast.vis;
    let ident = ast.ident;
    let (field, struct_def) = match &ast.data {
        Data::Struct(s) => match &s.fields {
            Fields::Named(fields) => {
                let fields = fields.named.iter();
                let def = quote! {
                    #vis struct #ident {
                        base: ::orzir_core::OpBase,
                        #(#fields,)*
                    }
                };
                let field = quote!(base);
                (field, def)
            }
            Fields::Unnamed(fields) => {
                let len = fields.unnamed.len();
                let fields = fields.unnamed.iter();
                let def = quote! {
                    #vis struct #ident (#(#fields,)* ::orzir_core::OpBase);
                };
                let field = Index::from(len);
                let field = quote!(#field);
                (field, def)
            }
            Fields::Unit => {
                let def = quote! {
                    #vis struct #ident(::orzir_core::OpBase);
                };
                let field = Index::from(0);
                let field = quote!(#field);
                (field, def)
            }
        },
        _ => panic!("only structs are supported to derive `Op`"),
    };

    let mnemonic = syn::parse_macro_input!(attr as LitStr).value();
    let (primary, secondary) = mnemonic.split_once('.').unwrap();

    // get the arguments of the `get` constructor
    let new_ctor = match &ast.data {
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
                    fn new(
                        ctx: &mut ::orzir_core::Context,
                        #(#fn_args),*
                    ) -> ::orzir_core::ArenaPtr<::orzir_core::OpObj> {
                        let instance = Self {
                            base: ::orzir_core::OpBase::default(),
                            #(#fn_arg_names),*
                        };
                        let instance = ::orzir_core::OpObj::from(instance);
                        <::orzir_core::Arena<
                            ::orzir_core::OpObj
                        > as ::orzir_core::ArenaBase<
                            ::orzir_core::OpObj
                        >>::alloc(&mut ctx.ops, instance)
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
                    fn new(
                        ctx: &mut ::orzir_core::Context,
                        #(#fn_args),*
                    ) -> ::orzir_core::ArenaPtr<::orzir_core::OpObj> {
                        let instance = Self(#(#fn_arg_names,)* ::orzir_core::OpBase::default());
                        let instance = ::orzir_core::OpObj::from(instance);
                        <::orzir_core::Arena<
                            ::orzir_core::OpObj
                        > as ::orzir_core::ArenaBase<
                            ::orzir_core::OpObj
                        >>::alloc(&mut ctx.ops, instance)
                    }
                }
            }
            Fields::Unit => {
                quote! {
                    fn new(
                        ctx: &mut ::orzir_core::Context
                    ) -> ::orzir_core::ArenaPtr<::orzir_core::OpObj> {
                        let instance = ::orzir_core::OpObj::from(Self(::orzir_core::OpBase::default()));
                        <::orzir_core::Arena<
                            ::orzir_core::OpObj
                        > as ::orzir_core::ArenaBase<
                            ::orzir_core::OpObj
                        >>::alloc(&mut ctx.ops, instance)
                    }
                }
            }
        },
        _ => panic!("only structs are supported to derive `Type`"),
    };

    let result = quote! {
        #struct_def

        impl #ident {
            pub #new_ctor
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
                &self.#field
            }

            fn as_base_mut(&mut self) -> &mut ::orzir_core::OpBase {
                &mut self.#field
            }
        }
    };

    result.into()
}
