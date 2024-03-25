use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Data, DeriveInput, Fields, LitStr};

pub fn derive_op(item: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(item as DeriveInput);

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

    let mnemonic = match mnemonic.unwrap().parse_args::<LitStr>() {
        Ok(mnemonic) => mnemonic.value(),
        Err(_) => panic!("mnemonic must be a string literal."),
    };

    let (primary, secondary) = mnemonic.split_once('.').unwrap();

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
        }
    };

    result.into()
}
