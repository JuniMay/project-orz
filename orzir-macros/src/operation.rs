use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Data, DeriveInput, Fields, Index, LitStr};

pub fn derive_op(attr: TokenStream, item: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(item as DeriveInput);

    let vis = ast.vis;
    let ident = ast.ident;
    let (field, struct_def) = match ast.data {
        Data::Struct(s) => match s.fields {
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

    let result = quote! {
        #struct_def

        impl ::orzir_core::Op for #ident {
            fn mnemonic(&self, ctx: &::orzir_core::Context) -> ::orzir_core::Mnemonic {
                ::orzir_core::Mnemonic::new(#primary, #secondary)
            }

            fn mnemonic_static(ctx: &::orzir_core::Context) -> ::orzir_core::Mnemonic
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
