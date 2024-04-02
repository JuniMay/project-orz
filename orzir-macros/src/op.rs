use proc_macro2::TokenStream;
use quote::quote;
use syn::spanned::Spanned;

#[derive(Debug, Clone, Copy)]
pub enum IndexKind {
    /// The `...` notation.
    All,
    /// A single index number.
    Single(usize),
}

impl syn::parse::Parse for IndexKind {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        if input.peek(syn::Token![...]) {
            input.parse::<syn::Token![...]>()?;
            Ok(Self::All)
        } else {
            let index = input.parse::<syn::LitInt>()?.base10_parse::<usize>()?;
            Ok(Self::Single(index))
        }
    }
}

pub struct RegionMeta {
    pub index: IndexKind,
    pub kind: Option<syn::Path>,
}

impl syn::parse::Parse for RegionMeta {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let index = input.parse::<IndexKind>()?;

        while !input.is_empty() {
            input.parse::<syn::Token![,]>()?;
            let key: syn::Ident = input.parse()?;
            input.parse::<syn::Token![=]>()?;
            let value: syn::Path = input.parse()?;
            if key == "kind" {
                return Ok(Self {
                    index,
                    kind: Some(value),
                });
            }
        }

        Ok(Self { index, kind: None })
    }
}


fn derive_struct_ctor_metadata(
    data_struct: &syn::DataStruct,
) -> syn::Result<(TokenStream, TokenStream)> {
    let mut ctor_args = Vec::new();
    let mut metadata_ident = None;
    let mut metadata_idx = None;

    let is_unnamed = match &data_struct.fields {
        syn::Fields::Named(_) => false,
        syn::Fields::Unnamed(_) => true,
        syn::Fields::Unit => unimplemented!("cannot derive for unit structs"),
    };

    for (idx, field) in data_struct.fields.iter().enumerate() {
        let attr = &field.attrs;

        let metadata_attr = attr.iter().find(|attr| attr.path().is_ident("metadata"));

        if let Some(metadata_attr) = metadata_attr {
            if metadata_ident.is_some() {
                return Err(syn::Error::new(
                    metadata_attr.span(),
                    "duplicate metadata attribute",
                ));
            }

            metadata_ident = Some(
                field
                    .ident
                    .clone()
                    .unwrap_or_else(|| syn::Ident::new(&format!("arg_{}", idx), field.span())),
            );

            metadata_idx = Some(idx);

            ctor_args.push((metadata_ident.as_ref().unwrap().clone(), field.ty.clone()));
        } else {
            let ident = field
                .ident
                .clone()
                .unwrap_or_else(|| syn::Ident::new(&format!("arg_{}", idx), field.span()));

            ctor_args.push((ident, field.ty.clone()));
        }
    }

    if metadata_ident.is_none() {
        return Err(syn::Error::new(
            data_struct.fields.span(),
            "missing metadata attribute",
        ));
    }

    let metadata_ident = metadata_ident.unwrap();
    let ctor_arg_tokens = ctor_args
        .iter()
        .filter(|(ident, _)| ident != &metadata_ident)
        .map(|(ident, ty)| {
            quote! { #ident: #ty }
        });

    let mut ctor_body = TokenStream::new();
    for (ident, _) in ctor_args.iter() {
        if ident == &metadata_ident {
            if is_unnamed {
                ctor_body.extend(quote! {
                    ::orzir_core::OpMetadata::new(self_ptr),
                });
            } else {
                ctor_body.extend(quote! {
                    #ident: ::orzir_core::OpMetadata::new(self_ptr),
                });
            }
        } else {
            ctor_body.extend(quote! {
                #ident,
            });
        }
    }

    let ctor_body = if is_unnamed {
        quote! {
            Self(#ctor_body)
        }
    } else {
        quote! {
            Self { #ctor_body }
        }
    };

    let ctor_body = quote! {
        fn new(
            ctx: &mut ::orzir_core::Context,
            self_ptr: ::orzir_core::ArenaPtr<::orzir_core::OpObj>,
            #(#ctor_arg_tokens),*
        ) -> ::orzir_core::ArenaPtr<::orzir_core::OpObj> {
            let instance = #ctor_body;
            let obj = ::orzir_core::OpObj::from(instance);
            ctx.ops.fill(self_ptr, obj);
            self_ptr
        }
    };

    let metadata_field = if is_unnamed {
        let index = syn::Index::from(metadata_idx.unwrap());
        quote! { self.#index }
    } else {
        quote! { self.#metadata_ident }
    };

    let metadata_body = quote! {
        fn metadata(&self) -> &::orzir_core::OpMetadata {
            &#metadata_field
        }

        fn metadata_mut(&mut self) -> &mut ::orzir_core::OpMetadata {
            &mut #metadata_field
        }
    };

    Ok((ctor_body, metadata_body))
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

    let (ctor_body, metadata_body) = if let syn::Data::Struct(ref data_struct) = ast.data {
        derive_struct_ctor_metadata(data_struct)?
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

        impl ::orzir_core::Op for #ident {
            fn mnemonic(&self) -> ::orzir_core::Mnemonic {
                ::orzir_core::Mnemonic::new(#primary, #secondary)
            }

            fn mnemonic_static() -> ::orzir_core::Mnemonic {
                ::orzir_core::Mnemonic::new(#primary, #secondary)
            }

            fn register(ctx: &mut ::orzir_core::Context, parse_fn: ::orzir_core::OpParseFn)
            where
                Self: Sized
            {
                let mnemonic = Self::mnemonic_static();
                ctx.dialects.get_mut(mnemonic.primary()).unwrap().add_op(mnemonic, parse_fn);

                #interface_register_casters
                #verifier_register_casters
            }

            #metadata_body
        }

        #verifier_impls

        impl ::orzir_core::RunVerifiers for #ident {
            fn run_verifiers(&self, ctx: &::orzir_core::Context) -> ::orzir_core::VerificationResult<()> {
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

    use crate::op::derive_impl;

    #[test]
    fn test_0() {
        let src = quote! {
            #[mnemonic = "macro.test"]
            #[verifiers(NumResults<0>, VariadicOperands, NumRegions<0>, IsTerminator)]
            #[interfaces(SomeInterface)]
            pub struct TestOp(#[operand(...)] Vec<ArenaPtr<Value>>, #[metadata] OpMetadata);
        };

        let ast = syn::parse2::<syn::DeriveInput>(src).unwrap();
        let output = derive_impl(&ast).unwrap();
        println!("{}", output);
        let ast = syn::parse_file(&output.to_string()).unwrap();
        let ast = prettyplease::unparse(&ast);
        println!("{}", ast);
    }
}
