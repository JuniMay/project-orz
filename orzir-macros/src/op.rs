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

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum FieldIdent {
    Ident(String),
    Index(usize),
}

pub enum OpFieldMeta {
    Metadata,
    Region(RegionMeta),
    Operand(IndexKind),
    Result(IndexKind),
    Successor(IndexKind),
    Other { is_vec: bool, ty: syn::Type },
}

pub struct OpDeriveInfo {
    pub is_named: bool,
    /// The mnemonic of the operation.
    pub mnemonic: (String, String),
    /// The verifiers that the operation implements.
    pub verifiers: Vec<syn::Path>,
    /// The interfaces that the operation implements.
    pub interfaces: Vec<syn::Path>,
    /// The fields in the struct.
    ///
    /// This follows the order of the fields in the struct.
    pub fields: Vec<(FieldIdent, OpFieldMeta)>,
}

pub fn is_type_vec(ty: &syn::Type) -> Option<syn::Type> {
    if let syn::Type::Path(ref path) = ty {
        let segment = path.path.segments.iter().next().unwrap();
        if segment.ident == "Vec" {
            if let syn::PathArguments::AngleBracketed(ref args) =
                path.path.segments.last().unwrap().arguments
            {
                if let syn::GenericArgument::Type(ref ty) = args.args.first().unwrap() {
                    return Some(ty.clone());
                }
            }
        }
    }
    None
}

impl OpDeriveInfo {
    pub fn from_ast(ast: &syn::DeriveInput) -> syn::Result<Self> {
        let mut mnemonic = None;
        let mut verifiers = Vec::new();
        let mut interfaces = Vec::new();

        for attr in ast.attrs.iter() {
            if let Some(ident) = attr.path().get_ident() {
                match ident.to_string().as_str() {
                    "mnemonic" => {
                        if let syn::Meta::NameValue(ref meta) = attr.meta {
                            if let syn::Expr::Lit(ref lit) = meta.value {
                                if let syn::Lit::Str(ref lit) = lit.lit {
                                    if mnemonic.is_some() {
                                        return Err(syn::Error::new(
                                            lit.span(),
                                            "duplicate mnemonic attribute",
                                        ));
                                    }
                                    let val = lit.value();
                                    let val = val.split_once('.').ok_or_else(|| {
                                        syn::Error::new(
                                            lit.span(),
                                            "invalid mnemonic format, expected `<primary>.<secondary>`",
                                        )
                                    })?;
                                    mnemonic = Some((val.0.to_string(), val.1.to_string()));
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

        let mut fields = Vec::new();

        let is_named;

        if let syn::Data::Struct(ref data_struct) = ast.data {
            is_named = matches!(data_struct.fields, syn::Fields::Named(_));

            for (idx, field) in data_struct.fields.iter().enumerate() {
                let field_ident = match &field.ident {
                    Some(ident) => FieldIdent::Ident(ident.to_string()),
                    None => FieldIdent::Index(idx),
                };

                let mut has_attr = false;

                for attr in field.attrs.iter() {
                    if let Some(ident) = attr.path().get_ident() {
                        if let ident
                        @ ("metadata" | "region" | "operand" | "result" | "successor") =
                            ident.to_string().as_str()
                        {
                            if has_attr {
                                return Err(syn::Error::new(
                                    ident.span(),
                                    "duplicate field attribute",
                                ));
                            }

                            match ident {
                                "metadata" => {
                                    fields.push((field_ident.clone(), OpFieldMeta::Metadata));
                                }
                                "region" => {
                                    let meta = attr.parse_args::<RegionMeta>()?;
                                    fields.push((field_ident.clone(), OpFieldMeta::Region(meta)));
                                }
                                "operand" => {
                                    let index = attr.parse_args::<IndexKind>()?;
                                    fields.push((field_ident.clone(), OpFieldMeta::Operand(index)));
                                }
                                "result" => {
                                    let index = attr.parse_args::<IndexKind>()?;
                                    fields.push((field_ident.clone(), OpFieldMeta::Result(index)));
                                }
                                "successor" => {
                                    let index = attr.parse_args::<IndexKind>()?;
                                    fields
                                        .push((field_ident.clone(), OpFieldMeta::Successor(index)));
                                }
                                _ => unreachable!(),
                            }

                            has_attr = true;
                        }
                    }
                }

                if !has_attr {
                    let ty = field.ty.clone();
                    if let Some(ty) = is_type_vec(&ty) {
                        fields.push((field_ident, OpFieldMeta::Other { is_vec: true, ty }));
                    } else {
                        fields.push((
                            field_ident,
                            OpFieldMeta::Other {
                                is_vec: false,
                                ty: field.ty.clone(),
                            },
                        ));
                    }
                }
            }
        } else {
            unimplemented!("items other than structs are not supported yet")
        }

        Ok(Self {
            is_named,
            mnemonic,
            verifiers,
            interfaces,
            fields,
        })
    }
}

fn derive_struct_ctor(derive_info: &OpDeriveInfo) -> syn::Result<TokenStream> {
    let ctor_args = derive_info
        .fields
        .iter()
        .filter(|(_, meta)| !matches!(meta, OpFieldMeta::Metadata))
        .map(|(ident, meta)| {
            let ident = match ident {
                FieldIdent::Ident(ident) => syn::Ident::new(ident, proc_macro2::Span::call_site()),
                FieldIdent::Index(idx) => {
                    syn::Ident::new(&format!("arg_{}", idx), proc_macro2::Span::call_site())
                }
            };
            match meta {
                OpFieldMeta::Metadata => unreachable!(),
                OpFieldMeta::Operand(index) => match index {
                    IndexKind::All => {
                        quote! { #ident: Vec<::orzir_core::ArenaPtr<::orzir_core::Value>>, }
                    }
                    IndexKind::Single(_) => {
                        quote! { #ident: ::orzir_core::ArenaPtr<::orzir_core::Value>, }
                    }
                },
                OpFieldMeta::Region(meta) => match meta.index {
                    IndexKind::All => {
                        quote! { #ident: Vec<::orzir_core::ArenaPtr<::orzir_core::Region>>, }
                    }
                    IndexKind::Single(_) => {
                        quote! { #ident: ::orzir_core::ArenaPtr<::orzir_core::Region>, }
                    }
                },
                OpFieldMeta::Result(index) => match index {
                    IndexKind::All => {
                        quote! { #ident: Vec<::orzir_core::ArenaPtr<::orzir_core::Value>>, }
                    }
                    IndexKind::Single(_) => {
                        quote! { #ident: ::orzir_core::ArenaPtr<::orzir_core::Value>, }
                    }
                },
                OpFieldMeta::Successor(index) => match index {
                    IndexKind::All => {
                        quote! { #ident: Vec<Successor>, }
                    }
                    IndexKind::Single(_) => {
                        quote! { #ident: Successor, }
                    }
                },
                OpFieldMeta::Other { is_vec, ty } => {
                    if *is_vec {
                        quote! { #ident: Vec<#ty>, }
                    } else {
                        quote! { #ident: #ty, }
                    }
                }
            }
        })
        .collect::<TokenStream>();

    let struct_init = derive_info
        .fields
        .iter()
        .map(|(ident, meta)| {
            let ident = match ident {
                FieldIdent::Ident(ident) => syn::Ident::new(ident, proc_macro2::Span::call_site()),
                FieldIdent::Index(idx) => {
                    syn::Ident::new(&format!("arg_{}", idx), proc_macro2::Span::call_site())
                }
            };
            match meta {
                OpFieldMeta::Metadata => {
                    if derive_info.is_named {
                        quote! { #ident: ::orzir_core::OpMetadata::new(self_ptr), }
                    } else {
                        quote! { ::orzir_core::OpMetadata::new(self_ptr), }
                    }
                }
                _ => quote! { #ident, },
            }
        })
        .collect::<TokenStream>();

    let struct_init = if derive_info.is_named {
        quote! {
            Self { #struct_init }
        }
    } else {
        quote! {
            Self(#struct_init)
        }
    };

    let output = quote! {
        fn new(
            ctx: &mut ::orzir_core::Context,
            self_ptr: ::orzir_core::ArenaPtr<::orzir_core::OpObj>,
            #ctor_args
        ) -> ::orzir_core::ArenaPtr<::orzir_core::OpObj> {
            let instance = #struct_init;
            let obj = ::orzir_core::OpObj::from(instance);
            ctx.ops.fill(self_ptr, obj);
            self_ptr
        }
    };

    Ok(output)
}

fn derive_struct_metadata_methods(derive_info: &OpDeriveInfo) -> TokenStream {
    let metadata_field = derive_info
        .fields
        .iter()
        .find(|(_, meta)| matches!(meta, OpFieldMeta::Metadata))
        .unwrap();

    let metadata_field = match metadata_field {
        (FieldIdent::Ident(ident), _) => {
            let ident = syn::Ident::new(ident, proc_macro2::Span::call_site());
            quote! { self.#ident }
        }
        (FieldIdent::Index(idx), _) => {
            let index = syn::Index::from(*idx);
            quote! { self.#index }
        }
    };

    let output = quote! {
        fn metadata(&self) -> &::orzir_core::OpMetadata {
            &#metadata_field
        }

        fn metadata_mut(&mut self) -> &mut ::orzir_core::OpMetadata {
            &mut #metadata_field
        }
    };

    output
}

pub fn derive_impl(ast: &syn::DeriveInput) -> syn::Result<TokenStream> {
    let derive_info = OpDeriveInfo::from_ast(ast)?;

    let (primary, secondary) = &derive_info.mnemonic;

    let ctor = derive_struct_ctor(&derive_info)?;
    let metadata = derive_struct_metadata_methods(&derive_info);

    let ident = &ast.ident;

    let interface_register_casters = derive_info
        .interfaces
        .iter()
        .map(|path| {
            quote! { ::orzir_macros::register_caster!(ctx, #ident => #path); }
        })
        .collect::<TokenStream>();

    let verifier_register_casters = derive_info
        .verifiers
        .iter()
        .map(|path| {
            quote! { ::orzir_macros::register_caster!(ctx, #ident => #path); }
        })
        .collect::<TokenStream>();

    let verifier_impls = derive_info
        .verifiers
        .iter()
        .map(|path| {
            quote! { impl #path for #ident {} }
        })
        .collect::<TokenStream>();

    let verifier_calls = derive_info
        .verifiers
        .iter()
        .map(|path| {
            quote! { <Self as #path>::verify(self, ctx)?; }
        })
        .collect::<TokenStream>();

    let output = quote! {
        impl #ident {
            pub #ctor
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

            #metadata
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

    #[test]
    fn test_is_vec() {
        let src = quote! { Vec<ArenaPtr<TyObj>> };
        let ty = syn::parse2::<syn::Type>(src).unwrap();
        let ty = super::is_type_vec(&ty).unwrap();

        println!("{}", quote! { #ty });
    }
}
