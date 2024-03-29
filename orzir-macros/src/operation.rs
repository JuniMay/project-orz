use proc_macro2::TokenStream;
use quote::quote;

#[derive(Debug, Clone, Copy)]
enum IndexKind {
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

enum OpFieldMeta {
    /// The metadata field.
    Metadata { ident: syn::Ident },
    /// Other fields.
    Other {
        /// Whether the field is optional.
        optional: bool,
        /// The corresponding field ident.
        ident: syn::Ident,
        /// The type of the field.
        ty: syn::Type,
    },
}

#[derive(Default)]
struct OpInfo {
    /// The mnemonic of the operation.
    mnemonic: Option<String>,
    /// The verifiers of the operation.
    verifiers: Vec<syn::Path>,
    /// The interfaces of the operation.
    interfaces: Vec<syn::Path>,
    /// Fields
    fields: Vec<OpFieldMeta>,

    /// The artifact for metadata.
    metadata_artifact: TokenStream,
}

impl OpInfo {
    /// Get the info from a [`syn::DeriveInput`].
    fn from_ast(ast: &syn::DeriveInput) -> syn::Result<Self> {
        let mut info = Self::default();

        for attr in ast.attrs.iter() {
            let ident = attr.path().get_ident();

            if let Some(ident) = ident {
                match ident.to_string().as_str() {
                    "mnemonic" => {
                        if let syn::Meta::NameValue(ref meta) = attr.meta {
                            if let syn::Expr::Lit(ref lit) = meta.value {
                                if let syn::Lit::Str(ref lit) = lit.lit {
                                    info.mnemonic = Some(lit.value());
                                }
                            }
                        }
                    }
                    "verifiers" => {
                        if let syn::Meta::List(ref list) = attr.meta {
                            let paths = list.parse_args_with(
                                syn::punctuated::Punctuated::<syn::Path, syn::Token![,]>::parse_terminated)?;
                            info.verifiers = paths.into_iter().collect();
                        }
                    }
                    "interfaces" => {
                        if let syn::Meta::List(ref list) = attr.meta {
                            let paths = list.parse_args_with(
                                syn::punctuated::Punctuated::<syn::Path, syn::Token![,]>::parse_terminated)?;
                            info.interfaces = paths.into_iter().collect();
                        }
                    }
                    _ => {
                        continue;
                    }
                }
            } else {
                continue;
            }
        }

        match &ast.data {
            syn::Data::Struct(s) => match &s.fields {
                syn::Fields::Named(fields) => {
                    for field in fields.named.iter() {
                        let mut field_meta = OpFieldMeta::Other {
                            ident: field.ident.clone().unwrap(),
                            optional: false,
                            ty: field.ty.clone(),
                        };

                        for attr in field.attrs.iter() {
                            let ident = attr.path().get_ident();
                            if let Some(ident) = ident {
                                if ident == "metadata" {
                                    field_meta = OpFieldMeta::Metadata {
                                        ident: field.ident.clone().unwrap(),
                                    };
                                    break;
                                }
                            }
                        }

                        let ty = &field.ty;

                        // basic type checking.
                        match field_meta {
                            OpFieldMeta::Metadata { .. } => {
                                // type should be `OpMetadata`
                                if let syn::Type::Path(ref path) = ty {
                                    if let Some(segment) = path.path.segments.last() {
                                        if segment.ident != "OpMetadata" {
                                            return Err(syn::Error::new_spanned(
                                                ty,
                                                "metadata field should be of type `OpMetadata`",
                                            ));
                                        }
                                    }
                                }
                            }
                            OpFieldMeta::Other {
                                ref mut optional,
                                ref mut ty,
                                ..
                            } => {
                                // if the field has `Option` type, it is optional
                                if let syn::Type::Path(ref path) = ty {
                                    if let Some(segment) = path.path.segments.last() {
                                        if segment.ident == "Option" {
                                            *optional = true;
                                            if let syn::PathArguments::AngleBracketed(ref args) =
                                                segment.arguments
                                            {
                                                if let Some(syn::GenericArgument::Type(
                                                    ref inside,
                                                )) = args.args.first()
                                                {
                                                    *ty = inside.clone();
                                                }
                                            } else {
                                                return Err(syn::Error::new_spanned(
                                                    ty,
                                                    "expected type arguments for `Option`",
                                                ));
                                            }
                                        }
                                    }
                                }
                            }
                        }

                        info.fields.push(field_meta);
                    }
                }
                _ => {
                    return Err(syn::Error::new_spanned(
                        ast,
                        "only named fields are supported to derive `Op`",
                    ))
                }
            },
            _ => {
                return Err(syn::Error::new_spanned(
                    ast,
                    "only structs are supported to derive `Op`",
                ))
            }
        }

        Ok(info)
    }

    /// To verify the indices of entities are valid
    fn verify(&self) -> syn::Result<()> { Ok(()) }

    /// Generate all artifact for different entities and methods.
    fn generate_artifacts(&mut self) -> syn::Result<()> {
        for field in &self.fields {
            match field {
                OpFieldMeta::Metadata { ident } => {
                    self.metadata_artifact = quote! {
                        fn metadata(&self) -> &::orzir_core::OpMetadata {
                            &self.#ident
                        }

                        fn metadata_mut(&mut self) -> &mut ::orzir_core::OpMetadata {
                            &mut self.#ident
                        }
                    };
                }
                OpFieldMeta::Other { .. } => {}
            }
        }

        Ok(())
    }

    fn op_trait_impl(&mut self) -> syn::Result<TokenStream> {
        self.verify()?;
        self.generate_artifacts()?;

        let metadata_methods = &self.metadata_artifact;

        let result = quote! {
            #metadata_methods
        };

        Ok(result)
    }

    /// Get the `new` constructor for op.
    fn op_ctor(&self) -> TokenStream {
        let ctor_args = self
            .fields
            .iter()
            .filter(|field| !matches!(field, OpFieldMeta::Metadata { .. }))
            .map(|field| {
                let ident = match field {
                    OpFieldMeta::Metadata { ident } => ident,
                    OpFieldMeta::Other { ident, .. } => ident,
                };
                let ty = match field {
                    OpFieldMeta::Metadata { .. } => quote! { ::orzir_core::OpMetadata },
                    OpFieldMeta::Other {
                        ty,
                        optional: false,
                        ..
                    } => quote! { #ty },
                    OpFieldMeta::Other {
                        ty, optional: true, ..
                    } => quote! { Option<#ty> },
                };
                quote! {
                    #ident: #ty
                }
            })
            .collect::<Vec<_>>();

        let ctor_arg_names = self
            .fields
            .iter()
            .filter(|field| !matches!(field, OpFieldMeta::Metadata { .. }))
            .map(|field| match field {
                OpFieldMeta::Metadata { ident } => ident,
                OpFieldMeta::Other { ident, .. } => ident,
            });

        let ctor = quote! {
            fn new(
                ctx: &mut ::orzir_core::Context,
                self_ptr: ::orzir_core::ArenaPtr<::orzir_core::OpObj>,
                #(#ctor_args),*
            ) -> ::orzir_core::ArenaPtr<::orzir_core::OpObj> {
                let instance = Self {
                    metadata: ::orzir_core::OpMetadata::new(self_ptr),
                    #(#ctor_arg_names,)*
                };
                let instance = ::orzir_core::OpObj::from(instance);
                ctx.ops.fill(self_ptr, instance);
                self_ptr
            }
        };

        ctor
    }
}

pub fn derive_op(input: TokenStream) -> syn::Result<TokenStream> {
    let ast = syn::parse2::<syn::DeriveInput>(input).unwrap();
    let mut info = OpInfo::from_ast(&ast)?;

    let ident = &ast.ident;

    let mnemonic = info
        .mnemonic
        .clone()
        .ok_or_else(|| syn::Error::new_spanned(&ast, "missing mnemonic"))?;
    let (primary, secondary) = mnemonic.split_once('.').unwrap();

    let ctor = info.op_ctor();

    let interface_register_casters = info
        .interfaces
        .iter()
        .map(|path| {
            quote! {
                ::orzir_macros::register_caster!(ctx, #ident => #path);
            }
        })
        .collect::<Vec<_>>();

    let verifier_register_casters = info
        .verifiers
        .iter()
        .map(|path| {
            quote! {
                ::orzir_macros::register_caster!(ctx, #ident => #path);
            }
        })
        .collect::<Vec<_>>();

    let verifier_impls = info
        .verifiers
        .iter()
        .map(|path| {
            quote! {
                impl #path for #ident {}
            }
        })
        .collect::<Vec<_>>();

    let verifier_calls = info
        .verifiers
        .iter()
        .map(|path| {
            quote! {
                <Self as #path>::verify(self, ctx)?;
            }
        })
        .collect::<Vec<_>>();

    let verify_interfaces_impl = quote! {
        impl ::orzir_core::RunVerifiers for #ident {
            fn run_verifiers(&self, ctx: &::orzir_core::Context) -> ::anyhow::Result<()> {
                #(#verifier_calls)*
                Ok(())
            }
        }
    };

    let op_impl_methods = info.op_trait_impl()?;
    let op_impl = quote! {
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

                #(#interface_register_casters)*
                #(#verifier_register_casters)*
            }

            #op_impl_methods
        }
    };

    let result = quote! {
        impl #ident {
            pub #ctor
        }

        #op_impl

        #(#verifier_impls)*

        #verify_interfaces_impl
    };

    Ok(result)
}

#[cfg(test)]
mod tests {
    use quote::quote;

    use super::derive_op;

    #[test]
    fn test_0() {
        let src = quote! {
            #[derive(Op)]
            #[mnemonic = "func.return"]
            // #[verifiers(NumResults<0>, VariadicOperands, NumRegions<0>, IsTerminator)]
            pub struct ReturnOp {
                #[metadata]
                metadata: OpMetadata,

                #[operand(...)]
                operands: Vec<ArenaPtr<Value>>,
            }
        };

        let output = derive_op(src).unwrap();

        println!("{}", output);

        let ast = syn::parse_file(&output.to_string()).unwrap();

        let ast = prettyplease::unparse(&ast);

        println!("{}", ast);
    }
}
