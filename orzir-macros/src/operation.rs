use std::collections::HashMap;

use proc_macro2::TokenStream;
use quote::quote;

/// The contents inside the attribute.
enum OpFieldMeta {
    /// An index number
    Index(usize),
    /// Three dots representing multiple entities.
    Multi,
}

impl syn::parse::Parse for OpFieldMeta {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        if input.peek(syn::Token![...]) {
            input.parse::<syn::Token![...]>()?;
            Ok(Self::Multi)
        } else {
            let index = input.parse::<syn::LitInt>()?.base10_parse::<usize>()?;
            Ok(Self::Index(index))
        }
    }
}

/// The deriving kind of an entity in the operation.
///
/// i.e. result, operand, region, successor
enum OpEntityKind {
    /// The field contains multiple entities.
    ///
    /// i.e. `#[result(...)]`
    Combined(syn::Ident),
    /// The field contains a single entity with the index.
    ///
    /// i.e. `#[result(0)]`
    Distributed { fields: HashMap<usize, syn::Ident> },
}

impl Default for OpEntityKind {
    fn default() -> Self {
        Self::Distributed {
            fields: HashMap::new(),
        }
    }
}

impl OpEntityKind {
    fn append(
        &mut self,
        attr: &syn::Attribute,
        field: &syn::Field,
        meta: OpFieldMeta,
    ) -> syn::Result<()> {
        match meta {
            OpFieldMeta::Index(index) => match self {
                OpEntityKind::Distributed { fields } => {
                    fields.insert(
                        index,
                        syn::Ident::new(
                            &field.ident.as_ref().unwrap().to_string(),
                            proc_macro2::Span::call_site(),
                        ),
                    );
                }
                _ => {
                    return Err(syn::Error::new_spanned(
                            attr,
                            "cannot have combined (`#[xxx(...)]`) and distributed (`#[xxx(0)]`) entities together",
                        ));
                }
            },
            OpFieldMeta::Multi => match self {
                OpEntityKind::Distributed { fields } if fields.is_empty() => {
                    *self = OpEntityKind::Combined(syn::Ident::new(
                        &field.ident.as_ref().unwrap().to_string(),
                        proc_macro2::Span::call_site(),
                    ));
                }
                _ => {
                    return Err(syn::Error::new_spanned(
                        attr,
                        "cannot have multiple combined entities",
                    ));
                }
            },
        }

        Ok(())
    }
}

#[derive(Default)]
struct OpInfo {
    /// The mnemonic of the operation.
    mnemonic: Option<String>,
    /// The verifiers of the operation.
    verifiers: Vec<syn::Path>,
    /// The interfaces of the operation.
    interfaces: Vec<syn::Path>,
    /// The field of the metadata.
    metadata: Option<syn::Ident>,
    /// Results
    results: OpEntityKind,
    /// Operands
    operands: OpEntityKind,
    /// Regions
    regions: OpEntityKind,
    /// Successors
    successors: OpEntityKind,
    /// Other fields to build the operation.
    ctor_arg_fields: Vec<syn::Field>,
    /// The default fields to build the operation.
    ctor_default_fields: Vec<syn::Field>,
}

impl OpInfo {
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
                        let mut is_derived_field = false;
                        let mut is_metadata = false;
                        for attr in field.attrs.iter() {
                            let ident = attr.path().get_ident();
                            if let Some(ident) = ident {
                                match ident.to_string().as_str() {
                                    "metadata" => {
                                        info.metadata = field.ident.clone();
                                        is_derived_field = true;
                                        is_metadata = true;
                                    }
                                    "result" => {
                                        let meta = attr.parse_args::<OpFieldMeta>()?;
                                        info.results.append(attr, field, meta)?;
                                        is_derived_field = true;
                                    }
                                    "operand" => {
                                        let meta = attr.parse_args::<OpFieldMeta>()?;
                                        info.operands.append(attr, field, meta)?;
                                        is_derived_field = true;
                                    }
                                    "region" => {
                                        let meta = attr.parse_args::<OpFieldMeta>()?;
                                        info.regions.append(attr, field, meta)?;
                                        is_derived_field = true;
                                    }
                                    "successor" => {
                                        let meta = attr.parse_args::<OpFieldMeta>()?;
                                        info.successors.append(attr, field, meta)?;
                                        is_derived_field = true;
                                    }
                                    _ => {}
                                }
                            }
                        }
                        if !is_derived_field {
                            info.ctor_arg_fields.push(field.clone());
                        } else if !is_metadata {
                            info.ctor_default_fields.push(field.clone());
                        }

                        let ty = &field.ty;

                        // check if ty starts with `HoldVec` or `Vec` for non-ctor fields.

                        // TODO: More fine-grained check for multi/single and the types.
                        if is_derived_field && !is_metadata {
                            if let syn::Type::Path(ref path) = ty {
                                if let Some(segment) = path.path.segments.last() {
                                    if segment.ident != "HoldVec" && segment.ident != "Hold" {
                                        return Err(syn::Error::new_spanned(
                                            ty,
                                            "only `HoldVec` or `Vec` is supported for derived fields",
                                        ));
                                    }
                                }
                            }
                        }
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

    fn num_entity_method(entities: &OpEntityKind) -> syn::Result<TokenStream> {
        let result = match entities {
            OpEntityKind::Combined(ident) => {
                let ident = ident.clone();
                quote! { self.#ident.len() }
            }
            OpEntityKind::Distributed { fields } => {
                let num = fields.len();
                quote! { #num }
            }
        };

        Ok(result)
    }

    fn get_entity_method(entities: &OpEntityKind, by_ref: bool) -> syn::Result<TokenStream> {
        let result = match entities {
            OpEntityKind::Combined(ident) => {
                let ident = ident.clone();
                if by_ref {
                    quote! {
                        self.#ident.get(index)
                    }
                } else {
                    quote! {
                        self.#ident.get(index).copied()
                    }
                }
            }
            OpEntityKind::Distributed { fields } => {
                let match_arms = fields.iter().map(|(i, ident)| {
                    let ident = ident.clone();
                    if by_ref {
                        quote! {
                            #i => self.#ident.as_ref()
                        }
                    } else {
                        quote! {
                            #i => self.#ident.copied().into()
                        }
                    }
                });
                quote! {
                    match index {
                        #(#match_arms,)*
                        _ => None
                    }
                }
            }
        };

        Ok(result)
    }

    fn set_entity_method(entities: &OpEntityKind) -> syn::Result<TokenStream> {
        let result = match entities {
            OpEntityKind::Combined(ident) => {
                let ident = ident.clone();
                quote! {
                    Ok(self.#ident.set(index, value))
                }
            }
            OpEntityKind::Distributed { fields } => {
                let match_arms = fields.iter().map(|(i, ident)| {
                    let ident = ident.clone();
                    quote! {
                        #i => Ok(std::mem::replace(&mut self.#ident, Some(value).into()).into())
                    }
                });
                quote! {
                    match index {
                        #(#match_arms,)*
                        _ => Err(::anyhow::anyhow!("index out of bounds"))
                    }
                }
            }
        };

        Ok(result)
    }

    fn op_trait_impl(&self, ast: &syn::DeriveInput) -> syn::Result<TokenStream> {
        let metadata_ident = self
            .metadata
            .as_ref()
            .ok_or_else(|| syn::Error::new_spanned(ast, "missing metadata field"))?;

        let metadata_methods = quote! {
            fn metadata(&self) -> &::orzir_core::OpMetadata {
                &self.#metadata_ident
            }

            fn metadata_mut(&mut self) -> &mut ::orzir_core::OpMetadata {
                &mut self.#metadata_ident
            }
        };

        let num_operands_method = Self::num_entity_method(&self.operands)?;
        let num_operands_method = quote! {
            fn num_operands(&self) -> usize {
                #num_operands_method
            }
        };

        // for single entities, generate arms first and match by index. For multiple
        // entities, just index by the index.
        let get_operand_method = Self::get_entity_method(&self.operands, false)?;
        let get_operand_method = quote! {
            fn get_operand(
                &self,
                index: usize
            ) -> Option<::orzir_core::ArenaPtr<::orzir_core::Value>> {
                #get_operand_method
            }
        };

        let set_operand_method = Self::set_entity_method(&self.operands)?;
        let set_operand_method = quote! {
            fn set_operand(
                &mut self,
                index: usize,
                value: ::orzir_core::ArenaPtr<::orzir_core::Value>
            ) -> ::anyhow::Result<Option<::orzir_core::ArenaPtr<::orzir_core::Value>>> {
                #set_operand_method
            }
        };

        let num_results_method = Self::num_entity_method(&self.results)?;
        let num_results_method = quote! {
            fn num_results(&self) -> usize {
                #num_results_method
            }
        };

        let get_result_method = Self::get_entity_method(&self.results, false)?;
        let get_result_method = quote! {
            fn get_result(
                &self,
                index: usize
            ) -> Option<::orzir_core::ArenaPtr<::orzir_core::Value>> {
                #get_result_method
            }
        };

        let set_result_method = Self::set_entity_method(&self.results)?;
        let set_result_method = quote! {
            fn set_result(
                &mut self,
                index: usize,
                value: ::orzir_core::ArenaPtr<::orzir_core::Value>
            ) -> ::anyhow::Result<Option<::orzir_core::ArenaPtr<::orzir_core::Value>>> {
                #set_result_method
            }
        };

        let num_regions_method = Self::num_entity_method(&self.regions)?;
        let num_regions_method = quote! {
            fn num_regions(&self) -> usize {
                #num_regions_method
            }
        };

        let get_region_method = Self::get_entity_method(&self.regions, false)?;
        let get_region_method = quote! {
            fn get_region(
                &self,
                index: usize
            ) -> Option<::orzir_core::ArenaPtr<::orzir_core::Region>> {
                #get_region_method
            }
        };

        let set_region_method = Self::set_entity_method(&self.regions)?;
        let set_region_method = quote! {
            fn set_region(
                &mut self,
                index: usize,
                value: ::orzir_core::ArenaPtr<::orzir_core::Region>
            ) -> ::anyhow::Result<Option<::orzir_core::ArenaPtr<::orzir_core::Region>>> {
                #set_region_method
            }
        };

        let num_successors_method = Self::num_entity_method(&self.successors)?;
        let num_successors_method = quote! {
            fn num_successors(&self) -> usize {
                #num_successors_method
            }
        };

        let get_successor_method = Self::get_entity_method(&self.successors, true)?;
        let get_successor_method = quote! {
            fn get_successor(
                &self,
                index: usize
            ) -> Option<&::orzir_core::Successor> {
                #get_successor_method
            }
        };

        let set_successor_method = Self::set_entity_method(&self.successors)?;
        let set_successor_method = quote! {
            fn set_successor(
                &mut self,
                index: usize,
                value: ::orzir_core::Successor
            ) -> ::anyhow::Result<Option<::orzir_core::Successor>> {
                #set_successor_method
            }
        };

        let result = quote! {
            #metadata_methods

            #num_operands_method
            #num_results_method
            #num_regions_method
            #num_successors_method

            #get_operand_method
            #get_result_method
            #get_region_method
            #get_successor_method

            #set_operand_method
            #set_result_method
            #set_region_method
            #set_successor_method
        };

        Ok(result)
    }
}

pub fn derive_op(input: TokenStream) -> syn::Result<TokenStream> {
    let ast = syn::parse2::<syn::DeriveInput>(input).unwrap();
    let info = OpInfo::from_ast(&ast)?;

    let ident = &ast.ident;

    let mnemonic = info
        .mnemonic
        .clone()
        .ok_or_else(|| syn::Error::new_spanned(&ast, "missing mnemonic"))?;
    let (primary, secondary) = mnemonic.split_once('.').unwrap();

    let ctor_args = info.ctor_arg_fields.iter().map(|field| {
        let ident = field.ident.clone().unwrap();
        let ty = field.ty.clone();
        quote! {
            #ident: #ty
        }
    });

    let ctor_arg_names = info.ctor_arg_fields.iter().map(|field| field.ident.clone().unwrap());
    let ctor_default_names =
        info.ctor_default_fields.iter().map(|field| field.ident.clone().unwrap());
    let metadata_ident = info.metadata.as_ref().unwrap();

    let ctor = quote! {
        fn new(
            ctx: &mut ::orzir_core::Context,
            #(#ctor_args),*
        ) -> ::orzir_core::ArenaPtr<::orzir_core::OpObj> {
            let self_ptr = ctx.ops.reserve();
            let instance = Self {
                #metadata_ident: ::orzir_core::OpMetadata::new(self_ptr),
                #(#ctor_arg_names,)*
                #(#ctor_default_names: Default::default(),)*
            };
            let instance = ::orzir_core::OpObj::from(instance);
            ctx.ops.fill(self_ptr, instance);
            self_ptr
        }
    };

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
        impl ::orzir_core::VerifyInterfaces for #ident {
            fn verify_interfaces(&self, ctx: &::orzir_core::Context) -> ::anyhow::Result<()> {
                #(#verifier_calls)*
                Ok(())
            }
        }
    };

    let op_impl_methods = info.op_trait_impl(&ast)?;
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
            #[mnemonic = "arith.iadd"]
            #[verifiers(
                NumResults<1>, NumOperands<2>, NumRegions<0>,
                SameResultTys, SameOperandTys, SameOperandAndResultTys
            )]
            pub struct IAddOp {
                #[metadata]
                metadata: OpMetadata,

                #[result(0)]
                result: Hold<ArenaPtr<Value>>,

                #[operand(0)]
                lhs: Hold<ArenaPtr<Value>>,

                #[operand(1)]
                rhs: Hold<ArenaPtr<Value>>,
            }
        };

        let output = derive_op(src).unwrap();

        let ast = syn::parse_file(&output.to_string()).unwrap();

        let ast = prettyplease::unparse(&ast);

        println!("{}", ast);
    }
}
