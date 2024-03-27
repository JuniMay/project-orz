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

impl OpFieldMeta {
    fn append(
        self,
        seq: &mut Vec<OpEntityKind>,
        field: &syn::Field,
        attr: &syn::Attribute,
    ) -> syn::Result<()> {
        match self {
            OpFieldMeta::Index(index) => {
                // check if the first element is a multi entity, if
                // so, return an error.
                // Otherwise, just push the single entity.
                if seq.len() == 1 {
                    if let OpEntityKind::Multi(_) = &seq[0] {
                        return Err(syn::Error::new_spanned(
                            attr,
                            "cannot have sequential and discrete `result` field at the same time.",
                        ));
                    }
                }
                if seq.len() <= index {
                    seq.resize(index + 1, OpEntityKind::Reserved);
                }

                if let OpEntityKind::Reserved = seq[index] {
                    seq[index] = OpEntityKind::Single(field.ident.clone().unwrap());
                } else {
                    return Err(syn::Error::new_spanned(
                        attr,
                        "index already used in `result` field.",
                    ));
                }
            }
            OpFieldMeta::Multi => {
                if !seq.is_empty() {
                    return Err(syn::Error::new_spanned(
                        attr,
                        "cannot have sequential and discrete or multiple sequential `result` field at the same time.",
                    ));
                }
                seq.push(OpEntityKind::Multi(field.ident.clone().unwrap()));
            }
        }

        Ok(())
    }
}

#[derive(Clone)]
enum OpEntityKind {
    /// The field contains multiple entities.
    Multi(syn::Ident),
    /// The field contains a single entity with the index.
    Single(syn::Ident),
    /// Reserved
    Reserved,
}

#[derive(Default)]
struct OpInfo {
    /// The mnemonic of the operation.
    mnemonic: Option<String>,
    /// The verifiers of the operation.
    verifiers: Vec<syn::Path>,
    /// The interfaces of the operation.
    interfaces: Vec<syn::Path>,
    /// The field of the self_ptr.
    self_ptr: Option<syn::Ident>,
    /// The field of the parent_block.
    parent_block: Option<syn::Ident>,
    /// Results
    results: Vec<OpEntityKind>,
    /// Operands
    operands: Vec<OpEntityKind>,
    /// Regions
    regions: Vec<OpEntityKind>,
    /// Successors
    successors: Vec<OpEntityKind>,
    /// Other fields to build the operation.
    ctor_fields: Vec<syn::Field>,
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
                        let mut is_ctor_field = true;
                        for attr in field.attrs.iter() {
                            let ident = attr.path().get_ident();
                            if let Some(ident) = ident {
                                match ident.to_string().as_str() {
                                    "self_ptr" => {
                                        info.self_ptr = field.ident.clone();
                                        is_ctor_field = false;
                                    }
                                    "result" => {
                                        // `#[result(0)]` or `#[result(...)]`
                                        // the inside can be an index, or three dots representing
                                        let meta = attr.parse_args::<OpFieldMeta>()?;
                                        meta.append(&mut info.results, field, attr)?;
                                        // result should be built and added with the builder.
                                        is_ctor_field = false;
                                    }
                                    "operand" => {
                                        let meta = attr.parse_args::<OpFieldMeta>()?;
                                        meta.append(&mut info.operands, field, attr)?;
                                        is_ctor_field = false;
                                    }
                                    "region" => {
                                        let meta = attr.parse_args::<OpFieldMeta>()?;
                                        meta.append(&mut info.regions, field, attr)?;
                                        is_ctor_field = false;
                                    }
                                    "successor" => {
                                        let meta = attr.parse_args::<OpFieldMeta>()?;
                                        meta.append(&mut info.successors, field, attr)?;
                                        is_ctor_field = false;
                                    }
                                    "parent_block" => {
                                        info.parent_block = field.ident.clone();
                                        is_ctor_field = false;
                                    }
                                    _ => {}
                                }
                            }
                        }
                        if is_ctor_field {
                            info.ctor_fields.push(field.clone());
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

    fn num_entity_method(entities: &Vec<OpEntityKind>) -> syn::Result<TokenStream> {
        let result = match entities.len() {
            0 => quote! { 0 },
            1 => {
                let num = match &entities[0] {
                    OpEntityKind::Single(_) => {
                        quote! { 1 }
                    }
                    OpEntityKind::Multi(ident) => {
                        let ident = ident.clone();
                        quote! { self.#ident.len() }
                    }
                    _ => unreachable!(),
                };
                quote! { #num }
            }
            _ => {
                let num = entities.len();
                quote! { #num }
            }
        };

        Ok(result)
    }

    fn get_entity_method(entities: &Vec<OpEntityKind>, by_ref: bool) -> syn::Result<TokenStream> {
        let result = match entities.len() {
            0 => quote! {
                None
            },
            1 => match &entities[0] {
                OpEntityKind::Single(ident) => {
                    let ident = ident.clone();
                    if by_ref {
                        quote! {
                            if index == 0 {
                                self.#ident.as_ref()
                            } else {
                                None
                            }
                        }
                    } else {
                        quote! {
                            if index == 0 {
                                self.#ident
                            } else {
                                None
                            }
                        }
                    }
                }
                OpEntityKind::Multi(ident) => {
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
                _ => unreachable!(),
            },
            _ => {
                let match_arms = entities.iter().enumerate().map(|(i, entity)| match entity {
                    OpEntityKind::Single(ident) => {
                        let ident = ident.clone();
                        if by_ref {
                            quote! {
                                #i => self.#ident.as_ref()
                            }
                        } else {
                            quote! {
                                #i => self.#ident
                            }
                        }
                    }
                    _ => unreachable!(),
                });
                quote! {
                    match index {
                        #(#match_arms),*,
                        _ => None
                    }
                }
            }
        };

        Ok(result)
    }

    fn set_entity_method(entities: &Vec<OpEntityKind>) -> syn::Result<TokenStream> {
        let result = match entities.len() {
            0 => {
                quote! {
                    ::anyhow::bail!("index out of bounds")
                }
            }
            1 => match &entities[0] {
                OpEntityKind::Single(ident) => {
                    let ident = ident.clone();
                    quote! {
                        if index == 0 {
                            Ok(std::mem::replace(&mut self.#ident, Some(value)))
                        } else {
                            Err(::anyhow::anyhow!("index out of bounds"))
                        }
                    }
                }
                OpEntityKind::Multi(ident) => {
                    let ident = ident.clone();
                    quote! {
                        if index < self.#ident.len() {
                            // let old = self.#ident[index];
                            // self.#ident[index] = value;
                            // Ok(Some(old))
                            Ok(Some(std::mem::replace(&mut self.#ident[index], value)))
                        } else if index == self.#ident.len() {
                            self.#ident.push(value);
                            Ok(None)
                        } else {
                            Err(::anyhow::anyhow!("index out of bounds"))
                        }
                    }
                }
                _ => unreachable!(),
            },
            _ => {
                let match_arms = entities.iter().enumerate().map(|(i, entity)| match entity {
                    OpEntityKind::Single(ident) => {
                        let ident = ident.clone();
                        quote! {
                            #i => {
                                Ok(std::mem::replace(&mut self.#ident, Some(value)))
                            }
                        }
                    }
                    _ => unreachable!(),
                });
                quote! {
                    match index {
                        #(#match_arms)*
                        _ => Err(::anyhow::anyhow!("index out of bounds"))
                    }
                }
            }
        };

        Ok(result)
    }

    fn op_trait_impl(&self, ast: &syn::DeriveInput) -> syn::Result<TokenStream> {
        let self_ptr_ident = self
            .self_ptr
            .as_ref()
            .ok_or_else(|| syn::Error::new_spanned(ast, "missing self_ptr field"))?;
        let self_ptr_method = quote! {
            fn self_ptr(&self) -> ::orzir_core::ArenaPtr<::orzir_core::OpObj> {
                self.#self_ptr_ident
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

        let parent_block_method = match &self.parent_block {
            Some(ident) => {
                quote! {
                    fn parent_block(&self) -> Option<::orzir_core::ArenaPtr<::orzir_core::Block>> {
                        self.#ident
                    }
                }
            }
            _ => return Err(syn::Error::new_spanned(ast, "missing parent_block field")),
        };

        let set_parent_block_method = match &self.parent_block {
            Some(ident) => {
                quote! {
                    fn set_parent_block(
                        &mut self,
                        value: Option<::orzir_core::ArenaPtr<::orzir_core::Block>>
                    ) -> ::anyhow::Result<Option<::orzir_core::ArenaPtr<::orzir_core::Block>>> {
                        let old = self.#ident;
                        self.#ident = value;
                        Ok(old)
                    }
                }
            }
            _ => return Err(syn::Error::new_spanned(ast, "missing parent_block field")),
        };

        let result = quote! {
            #self_ptr_method

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

            #parent_block_method
            #set_parent_block_method
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

    let ctor_args = info.ctor_fields.iter().map(|field| {
        let ident = field.ident.clone().unwrap();
        let ty = field.ty.clone();
        quote! {
            #ident: #ty
        }
    });

    let ctor_arg_names = info.ctor_fields.iter().map(|field| field.ident.clone().unwrap());

    let ctor = quote! {
        fn new(
            ctx: &mut ::orzir_core::Context,
            #(#ctor_args),*
        ) -> ::orzir_core::ArenaPtr<::orzir_core::OpObj> {
            let self_ptr = ctx.ops.reserve();
            let instance = Self {
                #(#ctor_arg_names,)*
                ..Default::default()
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
            #[derive(Default, Op)]
            #[mnemonic = "cf.jump"]
            pub struct Jump {
                #[self_ptr]
                self_ptr: ArenaPtr<OpObj>,

                #[parent_block]
                parent: Option<ArenaPtr<Block>>,

                #[successor(0)]
                succ: Option<Successor>,
            }
        };

        let output = derive_op(src).unwrap();

        let ast = syn::parse_file(&output.to_string()).unwrap();

        let ast = prettyplease::unparse(&ast);

        println!("{}", ast);
    }
}
