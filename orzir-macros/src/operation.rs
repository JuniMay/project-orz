use proc_macro2::TokenStream;
use quote::quote;

#[derive(Debug, Clone, Copy)]
enum IndexKind {
    All,
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
    Metadata {
        ident: syn::Ident,
    },
    Result {
        ident: syn::Ident,
        index: IndexKind,
    },
    Operand {
        ident: syn::Ident,
        index: IndexKind,
    },
    Region {
        ident: syn::Ident,
        index: IndexKind,
    },
    Successor {
        ident: syn::Ident,
        index: IndexKind,
    },
    Other {
        optional: bool,
        ident: syn::Ident,
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

    metadata_artifact: TokenStream,

    num_operands_artifact: Vec<TokenStream>,
    num_results_artifact: Vec<TokenStream>,
    num_regions_artifact: Vec<TokenStream>,
    num_successors_artifact: Vec<TokenStream>,

    get_operand_artifact: Vec<TokenStream>,
    get_result_artifact: Vec<TokenStream>,
    get_region_artifact: Vec<TokenStream>,
    get_successor_artifact: Vec<TokenStream>,

    set_operand_artifact: Vec<TokenStream>,
    set_result_artifact: Vec<TokenStream>,
    set_region_artifact: Vec<TokenStream>,
    set_successor_artifact: Vec<TokenStream>,

    is_operand_match: bool,
    is_result_match: bool,
    is_region_match: bool,
    is_successor_match: bool,
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
                        let mut field_meta = OpFieldMeta::Other {
                            ident: field.ident.clone().unwrap(),
                            optional: false,
                            ty: field.ty.clone(),
                        };

                        for attr in field.attrs.iter() {
                            let ident = attr.path().get_ident();
                            if let Some(ident) = ident {
                                match ident.to_string().as_str() {
                                    "metadata" => {
                                        field_meta = OpFieldMeta::Metadata {
                                            ident: field.ident.clone().unwrap(),
                                        };
                                        break;
                                    }
                                    "result" => {
                                        let index = attr.parse_args::<IndexKind>()?;
                                        field_meta = OpFieldMeta::Result {
                                            ident: field.ident.clone().unwrap(),
                                            index,
                                        };
                                    }
                                    "operand" => {
                                        let index = attr.parse_args::<IndexKind>()?;
                                        field_meta = OpFieldMeta::Operand {
                                            ident: field.ident.clone().unwrap(),
                                            index,
                                        };
                                    }
                                    "region" => {
                                        let index = attr.parse_args::<IndexKind>()?;
                                        field_meta = OpFieldMeta::Region {
                                            ident: field.ident.clone().unwrap(),
                                            index,
                                        };
                                    }
                                    "successor" => {
                                        let index = attr.parse_args::<IndexKind>()?;
                                        field_meta = OpFieldMeta::Successor {
                                            ident: field.ident.clone().unwrap(),
                                            index,
                                        };
                                    }
                                    _ => {}
                                }
                            }
                        }

                        let ty = &field.ty;

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
                            OpFieldMeta::Result { index, .. }
                            | OpFieldMeta::Operand { index, .. }
                            | OpFieldMeta::Region { index, .. } => {
                                let ty_str = match field_meta {
                                    OpFieldMeta::Result { .. } | OpFieldMeta::Operand { .. } => {
                                        "Value"
                                    }
                                    OpFieldMeta::Region { .. } => "Region",
                                    _ => unreachable!(),
                                };

                                match index {
                                    IndexKind::All => {
                                        if let syn::Type::Path(ref path) = ty {
                                            if let Some(segment) = path.path.segments.last() {
                                                if segment.ident != "Vec" {
                                                    return Err(syn::Error::new_spanned(
                                                        ty,
                                                        format!(
                                                            "expect type `Vec<ArenaPtr<{}>>`",
                                                            ty_str
                                                        ),
                                                    ));
                                                }
                                            }
                                        }
                                    }
                                    IndexKind::Single(_) => {
                                        if let syn::Type::Path(ref path) = ty {
                                            if let Some(segment) = path.path.segments.last() {
                                                if segment.ident != "ArenaPtr" {
                                                    return Err(syn::Error::new_spanned(
                                                        ty,
                                                        format!(
                                                            "expect type `ArenaPtr<{}>`",
                                                            ty_str
                                                        ),
                                                    ));
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            OpFieldMeta::Successor { .. } => {
                                // type should be `Successor`
                                if let syn::Type::Path(ref path) = ty {
                                    if let Some(segment) = path.path.segments.last() {
                                        if segment.ident != "Successor" {
                                            return Err(syn::Error::new_spanned(
                                                ty,
                                                "expect type `Successor`",
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
    fn verify(&self) -> syn::Result<()> {
        // for each entity kind, only one `All` can be present
        // and only one metadata field can be present
        let mut metadata = None;
        let mut result = None;
        let mut operand = None;
        let mut region = None;
        let mut successor = None;

        for field in &self.fields {
            match field {
                OpFieldMeta::Metadata { ident } => {
                    if metadata.is_some() {
                        return Err(syn::Error::new_spanned(
                            ident,
                            "only one metadata field is allowed",
                        ));
                    }
                    metadata = Some(ident);
                }
                OpFieldMeta::Result { ident, index } => match (result, index) {
                    (None, _) => result = Some(*index),
                    (Some(IndexKind::All), _) => {
                        return Err(syn::Error::new_spanned(
                            ident,
                            "only one `...` index is allowed",
                        ));
                    }
                    (Some(IndexKind::Single(_)), IndexKind::All) => {
                        return Err(syn::Error::new_spanned(
                            ident,
                            "single index and `...` index cannot be mixed",
                        ));
                    }
                    _ => {}
                },
                OpFieldMeta::Operand { ident, index } => match (operand, index) {
                    (None, _) => operand = Some(*index),
                    (Some(IndexKind::All), _) => {
                        return Err(syn::Error::new_spanned(
                            ident,
                            "only one `...` index is allowed",
                        ));
                    }
                    (Some(IndexKind::Single(_)), IndexKind::All) => {
                        return Err(syn::Error::new_spanned(
                            ident,
                            "single index and `...` index cannot be mixed",
                        ));
                    }
                    _ => {}
                },
                OpFieldMeta::Region { ident, index } => match (region, index) {
                    (None, _) => region = Some(*index),
                    (Some(IndexKind::All), _) => {
                        return Err(syn::Error::new_spanned(
                            ident,
                            "only one `...` index is allowed",
                        ));
                    }
                    (Some(IndexKind::Single(_)), IndexKind::All) => {
                        return Err(syn::Error::new_spanned(
                            ident,
                            "single index and `...` index cannot be mixed",
                        ));
                    }
                    _ => {}
                },
                OpFieldMeta::Successor { ident, index } => match (successor, index) {
                    (None, _) => successor = Some(*index),
                    (Some(IndexKind::All), _) => {
                        return Err(syn::Error::new_spanned(
                            ident,
                            "only one `...` index is allowed",
                        ));
                    }
                    (Some(IndexKind::Single(_)), IndexKind::All) => {
                        return Err(syn::Error::new_spanned(
                            ident,
                            "single index and `...` index cannot be mixed",
                        ));
                    }
                    _ => {}
                },
                OpFieldMeta::Other { .. } => {}
            }
        }

        Ok(())
    }

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
                OpFieldMeta::Operand { ident, index } => match index {
                    IndexKind::All => {
                        self.num_operands_artifact = vec![quote! {
                            self.#ident.len()
                        }];
                        self.get_operand_artifact = vec![quote! {
                            self.#ident.get(index).copied()
                        }];
                        self.set_operand_artifact = vec![quote! {
                            if index > self.#ident.len() {
                                ::anyhow::bail!("index out of bounds")
                            }
                            if index == self.#ident.len() {
                                self.#ident.push(value);
                                Ok(None)
                            } else {
                                Ok(Some(std::mem::replace(&mut self.#ident[index], value)))
                            }
                        }];
                    }
                    IndexKind::Single(index) => {
                        if self.num_operands_artifact.is_empty() {
                            self.num_operands_artifact = vec![quote!(1)];
                        } else {
                            self.num_operands_artifact.push(quote!(+1));
                        }
                        self.get_operand_artifact.push(quote! {
                            #index => Some(self.#ident)
                        });
                        self.set_operand_artifact.push(quote! {
                            #index => Ok(Some(std::mem::replace(&mut self.#ident, value)))
                        });
                        self.is_operand_match = true;
                    }
                },
                OpFieldMeta::Result { ident, index } => match index {
                    IndexKind::All => {
                        self.num_results_artifact = vec![quote! {
                            self.#ident.len()
                        }];
                        self.get_result_artifact = vec![quote! {
                            self.#ident.get(index).copied()
                        }];
                        self.set_result_artifact = vec![quote! {
                            if index > self.#ident.len() {
                                ::anyhow::bail!("index out of bounds")
                            }
                            if index == self.#ident.len() {
                                self.#ident.push(value);
                                Ok(None)
                            } else {
                                Ok(Some(std::mem::replace(&mut self.#ident[index], value)))
                            }
                        }];
                    }
                    IndexKind::Single(index) => {
                        if self.num_results_artifact.is_empty() {
                            self.num_results_artifact = vec![quote!(1)];
                        } else {
                            self.num_results_artifact.push(quote!(+1));
                        }
                        self.get_result_artifact.push(quote! {
                            #index => Some(self.#ident)
                        });
                        self.set_result_artifact.push(quote! {
                            #index => Ok(Some(std::mem::replace(&mut self.#ident, value)))
                        });
                        self.is_result_match = true;
                    }
                },
                OpFieldMeta::Region { ident, index } => match index {
                    IndexKind::All => {
                        self.num_regions_artifact = vec![quote! {
                            self.#ident.len()
                        }];
                        self.get_region_artifact = vec![quote! {
                            self.#ident.get(index).copied()
                        }];
                        self.set_region_artifact = vec![quote! {
                            if index > self.#ident.len() {
                                ::anyhow::bail!("index out of bounds")
                            }
                            if index == self.#ident.len() {
                                self.#ident.push(value);
                                Ok(None)
                            } else {
                                Ok(Some(std::mem::replace(&mut self.#ident[index], value)))
                            }
                        }];
                    }
                    IndexKind::Single(index) => {
                        if self.num_regions_artifact.is_empty() {
                            self.num_regions_artifact = vec![quote!(1)];
                        } else {
                            self.num_regions_artifact.push(quote!(+1));
                        }
                        self.get_region_artifact.push(quote! {
                            #index => Some(self.#ident)
                        });
                        self.set_region_artifact.push(quote! {
                            #index => Ok(Some(std::mem::replace(&mut self.#ident, value)))
                        });
                        self.is_region_match = true;
                    }
                },
                OpFieldMeta::Successor { ident, index } => match index {
                    IndexKind::All => {
                        self.num_successors_artifact = vec![quote! {
                            self.#ident.len()
                        }];
                        self.get_successor_artifact = vec![quote! {
                            self.#ident.get(index).copied()
                        }];
                        self.set_successor_artifact = vec![quote! {
                            if index > self.#ident.len() {
                                ::anyhow::bail!("index out of bounds")
                            }
                            if index == self.#ident.len() {
                                self.#ident.push(value);
                                Ok(None)
                            } else {
                                Ok(Some(std::mem::replace(&mut self.#ident[index], value)))
                            }
                        }];
                    }
                    IndexKind::Single(index) => {
                        if self.num_successors_artifact.is_empty() {
                            self.num_successors_artifact = vec![quote!(1)];
                        } else {
                            self.num_successors_artifact.push(quote!(+1));
                        }
                        self.get_successor_artifact.push(quote! {
                            #index => Some(&self.#ident)
                        });
                        self.set_successor_artifact.push(quote! {
                            #index => Ok(Some(std::mem::replace(&mut self.#ident, value)))
                        });
                        self.is_successor_match = true;
                    }
                },
                OpFieldMeta::Other { .. } => {}
            }
        }

        Ok(())
    }

    fn num_operands_method(&mut self) -> TokenStream {
        let num_operands_method = self.num_operands_artifact.drain(..).collect::<Vec<_>>();
        if num_operands_method.is_empty() {
            quote! {
                fn num_operands(&self) -> usize {
                    0
                }
            }
        } else {
            quote! {
                fn num_operands(&self) -> usize {
                    #(#num_operands_method)*
                }
            }
        }
    }

    fn get_operand_method(&mut self) -> TokenStream {
        let get_operand_method = if self.get_operand_artifact.is_empty() {
            quote! {
                None
            }
        } else if self.is_operand_match {
            let artifact = self.get_operand_artifact.drain(..).collect::<Vec<_>>();
            quote! {
                match index {
                    #(#artifact,)*
                    _ => None,
                }
            }
        } else {
            let artifact = self.get_operand_artifact.drain(..).collect::<Vec<_>>();
            let artifact = &artifact[0];
            quote! {
                #artifact
            }
        };

        let get_operand_method = quote! {
            fn get_operand(
                &self,
                index: usize
            ) -> Option<::orzir_core::ArenaPtr<::orzir_core::Value>> {
                #get_operand_method
            }
        };

        get_operand_method
    }

    fn set_operand_method(&mut self) -> TokenStream {
        let set_operand_method = if self.set_operand_artifact.is_empty() {
            quote! {
                ::anyhow::bail!("index out of bounds");
            }
        } else if self.is_operand_match {
            let artifact = self.set_operand_artifact.drain(..).collect::<Vec<_>>();
            quote! {
                match index {
                    #(#artifact,)*
                    _ => Err(::anyhow::anyhow!("index out of bounds"))
                }
            }
        } else {
            let artifact = self.set_operand_artifact.drain(..).collect::<Vec<_>>();
            let artifact = &artifact[0];
            quote! {
                #artifact
            }
        };

        let set_operand_method = quote! {
            fn set_operand(
                &mut self,
                index: usize,
                value: ::orzir_core::ArenaPtr<::orzir_core::Value>
            ) -> ::anyhow::Result<Option<::orzir_core::ArenaPtr<::orzir_core::Value>>> {
                #set_operand_method
            }
        };

        set_operand_method
    }

    fn num_results_method(&mut self) -> TokenStream {
        let num_results_method = self.num_results_artifact.drain(..).collect::<Vec<_>>();
        if num_results_method.is_empty() {
            quote! {
                fn num_results(&self) -> usize {
                    0
                }
            }
        } else {
            quote! {
                fn num_results(&self) -> usize {
                    #(#num_results_method)*
                }
            }
        }
    }

    fn get_result_method(&mut self) -> TokenStream {
        let get_result_method = if self.get_result_artifact.is_empty() {
            quote! {
                None
            }
        } else if self.is_result_match {
            let artifact = self.get_result_artifact.drain(..).collect::<Vec<_>>();
            quote! {
                match index {
                    #(#artifact,)*
                    _ => None,
                }
            }
        } else {
            let artifact = self.get_result_artifact.drain(..).collect::<Vec<_>>();
            let artifact = &artifact[0];
            quote! {
                #artifact
            }
        };

        let get_result_method = quote! {
            fn get_result(
                &self,
                index: usize
            ) -> Option<::orzir_core::ArenaPtr<::orzir_core::Value>> {
                #get_result_method
            }
        };

        get_result_method
    }

    fn set_result_method(&mut self) -> TokenStream {
        let set_result_method = if self.set_result_artifact.is_empty() {
            quote! {
                ::anyhow::bail!("index out of bounds");
            }
        } else if self.is_result_match {
            let artifact = self.set_result_artifact.drain(..).collect::<Vec<_>>();
            quote! {
                match index {
                    #(#artifact,)*
                    _ => Err(::anyhow::anyhow!("index out of bounds"))
                }
            }
        } else {
            let artifact = self.set_result_artifact.drain(..).collect::<Vec<_>>();
            let artifact = &artifact[0];
            quote! {
                #artifact
            }
        };

        let set_result_method = quote! {
            fn set_result(
                &mut self,
                index: usize,
                value: ::orzir_core::ArenaPtr<::orzir_core::Value>
            ) -> ::anyhow::Result<Option<::orzir_core::ArenaPtr<::orzir_core::Value>>> {
                #set_result_method
            }
        };

        set_result_method
    }

    fn num_regions_method(&mut self) -> TokenStream {
        let num_regions_method = self.num_regions_artifact.drain(..).collect::<Vec<_>>();
        if num_regions_method.is_empty() {
            quote! {
                fn num_regions(&self) -> usize {
                    0
                }
            }
        } else {
            quote! {
                fn num_regions(&self) -> usize {
                    #(#num_regions_method)*
                }
            }
        }
    }

    fn get_region_method(&mut self) -> TokenStream {
        let get_region_method = if self.get_region_artifact.is_empty() {
            quote! {
                None
            }
        } else if self.is_region_match {
            let artifact = self.get_region_artifact.drain(..).collect::<Vec<_>>();
            quote! {
                match index {
                    #(#artifact,)*
                    _ => None,
                }
            }
        } else {
            let artifact = self.get_region_artifact.drain(..).collect::<Vec<_>>();
            let artifact = &artifact[0];
            quote! {
                #artifact
            }
        };

        let get_region_method = quote! {
            fn get_region(
                &self,
                index: usize
            ) -> Option<::orzir_core::ArenaPtr<::orzir_core::Region>> {
                #get_region_method
            }
        };

        get_region_method
    }

    fn set_region_method(&mut self) -> TokenStream {
        let set_region_method = if self.set_region_artifact.is_empty() {
            quote! {
                ::anyhow::bail!("index out of bounds");
            }
        } else if self.is_region_match {
            let artifact = self.set_region_artifact.drain(..).collect::<Vec<_>>();
            quote! {
                match index {
                    #(#artifact,)*
                    _ => Err(::anyhow::anyhow!("index out of bounds"))
                }
            }
        } else {
            let artifact = self.set_region_artifact.drain(..).collect::<Vec<_>>();
            let artifact = &artifact[0];
            quote! {
                #artifact
            }
        };

        let set_region_method = quote! {
            fn set_region(
                &mut self,
                index: usize,
                value: ::orzir_core::ArenaPtr<::orzir_core::Region>
            ) -> ::anyhow::Result<Option<::orzir_core::ArenaPtr<::orzir_core::Region>>> {
                #set_region_method
            }
        };

        set_region_method
    }

    fn num_successors_method(&mut self) -> TokenStream {
        let num_successors_method = self.num_successors_artifact.drain(..).collect::<Vec<_>>();
        if num_successors_method.is_empty() {
            quote! {
                fn num_successors(&self) -> usize {
                    0
                }
            }
        } else {
            quote! {
                fn num_successors(&self) -> usize {
                    #(#num_successors_method)*
                }
            }
        }
    }

    fn get_successor_method(&mut self) -> TokenStream {
        let get_successor_method = if self.get_successor_artifact.is_empty() {
            quote! {
                None
            }
        } else if self.is_successor_match {
            let artifact = self.get_successor_artifact.drain(..).collect::<Vec<_>>();
            quote! {
                match index {
                    #(#artifact,)*
                    _ => None,
                }
            }
        } else {
            let artifact = self.get_successor_artifact.drain(..).collect::<Vec<_>>();
            let artifact = &artifact[0];
            quote! {
                #artifact
            }
        };

        let get_successor_method = quote! {
            fn get_successor(
                &self,
                index: usize
            ) -> Option<&::orzir_core::Successor> {
                #get_successor_method
            }
        };

        get_successor_method
    }

    fn set_successor_method(&mut self) -> TokenStream {
        let set_successor_method = if self.set_successor_artifact.is_empty() {
            quote! {
                ::anyhow::bail!("index out of bounds");
            }
        } else if self.is_successor_match {
            let artifact = self.set_successor_artifact.drain(..).collect::<Vec<_>>();
            quote! {
                match index {
                    #(#artifact,)*
                    _ => Err(::anyhow::anyhow!("index out of bounds"))
                }
            }
        } else {
            let artifact = self.set_successor_artifact.drain(..).collect::<Vec<_>>();
            let artifact = &artifact[0];
            quote! {
                #artifact
            }
        };

        let set_successor_method = quote! {
            fn set_successor(
                &mut self,
                index: usize,
                value: ::orzir_core::Successor
            ) -> ::anyhow::Result<Option<::orzir_core::Successor>> {
                #set_successor_method
            }
        };

        set_successor_method
    }

    fn op_trait_impl(&mut self) -> syn::Result<TokenStream> {
        self.verify()?;
        self.generate_artifacts()?;

        let num_operands_method = self.num_operands_method();
        let get_operand_method = self.get_operand_method();
        let set_operand_method = self.set_operand_method();

        let num_results_method = self.num_results_method();
        let get_result_method = self.get_result_method();
        let set_result_method = self.set_result_method();

        let num_regions_method = self.num_regions_method();
        let get_region_method = self.get_region_method();
        let set_region_method = self.set_region_method();

        let num_successors_method = self.num_successors_method();
        let get_successor_method = self.get_successor_method();
        let set_successor_method = self.set_successor_method();

        let metadata_methods = &self.metadata_artifact;

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

    fn op_ctor(&self) -> TokenStream {
        let ctor_args = self
            .fields
            .iter()
            .filter(|field| !matches!(field, OpFieldMeta::Metadata { .. }))
            .map(|field| {
                let ident = match field {
                    OpFieldMeta::Metadata { ident } => ident,
                    OpFieldMeta::Result { ident, .. } => ident,
                    OpFieldMeta::Operand { ident, .. } => ident,
                    OpFieldMeta::Region { ident, .. } => ident,
                    OpFieldMeta::Successor { ident, .. } => ident,
                    OpFieldMeta::Other { ident, .. } => ident,
                };
                let ty = match field {
                    OpFieldMeta::Metadata { .. } => quote! { ::orzir_core::OpMetadata },
                    OpFieldMeta::Result { index, .. } | OpFieldMeta::Operand { index, .. } => {
                        match index {
                            IndexKind::All => {
                                quote! { Vec<::orzir_core::ArenaPtr<::orzir_core::Value>> }
                            }
                            IndexKind::Single(_) => {
                                quote! { ::orzir_core::ArenaPtr<::orzir_core::Value> }
                            }
                        }
                    }
                    OpFieldMeta::Region { index, .. } => match index {
                        IndexKind::All => {
                            quote! { Vec<::orzir_core::ArenaPtr<::orzir_core::Region>> }
                        }
                        IndexKind::Single(_) => {
                            quote! { ::orzir_core::ArenaPtr<::orzir_core::Region> }
                        }
                    },
                    OpFieldMeta::Successor { index, .. } => match index {
                        IndexKind::All => quote! { Vec<::orzir_core::Successor> },
                        IndexKind::Single(_) => quote! { ::orzir_core::Successor },
                    },
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
                OpFieldMeta::Result { ident, .. }
                | OpFieldMeta::Operand { ident, .. }
                | OpFieldMeta::Region { ident, .. }
                | OpFieldMeta::Successor { ident, .. }
                | OpFieldMeta::Other { ident, .. } => ident,
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
        impl ::orzir_core::VerifyInterfaces for #ident {
            fn verify_interfaces(&self, ctx: &::orzir_core::Context) -> ::anyhow::Result<()> {
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
