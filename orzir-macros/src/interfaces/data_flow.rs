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
    /// The result field.
    Result {
        /// The corresponding field ident.
        ident: syn::Ident,
        /// The index kind.
        index: IndexKind,
    },
    /// The operand field.
    Operand {
        /// The corresponding field ident.
        ident: syn::Ident,
        /// The index kind.
        index: IndexKind,
    },
}

#[derive(Default)]
struct OpInfo {
    /// Fields
    fields: Vec<OpFieldMeta>,

    /// The artifact for the number of operands.
    num_operands_artifact: TokenStream,
    /// The artifact for the number of results.
    num_results_artifact: TokenStream,

    /// The artifact for getting operands.
    get_operand_artifact: Vec<TokenStream>,
    /// The artifact for getting results.
    get_result_artifact: Vec<TokenStream>,

    /// The artifact for setting operands.
    set_operand_artifact: Vec<TokenStream>,
    /// The artifact for setting results.
    set_result_artifact: Vec<TokenStream>,

    /// Whether the operand index will be matched to get/set.
    operand_need_match: bool,
    /// Whether the result index will be matched to get/set.
    result_need_match: bool,
}

impl OpInfo {
    /// Get the info from a [`syn::DeriveInput`].
    fn from_ast(ast: &syn::DeriveInput) -> syn::Result<Self> {
        let mut info = Self::default();

        match &ast.data {
            syn::Data::Struct(s) => match &s.fields {
                syn::Fields::Named(fields) => {
                    for field in fields.named.iter() {
                        let mut field_meta = None;

                        for attr in field.attrs.iter() {
                            let ident = attr.path().get_ident();
                            if let Some(ident) = ident {
                                match ident.to_string().as_str() {
                                    "result" => {
                                        let index = attr.parse_args::<IndexKind>()?;
                                        field_meta = Some(OpFieldMeta::Result {
                                            ident: field.ident.clone().unwrap(),
                                            index,
                                        });
                                    }
                                    "operand" => {
                                        let index = attr.parse_args::<IndexKind>()?;
                                        field_meta = Some(OpFieldMeta::Operand {
                                            ident: field.ident.clone().unwrap(),
                                            index,
                                        });
                                    }
                                    _ => {}
                                }
                            }
                        }

                        if field_meta.is_none() {
                            continue;
                        }

                        let field_meta = field_meta.unwrap();

                        let ty = &field.ty;

                        // basic type checking.
                        match field_meta {
                            OpFieldMeta::Result { index, .. }
                            | OpFieldMeta::Operand { index, .. } => match index {
                                IndexKind::All => {
                                    if let syn::Type::Path(ref path) = ty {
                                        if let Some(segment) = path.path.segments.last() {
                                            if segment.ident != "Vec" {
                                                return Err(syn::Error::new_spanned(
                                                    ty,
                                                    "expect type `Vec<ArenaPtr<Value>>`",
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
                                                    "expect type `ArenaPtr<Value>`",
                                                ));
                                            }
                                        }
                                    }
                                }
                            },
                        }

                        info.fields.push(field_meta);
                    }
                }
                _ => {
                    return Err(syn::Error::new_spanned(
                        ast,
                        "only named fields are supported to derive `DataFlow`",
                    ))
                }
            },
            _ => {
                return Err(syn::Error::new_spanned(
                    ast,
                    "only structs are supported to derive `DataFlow`",
                ))
            }
        }

        Ok(info)
    }

    /// To verify the indices of entities are valid
    fn verify(&self) -> syn::Result<()> {
        let mut result = None;
        let mut operand = None;

        for field in &self.fields {
            match field {
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
            }
        }

        Ok(())
    }

    /// Generate all artifact for different entities and methods.
    fn generate_artifacts(&mut self) -> syn::Result<()> {
        let mut operand_cnt = 0;
        let mut result_cnt = 0;

        self.num_operands_artifact = quote! { 0 };
        self.num_results_artifact = quote! { 0 };

        for field in &self.fields {
            match field {
                OpFieldMeta::Operand { ident, index } => match index {
                    IndexKind::All => {
                        self.num_operands_artifact = quote! {
                            self.#ident.len()
                        };
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
                        operand_cnt += 1;
                        self.get_operand_artifact.push(quote! {
                            #index => Some(self.#ident)
                        });
                        self.set_operand_artifact.push(quote! {
                            #index => Ok(Some(std::mem::replace(&mut self.#ident, value)))
                        });
                        self.operand_need_match = true;
                    }
                },
                OpFieldMeta::Result { ident, index } => match index {
                    IndexKind::All => {
                        self.num_results_artifact = quote! {
                            self.#ident.len()
                        };
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
                        result_cnt += 1;
                        self.get_result_artifact.push(quote! {
                            #index => Some(self.#ident)
                        });
                        self.set_result_artifact.push(quote! {
                            #index => Ok(Some(std::mem::replace(&mut self.#ident, value)))
                        });
                        self.result_need_match = true;
                    }
                },
            }
        }

        if self.operand_need_match {
            self.num_operands_artifact = quote! { #operand_cnt };
        }

        if self.result_need_match {
            self.num_results_artifact = quote! { #result_cnt };
        }

        Ok(())
    }

    fn num_operands_method(&self) -> TokenStream {
        let artifact = &self.num_operands_artifact;
        quote! {
            fn num_operands(&self) -> usize {
                #artifact as usize
            }
        }
    }

    fn get_operand_method(&mut self) -> TokenStream {
        let get_operand_method = if self.get_operand_artifact.is_empty() {
            quote! {
                None
            }
        } else if self.operand_need_match {
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
        } else if self.operand_need_match {
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

    fn num_results_method(&self) -> TokenStream {
        let artifact = &self.num_results_artifact;
        quote! {
            fn num_results(&self) -> usize {
                #artifact as usize
            }
        }
    }

    fn get_result_method(&mut self) -> TokenStream {
        let get_result_method = if self.get_result_artifact.is_empty() {
            quote! {
                None
            }
        } else if self.result_need_match {
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
        } else if self.result_need_match {
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
}

pub fn derive_data_flow_impl(input: TokenStream) -> syn::Result<TokenStream> {
    let ast = syn::parse2::<syn::DeriveInput>(input).unwrap();
    let mut info = OpInfo::from_ast(&ast)?;

    info.verify()?;
    info.generate_artifacts()?;

    let ident = &ast.ident;

    let num_operands_method = info.num_operands_method();
    let get_operand_method = info.get_operand_method();
    let set_operand_method = info.set_operand_method();

    let num_results_method = info.num_results_method();
    let get_result_method = info.get_result_method();
    let set_result_method = info.set_result_method();

    let expaned = quote! {
        impl ::orzir_core::DataFlow for #ident {
            #num_operands_method
            #get_operand_method
            #set_operand_method

            #num_results_method
            #get_result_method
            #set_result_method
        }
    };

    Ok(expaned)
}

#[cfg(test)]
mod tests {
    use quote::quote;

    use super::derive_data_flow_impl;

    #[test]
    fn test_0() {
        let src = quote! {
            #[derive(Op)]
            #[mnemonic = "func.return"]
            // #[verifiers(NumResults<0>, VariadicOperands, NumRegions<0>, IsTerminator)]
            pub struct ReturnOp {
                #[metadata]
                metadata: OpMetadata,

                #[operand(0)]
                x: ArenaPtr<Value>,

                #[operand(1)]
                y: ArenaPtr<Value>,

                #[result(0)]
                z: ArenaPtr<Value>,

                #[result(1)]
                w: ArenaPtr<Value>,

                #[result(2)]
                v: ArenaPtr<Value>,
            }
        };

        let output = derive_data_flow_impl(src).unwrap();

        println!("{}", output);

        let ast = syn::parse_file(&output.to_string()).unwrap();

        let ast = prettyplease::unparse(&ast);

        println!("{}", ast);
    }
}
