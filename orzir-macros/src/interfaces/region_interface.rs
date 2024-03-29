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

struct FieldMeta {
    ident: syn::Ident,
    index: IndexKind,
}

#[derive(Default)]
struct DeriveInfo {
    fields: Vec<FieldMeta>,

    num_artifact: TokenStream,
    get_artifacts: Vec<TokenStream>,
    set_artifacts: Vec<TokenStream>,

    need_match: bool,
}

impl DeriveInfo {
    fn from_ast(ast: &syn::DeriveInput) -> syn::Result<Self> {
        let mut info = DeriveInfo::default();

        match &ast.data {
            syn::Data::Struct(s) => match &s.fields {
                syn::Fields::Named(fields) => {
                    for field in fields.named.iter() {
                        let mut index = None;
                        for attr in field.attrs.iter() {
                            let ident = attr.path().get_ident();
                            if let Some(ident) = ident {
                                if ident == "region" {
                                    index = Some(attr.parse_args::<IndexKind>()?);
                                }
                            }
                        }

                        if index.is_none() {
                            continue;
                        }

                        let index = index.unwrap();

                        let ty = &field.ty;

                        match index {
                            IndexKind::All => {
                                if let syn::Type::Path(ref path) = ty {
                                    if let Some(segment) = path.path.segments.last() {
                                        if segment.ident != "Vec" {
                                            return Err(syn::Error::new_spanned(
                                                ty,
                                                "expect type `Vec<ArenaPtr<Region>>`",
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
                                                "expect type `ArenaPtr<Region>`",
                                            ));
                                        }
                                    }
                                }
                            }
                        }

                        info.fields.push(FieldMeta {
                            ident: field.ident.clone().unwrap(),
                            index,
                        });
                    }
                }
                _ => {
                    return Err(syn::Error::new_spanned(
                        ast,
                        "only named fields are supported to derive `RegionInterface`",
                    ))
                }
            },
            _ => {
                return Err(syn::Error::new_spanned(
                    ast,
                    "only structs are supported to derive `RegionInterface`",
                ))
            }
        }

        Ok(info)
    }

    fn verify(&self) -> syn::Result<()> {
        // only allow one `...` field, and cannot coexist with other fields
        let mut index_kind = None;

        for field in self.fields.iter() {
            match field.index {
                IndexKind::All => {
                    if index_kind.is_some() {
                        return Err(syn::Error::new_spanned(
                            field.ident.clone(),
                            "only one `...` field is allowed",
                        ));
                    } else {
                        index_kind = Some(IndexKind::All);
                    }
                }
                IndexKind::Single(i) => {
                    if let Some(IndexKind::All) = index_kind {
                        return Err(syn::Error::new_spanned(
                            field.ident.clone(),
                            "cannot coexist with `...` field",
                        ));
                    } else {
                        index_kind = Some(IndexKind::Single(i));
                    }
                }
            }
        }

        Ok(())
    }

    fn genrate_artifacts(&mut self) -> syn::Result<()> {
        let mut cnt = 0;

        self.num_artifact = quote! {
            0
        };

        if self.fields.is_empty() {
            self.get_artifacts = vec![quote! {
                None
            }];
            self.set_artifacts = vec![quote! {
                ::anyhow::bail!("inedx out of bounds");
            }];
        }

        for field in &self.fields {
            let ident = &field.ident;
            let index = &field.index;

            match index {
                IndexKind::All => {
                    self.num_artifact = quote! {
                        self.#ident.len()
                    };
                    self.get_artifacts = vec![quote! {
                        self.#ident.get(index).copied()
                    }];
                    self.set_artifacts = vec![quote! {
                        if index > self.#ident.len() {
                            ::anyhow::bail!("index out of bounds")
                        }
                        if index == self.#ident.len() {
                            self.#ident.push(region);
                            Ok(None)
                        } else {
                            Ok(Some(std::mem::replace(&mut self.#ident[index], region)))
                        }
                    }]
                }
                IndexKind::Single(i) => {
                    cnt += 1;
                    self.get_artifacts.push(quote! {
                        #i => Some(self.#ident)
                    });
                    self.set_artifacts.push(quote! {
                        #i => Ok(Some(std::mem::replace(&mut self.#ident, region)))
                    });
                    self.need_match = true;
                }
            }
        }

        if self.need_match {
            self.num_artifact = quote! {
                #cnt
            };
        }

        Ok(())
    }

    fn num_method(&self) -> TokenStream {
        let artifact = &self.num_artifact;
        quote! {
            fn num_regions(&self) -> usize {
                #artifact as usize
            }
        }
    }

    fn get_method(&mut self) -> TokenStream {
        let mut artifacts = self.get_artifacts.drain(..).collect::<Vec<_>>();

        if self.need_match {
            quote! {
                fn get_region(&self, index: usize) -> Option<::orzir_core::ArenaPtr<::orzir_core::Region>> {
                    match index {
                        #(#artifacts,)*
                        _ => None
                    }
                }
            }
        } else {
            let artifact = artifacts.pop().unwrap();
            quote! {
                fn get_region(&self, index: usize) -> Option<::orzir_core::ArenaPtr<::orzir_core::Region>> {
                    #artifact
                }
            }
        }
    }

    fn set_method(&mut self) -> TokenStream {
        let mut artifacts = self.set_artifacts.drain(..).collect::<Vec<_>>();

        if self.need_match {
            quote! {
                fn set_region(
                    &mut self,
                    index: usize,
                    region: ::orzir_core::ArenaPtr<::orzir_core::Region>,
                ) -> ::anyhow::Result<Option<::orzir_core::ArenaPtr<::orzir_core::Region>>> {
                    match index {
                        #(#artifacts,)*
                        _ => ::anyhow::bail!("index out of bounds")
                    }
                }
            }
        } else {
            let artifact = artifacts.pop().unwrap();
            quote! {
                fn set_region(
                    &mut self,
                    index: usize,
                    region: ::orzir_core::ArenaPtr<::orzir_core::Region>,
                ) -> ::anyhow::Result<Option<::orzir_core::ArenaPtr<::orzir_core::Region>>> {
                    #artifact
                }
            }
        }
    }
}

pub fn derive_region_interface_impl(item: TokenStream) -> syn::Result<TokenStream> {
    let ast = syn::parse2::<syn::DeriveInput>(item)?;
    let mut info = DeriveInfo::from_ast(&ast)?;

    let ident = &ast.ident;

    info.verify()?;
    info.genrate_artifacts()?;

    let num_method = info.num_method();
    let get_method = info.get_method();
    let set_method = info.set_method();

    let expanded = quote! {
        impl ::orzir_core::RegionInterface for #ident {
            #num_method
            #get_method
            #set_method
        }
    };

    Ok(expanded)
}

#[cfg(test)]
mod tests {
    use quote::quote;

    use super::derive_region_interface_impl;

    #[test]
    fn test_0() {
        let src = quote! {
            #[derive(Op, RegionInterface)]
            #[mnemonic = "func.return"]
            // #[verifiers(NumResults<0>, VariadicOperands, NumRegions<0>, IsTerminator)]
            pub struct ReturnOp {
                #[metadata]
                metadata: OpMetadata,

                #[operand(...)]
                operands: Vec<ArenaPtr<Value>>,

                #[region(0)]
                x: ArenaPtr<Region>,

                #[region(1)]
                y: ArenaPtr<Region>,

                #[region(2)]
                z: ArenaPtr<Region>,
            }
        };

        let output = derive_region_interface_impl(src).unwrap();

        println!("{}", output);

        let ast = syn::parse_file(&output.to_string()).unwrap();

        let ast = prettyplease::unparse(&ast);

        println!("{}", ast);
    }
}
