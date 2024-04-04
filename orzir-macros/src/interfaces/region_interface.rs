use proc_macro2::{Span, TokenStream};
use quote::quote;

use crate::op::{FieldIdent, IndexKind, OpDeriveInfo, OpFieldMeta, RegionMeta};

#[derive(Default)]
struct DeriveArtifacts {
    /// The `num_result/operands` method.
    num_impl: TokenStream,
    /// The `get_result/operand` method.
    getter_impl: TokenStream,
    /// The `set_result/operand` method.
    setter_impl: TokenStream,

    getter_has_default_arm: bool,
    setter_has_default_arm: bool,
}

fn derive_struct(derive_info: &OpDeriveInfo, artifacts: &mut DeriveArtifacts) -> syn::Result<()> {
    artifacts.num_impl = quote! { 0 };
    artifacts.getter_impl = TokenStream::new();
    artifacts.setter_impl = TokenStream::new();

    artifacts.getter_has_default_arm = false;
    artifacts.setter_has_default_arm = false;

    for (ident, meta) in derive_info.fields.iter() {
        if !matches!(meta, OpFieldMeta::Region(_)) {
            continue;
        }

        let index = match &meta {
            OpFieldMeta::Region(RegionMeta { index, .. }) => index,
            _ => unreachable!(),
        };

        let field = match &ident {
            FieldIdent::Ident(ident) => {
                let ident = syn::Ident::new(ident, Span::call_site());
                quote! { self.#ident }
            }
            FieldIdent::Index(index) => {
                let index = syn::Index::from(*index);
                quote! { self.#index }
            }
        };

        match index {
            IndexKind::All => {
                artifacts.num_impl.extend(quote! { + #field.len() });
                artifacts
                    .getter_impl
                    .extend(quote! { _ => #field.get(index).copied() });
                artifacts.setter_impl.extend(quote! {
                    _ => {
                        if index > #field.len() {
                            panic!("index out of bounds");
                        }
                        if index == #field.len() {
                            #field.push(region);
                            None
                        } else {
                            Some(std::mem::replace(&mut #field[index], region))
                        }
                    }
                });
                artifacts.getter_has_default_arm = true;
                artifacts.setter_has_default_arm = true;
            }
            IndexKind::Range(start, end) => match end {
                Some(end) => {
                    artifacts.num_impl.extend(quote! { + #end - #start });
                    artifacts
                        .getter_impl
                        .extend(quote! { #start..=#end => #field.get(index - #start).copied(), });
                    artifacts.setter_impl.extend(quote! {
                        #start..=#end => {
                            if index > #end {
                                panic!("index out of bounds");
                            }
                            Some(std::mem::replace(&mut #field[index - #start], region))
                        }
                    });
                }
                None => {
                    artifacts.num_impl.extend(quote! { + #field.len() });
                    artifacts
                        .getter_impl
                        .extend(quote! { #start.. => #field.get(index - #start).copied(), });
                    artifacts.setter_impl.extend(quote! {
                        #start.. => {
                            if index - #start > #field.len() {
                                panic!("index out of bounds");
                            }
                            if index - #start == #field.len() {
                                #field.push(region);
                                None
                            } else {
                                Some(std::mem::replace(&mut #field[index - #start], region))
                            }
                        }
                    });
                }
            },
            IndexKind::Single(idx) => {
                artifacts.num_impl.extend(quote! { + 1 });
                artifacts.getter_impl.extend(quote! {
                    #idx => Some(#field),
                });
                artifacts.setter_impl.extend(quote! {
                    #idx => Some(std::mem::replace(&mut #field, region)),
                });
            }
        }
    }

    if !artifacts.getter_has_default_arm {
        artifacts.getter_impl.extend(quote! {
            _ => None,
        });
    }

    if !artifacts.setter_has_default_arm {
        artifacts.setter_impl.extend(quote! {
            _ => None,
        });
    }

    let getter_impl = &artifacts.getter_impl;
    let setter_impl = &artifacts.setter_impl;

    artifacts.getter_impl = quote! {
        match index {
            #getter_impl
        }
    };

    artifacts.setter_impl = quote! {
        match index {
            #setter_impl
        }
    };

    Ok(())
}

pub fn derive_impl(ast: &syn::DeriveInput) -> syn::Result<TokenStream> {
    let derive_info = OpDeriveInfo::from_ast(ast)?;
    let mut artifacts = DeriveArtifacts::default();

    derive_struct(&derive_info, &mut artifacts)?;

    let num_impl = artifacts.num_impl;
    let num_impl = quote! {
        fn num_regions(&self) -> usize {
            #num_impl
        }
    };
    let getter_impl = artifacts.getter_impl;
    let getter_impl = quote! {
        fn get_region(&self, index: usize) -> Option<::orzir_core::ArenaPtr<::orzir_core::Region>> {
            #getter_impl
        }
    };
    let setter_impl = artifacts.setter_impl;
    let setter_impl = quote! {
        fn set_region(
            &mut self,
            index: usize,
            region: ::orzir_core::ArenaPtr<::orzir_core::Region>,
        ) -> Option<::orzir_core::ArenaPtr<::orzir_core::Region>> {
            #setter_impl
        }
    };
    let ident = &ast.ident;
    let output = quote! {
        impl ::orzir_core::RegionInterface for #ident {
            #num_impl
            #getter_impl
            #setter_impl
        }
    };

    Ok(output)
}

#[cfg(test)]
mod tests {
    use quote::quote;

    use crate::interfaces::region_interface::derive_impl;

    #[test]
    fn test_0() {
        let src = quote! {
            #[mnemonic = "test.test"]
            pub struct TestOp {
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
        let ast = syn::parse2::<syn::DeriveInput>(src).unwrap();
        let output = derive_impl(&ast).unwrap();
        println!("{}", output);
        let ast = syn::parse_file(&output.to_string()).unwrap();
        let ast = prettyplease::unparse(&ast);
        println!("{}", ast);
    }
}
