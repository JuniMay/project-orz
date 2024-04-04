use proc_macro2::{Span, TokenStream};
use quote::quote;

use crate::op::{FieldIdent, IndexKind, OpDeriveInfo, OpFieldMeta};

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

fn derive_struct(
    derive_info: &OpDeriveInfo,
    artifacts: &mut DeriveArtifacts,
    attr_name: &str,
) -> syn::Result<()> {
    artifacts.num_impl = quote! { 0 };
    artifacts.getter_impl = TokenStream::new();
    artifacts.setter_impl = TokenStream::new();

    artifacts.getter_has_default_arm = false;
    artifacts.setter_has_default_arm = false;

    for (ident, meta) in derive_info.fields.iter() {
        match attr_name {
            "result" => {
                if !matches!(meta, OpFieldMeta::Result(_)) {
                    continue;
                }
            }
            "operand" => {
                if !matches!(meta, OpFieldMeta::Operand(_)) {
                    continue;
                }
            }
            _ => unreachable!(),
        }

        let index = match &meta {
            OpFieldMeta::Result(index) => index,
            OpFieldMeta::Operand(index) => index,
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
                            #field.push(value);
                            None
                        } else {
                            Some(std::mem::replace(&mut #field[index], value))
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
                            Some(std::mem::replace(&mut #field[index - #start], value))
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
                                #field.push(value);
                                None
                            } else {
                                Some(std::mem::replace(&mut #field[index - #start], value))
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
                    #idx => Some(std::mem::replace(&mut #field, value)),
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

fn derive_impl_helper(ast: &syn::DeriveInput, attr_name: &str) -> syn::Result<TokenStream> {
    let derive_info = OpDeriveInfo::from_ast(ast)?;
    let mut artifacts = DeriveArtifacts::default();

    derive_struct(&derive_info, &mut artifacts, attr_name)?;

    let num_method_name =
        syn::Ident::new(format!("num_{}s", attr_name).as_str(), Span::call_site());
    let getter_method_name =
        syn::Ident::new(format!("get_{}", attr_name).as_str(), Span::call_site());
    let setter_method_name =
        syn::Ident::new(format!("set_{}", attr_name).as_str(), Span::call_site());

    let num_impl = artifacts.num_impl;
    let num_impl = quote! {
        fn #num_method_name(&self) -> usize {
            #num_impl
        }
    };
    let getter_impl = artifacts.getter_impl;
    let getter_impl = quote! {
        fn #getter_method_name(&self, index: usize) -> Option<::orzir_core::ArenaPtr<::orzir_core::Value>> {
            #getter_impl
        }
    };
    let setter_impl = artifacts.setter_impl;
    let setter_impl = quote! {
        fn #setter_method_name(
            &mut self,
            index: usize,
            value: ::orzir_core::ArenaPtr<::orzir_core::Value>,
        ) -> Option<::orzir_core::ArenaPtr<::orzir_core::Value>> {
            #setter_impl
        }
    };

    let impls = quote! {
        #num_impl
        #getter_impl
        #setter_impl
    };

    Ok(impls)
}

pub fn derive_impl(ast: &syn::DeriveInput) -> syn::Result<TokenStream> {
    let operand_impls = derive_impl_helper(ast, "operand")?;
    let result_impls = derive_impl_helper(ast, "result")?;

    let ident = &ast.ident;

    let output = quote! {
        impl ::orzir_core::DataFlow for #ident {
            #operand_impls
            #result_impls
        }
    };

    Ok(output)
}

#[cfg(test)]
mod tests {
    use quote::quote;

    use crate::interfaces::data_flow::derive_impl;

    #[test]
    fn test_0() {
        let src = quote! {
            #[mnemonic = "test.test"]
            pub struct TestOp {
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
        let ast = syn::parse2::<syn::DeriveInput>(src).unwrap();
        let output = derive_impl(&ast).unwrap();
        println!("{}", output);
        let ast = syn::parse_file(&output.to_string()).unwrap();
        let ast = prettyplease::unparse(&ast);
        println!("{}", ast);
    }
}
