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

fn derive_struct(derive_info: &OpDeriveInfo, artifacts: &mut DeriveArtifacts) -> syn::Result<()> {
    artifacts.num_impl = quote! { 0 };
    artifacts.getter_impl = TokenStream::new();
    artifacts.setter_impl = TokenStream::new();

    artifacts.getter_has_default_arm = false;
    artifacts.setter_has_default_arm = false;

    for (ident, meta) in derive_info.fields.iter() {
        if !matches!(meta, OpFieldMeta::Successor(_)) {
            continue;
        }

        let index = match &meta {
            OpFieldMeta::Successor(index) => index,
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
                    .extend(quote! { _ => #field.get(index) });
                artifacts.setter_impl.extend(quote! {
                    _ => {
                        if index > #field.len() {
                            panic!("index out of bounds");
                        }
                        if index == #field.len() {
                            #field.push(successor);
                            None
                        } else {
                            Some(std::mem::replace(&mut #field[index], successor))
                        }
                    }
                });
                artifacts.getter_has_default_arm = true;
                artifacts.setter_has_default_arm = true;
            }
            IndexKind::Range(start, end) => {
                match end {
                    Some(end) => {
                        artifacts.num_impl.extend(quote! { + #end - #start });
                        artifacts
                            .getter_impl
                            .extend(quote! { #start..=#end => #field.get(index - #start), });
                        artifacts.setter_impl.extend(quote! {
                            #start..=#end => {
                                if index > #end {
                                    panic!("index out of bounds");
                                }
                                Some(std::mem::replace(&mut #field[index - #start], successor))
                            }
                        });
                    }
                    None => {
                        artifacts.num_impl.extend(quote! { + #field.len() });
                        artifacts
                            .getter_impl
                            .extend(quote! { #start.. => #field.get(index - #start), });
                        artifacts.setter_impl.extend(quote! {
                            #start.. => {
                                if index - #start > #field.len() {
                                    panic!("index out of bounds");
                                }
                                if index - #start == #field.len() {
                                    #field.push(successor);
                                    None
                                } else {
                                    Some(std::mem::replace(&mut #field[index - #start], successor))
                                }
                            }
                        });
                    }
                }
            }
            IndexKind::Single(idx) => {
                artifacts.num_impl.extend(quote! { + 1 });
                artifacts.getter_impl.extend(quote! {
                    #idx => Some(&#field),
                });
                artifacts.setter_impl.extend(quote! {
                    #idx => Some(std::mem::replace(&mut #field, successor)),
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
    let artifacts = &mut DeriveArtifacts::default();

    derive_struct(&derive_info, artifacts)?;

    let num_impl = &artifacts.num_impl;
    let num_impl = quote! {
        fn num_successors(&self) -> usize {
            #num_impl
        }
    };
    let getter_impl = &artifacts.getter_impl;
    let getter_impl = quote! {
        fn get_successor(&self, index: usize) -> Option<&::orzir_core::Successor> {
            #getter_impl
        }
    };
    let setter_impl = &artifacts.setter_impl;
    let setter_impl = quote! {
        fn set_successor(
            &mut self,
            index: usize,
            successor: ::orzir_core::Successor,
        ) -> Option<::orzir_core::Successor> {
            #setter_impl
        }
    };
    let ident = &ast.ident;
    let output = quote! {
        impl ::orzir_core::ControlFlow for #ident {
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

    use crate::interfaces::control_flow::derive_impl;

    #[test]
    fn test_0() {
        let src = quote! {
            #[mnemonic = "test.test"]
            pub struct TestOp {
                #[metadata]
                metadata: OpMetadata,

                #[successor(0)]
                succ: Successor,
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
