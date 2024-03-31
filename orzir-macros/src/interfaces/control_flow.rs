use proc_macro2::TokenStream;
use quote::quote;
use syn::spanned::Spanned;

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

#[derive(Default)]
struct DeriveInfo {
    field_cnt: Option<usize>,
    /// The `num_successors` method.
    num_impl: Option<TokenStream>,
    /// The `get_successor` method.
    getter_impl: Option<TokenStream>,
    /// The `set_successor` method.
    setter_impl: Option<TokenStream>,
    /// If the members are discrete, i.e. they only store a single entity.
    ///
    /// If this is `None`, this is not yet determined.
    discrete: Option<bool>,
}

fn derive_struct(data_struct: &syn::DataStruct, info: &mut DeriveInfo) -> syn::Result<()> {
    for (idx, field) in data_struct.fields.iter().enumerate() {
        let attr = field
            .attrs
            .iter()
            .find(|attr| attr.path().is_ident("successor"));
        if attr.is_none() {
            continue;
        }
        let attr = attr.unwrap();
        let index = attr.parse_args::<IndexKind>()?;
        match (info.discrete, index) {
            (Some(true), IndexKind::All) | (Some(false), IndexKind::Single(_)) => {
                return Err(syn::Error::new(
                    attr.span(),
                    "cannot have both `...` and discrete indices",
                ))
            }
            (Some(false), IndexKind::All) => {
                return Err(syn::Error::new(
                    attr.span(),
                    "cannot have both multiple `...` indices",
                ))
            }
            (_, IndexKind::All) => info.discrete = Some(false),
            (_, IndexKind::Single(_)) => info.discrete = Some(true),
        }

        let field = match &field.ident {
            Some(ident) => quote! { self.#ident },
            None => {
                let index = syn::Index::from(idx);
                quote! { self.#index }
            }
        };

        match index {
            IndexKind::All => {
                info.num_impl = Some(quote! { #field.len() });
                info.getter_impl = Some(quote! { #field.get(index) });
                info.setter_impl = Some(quote! {
                    if index > #field.len() {
                        panic!("index out of bounds");
                    }
                    if index == #field.len() {
                        #field.push(successor);
                        None
                    } else {
                        Some(std::mem::replace(&mut #field[index], successor))
                    }
                });
            }
            IndexKind::Single(idx) => {
                info.field_cnt = Some(info.field_cnt.unwrap_or(0) + 1);

                if info.getter_impl.is_none() {
                    info.getter_impl = Some(TokenStream::new());
                }

                if info.setter_impl.is_none() {
                    info.setter_impl = Some(TokenStream::new());
                }

                if let Some(ref mut method) = info.getter_impl.as_mut() {
                    method.extend(quote! {
                        #idx => Some(&#field),
                    });
                } else {
                    unreachable!()
                }

                if let Some(ref mut method) = info.setter_impl.as_mut() {
                    method.extend(quote! {
                        #idx => Some(std::mem::replace(&mut #field, successor)),
                    });
                } else {
                    unreachable!()
                }
            }
        }
    }

    if let Some(discrete) = info.discrete {
        if discrete {
            let num = info.field_cnt.unwrap();
            info.num_impl = Some(quote! { #num });

            let getters = info.getter_impl.as_mut().unwrap();
            let setters = info.setter_impl.as_mut().unwrap();
            info.getter_impl = Some(quote! {
                match index {
                    #getters
                    _ => None,
                }
            });
            info.setter_impl = Some(quote! {
                match index {
                    #setters
                    _ => None,
                }
            });
        }
    } else {
        info.num_impl = Some(quote! { 0 });
        info.getter_impl = Some(quote! { None });
        info.setter_impl = Some(quote! { panic!("index out of bounds") });
    }

    Ok(())
}

pub fn derive_impl(ast: &syn::DeriveInput) -> syn::Result<TokenStream> {
    let mut info = DeriveInfo::default();

    match &ast.data {
        syn::Data::Struct(data_struct) => {
            derive_struct(data_struct, &mut info)?;
        }
        _ => unimplemented!("items other than structs are not supported yet"),
    }

    let num_impl = info.num_impl.unwrap();
    let num_impl = quote! {
        fn num_successors(&self) -> usize {
            #num_impl
        }
    };
    let getter_impl = info.getter_impl.unwrap();
    let getter_impl = quote! {
        fn get_successor(&self, index: usize) -> Option<&::orzir_core::Successor> {
            #getter_impl
        }
    };
    let setter_impl = info.setter_impl.unwrap();
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
