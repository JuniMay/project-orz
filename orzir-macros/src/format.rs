use std::collections::BTreeMap;

use proc_macro2::TokenStream;
use quote::quote;
use syn::spanned::Spanned;

use crate::op::{IndexKind, RegionMeta};

/// A format token is embraced by `{}` or just a tokenizer-compatible
/// character/str.
///
/// The compatible puntuations are:
/// ':' | '=' | '(' | ')' | '{' | '}' | '[' | ']' | '<' | '>' | ',' | ';' | '-'
/// or an arrow `->`
///
/// Other punctuations are cannot be tokenized in the
/// [`TokenStream`](orzir_core::TokenStream).
#[derive(Debug, Clone, PartialEq, Eq)]
enum FormatToken {
    Ident(String),
    Delimiter(String),
}

impl FormatToken {
    fn from_str(token: &str) -> syn::Result<Self> {
        if token.starts_with('{') && token.ends_with('}') {
            Ok(Self::Ident(token[1..token.len() - 1].to_string()))
        } else if token == "{{" {
            Ok(Self::Delimiter("{".to_string()))
        } else if token == "}}" {
            Ok(Self::Delimiter("}".to_string()))
        } else {
            Ok(Self::Delimiter(token.to_string()))
        }
    }
}

struct FormatPattern {
    tokens: Vec<FormatToken>,
}

impl FormatPattern {
    fn from_str(pattern: &str) -> syn::Result<Self> {
        let tokens = pattern
            .split_whitespace()
            .map(FormatToken::from_str)
            .collect::<syn::Result<Vec<_>>>()?;
        Ok(Self { tokens })
    }
}

/// The format config
///
/// #[format(pattern = "...", num_results = 1, trailing = false)]
struct FormatConfig {
    /// The pattern
    pattern: FormatPattern,
    /// Number of results
    ///
    /// This can be none, and the number of results will be determined by the
    /// trailing types.
    num_results: Option<usize>,
}

/// The field format config
struct FieldFormatConfig {
    sep: String,
    leading: Option<String>,
    trailing: Option<String>,
}

impl syn::parse::Parse for FieldFormatConfig {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut sep = None;
        let mut leading = None;
        let mut trailing = None;

        while !input.is_empty() {
            let ident: syn::Ident = input.parse()?;
            input.parse::<syn::Token![=]>()?;
            match ident.to_string().as_str() {
                "sep" => {
                    let lit: syn::LitStr = input.parse()?;
                    sep = Some(lit.value());
                }
                "leading" => {
                    let lit: syn::LitStr = input.parse()?;
                    leading = Some(lit.value());
                }
                "trailing" => {
                    let lit: syn::LitStr = input.parse()?;
                    trailing = Some(lit.value());
                }
                _ => {
                    return Err(syn::Error::new(ident.span(), "unknown attribute"));
                }
            }
            if !input.is_empty() {
                input.parse::<syn::Token![,]>()?;
            }
        }

        let config = Self {
            sep: sep.ok_or_else(|| syn::Error::new(input.span(), "missing sep"))?,
            leading,
            trailing,
        };

        Ok(config)
    }
}

impl syn::parse::Parse for FormatConfig {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut pattern = None;
        let mut num_results = None;

        while !input.is_empty() {
            let ident: syn::Ident = input.parse()?;
            input.parse::<syn::Token![=]>()?;
            match ident.to_string().as_str() {
                "pattern" => {
                    let lit: syn::LitStr = input.parse()?;
                    pattern = Some(FormatPattern::from_str(&lit.value())?);
                }
                "num_results" => {
                    let lit: syn::LitInt = input.parse()?;
                    num_results = Some(lit.base10_parse()?);
                }
                _ => {
                    return Err(syn::Error::new(ident.span(), "unknown attribute"));
                }
            }
            if !input.is_empty() {
                input.parse::<syn::Token![,]>()?;
            }
        }

        let config = Self {
            pattern: pattern.ok_or_else(|| syn::Error::new(input.span(), "missing pattern"))?,
            num_results,
        };

        Ok(config)
    }
}

fn derive_print_struct(
    data_struct_ident: &syn::Ident,
    data_struct: &syn::DataStruct,
    config: &FormatConfig,
) -> syn::Result<TokenStream> {
    let fields = data_struct
        .fields
        .iter()
        .enumerate()
        .map(|(idx, field)| {
            if let Some(ident) = &field.ident {
                (ident.to_string(), field)
            } else {
                (format!("arg_{}", idx), field)
            }
        })
        .collect::<BTreeMap<_, _>>();

    let mut print_body = TokenStream::new();

    for token in config.pattern.tokens.iter() {
        match token {
            FormatToken::Ident(ident) => {
                let ident_key = if ident.chars().all(char::is_numeric) {
                    format!("arg_{}", ident)
                } else {
                    ident.clone()
                };

                let field = fields.get(&ident_key).ok_or_else(|| {
                    syn::Error::new(ident.span(), format!("`{}` not found in the struct", ident))
                })?;

                let ident = if ident.chars().all(char::is_numeric) {
                    let index = syn::Index::from(ident.parse::<usize>().unwrap());
                    quote! { self.#index }
                } else {
                    let ident = syn::Ident::new(ident, proc_macro2::Span::call_site());
                    quote! { self.#ident }
                };

                let mut ty = &field.ty;
                let attrs = &field.attrs;

                let mut is_vec = false;
                let mut is_arena_ptr = false;

                let mut is_ty = false;
                let mut is_region = false;
                let mut is_value = false;

                // if the type is Vec<...>, `#[format(sep = "...")]` is required

                // very basic type checking
                if let syn::Type::Path(path) = ty {
                    if let Some(segment) = path.path.segments.last() {
                        if segment.ident == "Vec" {
                            is_vec = true;
                            ty = if let syn::PathArguments::AngleBracketed(args) =
                                &segment.arguments
                            {
                                if let Some(syn::GenericArgument::Type(ty)) = args.args.first() {
                                    ty
                                } else {
                                    return Err(syn::Error::new(
                                        ident.span(),
                                        "missing type argument for Vec",
                                    ));
                                }
                            } else {
                                return Err(syn::Error::new(
                                    ident.span(),
                                    "missing type argument for Vec",
                                ));
                            };
                        }
                    }
                }

                if let syn::Type::Path(path) = ty {
                    if let Some(segment) = path.path.segments.last() {
                        if segment.ident == "ArenaPtr" {
                            if let syn::PathArguments::AngleBracketed(args) = &segment.arguments {
                                if let Some(syn::GenericArgument::Type(
                                    inner_ty @ syn::Type::Path(_),
                                )) = args.args.first()
                                {
                                    is_arena_ptr = true;
                                    ty = inner_ty;

                                    if let syn::Type::Path(path) = &inner_ty {
                                        if let Some(segment) = path.path.segments.last() {
                                            if segment.ident == "Region" {
                                                is_region = true;
                                            } else if segment.ident == "Value" {
                                                is_value = true;
                                            } else if segment.ident == "TyObj" {
                                                is_ty = true;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                let field_config = attrs
                    .iter()
                    .find(|attr| attr.path().is_ident("format"))
                    .map(|attr| attr.parse_args::<FieldFormatConfig>())
                    .transpose()?;

                let field_print_body;

                if is_vec {
                    let field_config = field_config
                        .ok_or_else(|| syn::Error::new(ident.span(), "missing format attribute"))?;
                    let sep = field_config.sep;
                    let leading = field_config.leading;
                    let trailing = field_config.trailing;

                    let item = if is_arena_ptr {
                        if is_region {
                            quote! { item.deref(&__ctx.regions) }
                        } else if is_value {
                            quote! { item.deref(&__ctx.values) }
                        } else if is_ty {
                            quote! { item.deref(&__ctx.tys) }
                        } else {
                            return Err(syn::Error::new(
                                ident.span(),
                                "unsupported ArenaPtr type, expected Region, Value or TyObj",
                            ));
                        }
                    } else {
                        quote! { item }
                    };

                    let leading_space = if sep == "," {
                        quote! {}
                    } else {
                        quote! { write!(__state.buffer, " ")?; }
                    };

                    let leading = leading
                        .map(|s| quote! { #s })
                        .unwrap_or_else(|| quote! { "" });
                    let trailing = trailing
                        .map(|s| quote! { #s })
                        .unwrap_or_else(|| quote! { "" });

                    field_print_body = quote! {
                        write!(__state.buffer, "{}", #leading)?;
                        for (idx, item) in #ident.iter().enumerate() {
                            if idx > 0 {
                                #leading_space
                                write!(__state.buffer, #sep)?;
                                write!(__state.buffer, " ")?;
                            }
                            <#ty as ::orzir_core::Print>::print(#item, __ctx, __state)?;
                        }
                        write!(__state.buffer, "{}", #trailing)?;
                    };
                } else if is_arena_ptr {
                    if is_region {
                        field_print_body = quote! {
                            <#ty as ::orzir_core::Print>::print(#ident.deref(&__ctx.regions), __ctx, __state)?;
                        };
                    } else if is_value {
                        field_print_body = quote! {
                            <#ty as ::orzir_core::Print>::print(#ident.deref(&__ctx.values), __ctx, __state)?;
                        };
                    } else if is_ty {
                        field_print_body = quote! {
                            <#ty as ::orzir_core::Print>::print(#ident.deref(&__ctx.tys), __ctx, __state)?;
                        };
                    } else {
                        return Err(syn::Error::new(
                            ident.span(),
                            "unsupported ArenaPtr type, expected Region, Value or TyObj",
                        ));
                    }
                } else {
                    field_print_body = quote! {
                        <#ty as ::orzir_core::Print>::print(&#ident, __ctx, __state)?;
                    };
                }

                print_body.extend(field_print_body);
            }
            FormatToken::Delimiter(punct) => {
                if punct == "," {
                    // no leading space.
                } else {
                    // add leading space for puncts other than a comma
                    print_body.extend(quote! {
                        write!(__state.buffer, " ")?;
                    });
                }

                print_body.extend(quote! {
                    write!(__state.buffer, #punct)?;
                    write!(__state.buffer, " ")?;
                });
            }
        }
    }

    if let Some(0) = config.num_results {
        // no trailing types
    } else {
        print_body.extend(quote! {
            write!(__state.buffer, " : ")?;
            let __tys = <Self as ::orzir_core::DataFlow>::result_tys(self, __ctx);
        });
        print_body.extend(quote! {
            if __tys.len() > 1 {
                write!(__state.buffer, "(")?;
            }

            for (__idx, __ty) in __tys.iter().enumerate() {
                if __idx > 0 {
                    write!(__state.buffer, ", ")?;
                }
                <::orzir_core::TyObj as ::orzir_core::Print>::print(__ty.deref(&__ctx.tys), __ctx, __state)?;
            }

            if __tys.len() > 1 {
                write!(__state.buffer, ")")?;
            }
        });
    }

    let print_impl = quote! {
        impl ::orzir_core::Print for #data_struct_ident {
            fn print(&self, __ctx: &::orzir_core::Context, __state: &mut ::orzir_core::PrintState) -> ::orzir_core::PrintResult<()> {
                #print_body
                Ok(())
            }
        }
    };

    Ok(print_impl)
}

fn derive_parse_struct(
    data_struct_ident: &syn::Ident,
    data_struct: &syn::DataStruct,
    config: &FormatConfig,
) -> syn::Result<TokenStream> {
    // get the ident to field mapping
    let fields = data_struct
        .fields
        .iter()
        .enumerate()
        .map(|(idx, field)| {
            if let Some(ident) = &field.ident {
                (ident.to_string(), field)
            } else {
                (format!("arg_{}", idx), field)
            }
        })
        .collect::<BTreeMap<_, _>>();

    let mut parse_body = TokenStream::new();

    for token in config.pattern.tokens.iter() {
        match token {
            FormatToken::Ident(ident) => {
                let ident = if ident.chars().all(char::is_numeric) {
                    format!("arg_{}", ident)
                } else {
                    ident.clone()
                };

                let field = fields.get(&ident).ok_or_else(|| {
                    syn::Error::new(ident.span(), format!("`{}` not found in the struct", ident))
                })?;

                // cannot use the field's ident directly, because it may be an index
                let ident = syn::Ident::new(&ident, proc_macro2::Span::call_site());

                let mut ty = &field.ty;
                let attrs = &field.attrs;

                let mut is_vec = false;
                let mut is_region = false;

                // if the type is Vec<...>, `#[format(sep = "...")]` is required
                // if the type is ArenaPtr<Region>, `#[region(<idx>, <kind>)]` is required

                // very basic type checking
                if let syn::Type::Path(path) = ty {
                    if let Some(segment) = path.path.segments.last() {
                        if segment.ident == "Vec" {
                            is_vec = true;
                            ty = if let syn::PathArguments::AngleBracketed(args) =
                                &segment.arguments
                            {
                                if let Some(syn::GenericArgument::Type(ty)) = args.args.first() {
                                    ty
                                } else {
                                    return Err(syn::Error::new(
                                        ident.span(),
                                        "missing type argument for Vec",
                                    ));
                                }
                            } else {
                                return Err(syn::Error::new(
                                    ident.span(),
                                    "missing type argument for Vec",
                                ));
                            };
                        }
                    }
                }

                if let syn::Type::Path(path) = ty {
                    if let Some(segment) = path.path.segments.last() {
                        if segment.ident == "ArenaPtr" {
                            if let syn::PathArguments::AngleBracketed(args) = &segment.arguments {
                                if let Some(syn::GenericArgument::Type(
                                    inner_ty @ syn::Type::Path(path),
                                )) = args.args.first()
                                {
                                    if let Some(segment) = path.path.segments.last() {
                                        if segment.ident == "Region" {
                                            is_region = true;
                                        }
                                    }
                                    ty = inner_ty;
                                }
                            }
                        }
                    }
                }

                let region_meta = if is_region {
                    attrs
                        .iter()
                        .find(|attr| attr.path().is_ident("region"))
                        .map(|attr| attr.parse_args::<RegionMeta>())
                } else {
                    None
                }
                .transpose()?;

                let field_config = attrs
                    .iter()
                    .find(|attr| attr.path().is_ident("format"))
                    .map(|attr| attr.parse_args::<FieldFormatConfig>())
                    .transpose()?;

                let field_parse_body;

                let region_kind = region_meta.as_ref().and_then(|meta| meta.kind.clone());
                let region_index = region_meta.as_ref().map(|meta| meta.index);

                if is_vec {
                    let field_config = field_config
                        .ok_or_else(|| syn::Error::new(ident.span(), "missing format attribute"))?;
                    let sep = field_config.sep;

                    let parse_stmt = if is_region {
                        let region_kind = region_kind.ok_or_else(|| {
                            syn::Error::new(ident.span(), "missing region kind attribute")
                        })?;
                        if let Some(IndexKind::Single(_)) = region_index {
                            return Err(syn::Error::new(
                                ident.span(),
                                "region index cannot be discrete for Vec<...>",
                            ));
                        }
                        quote! {
                            __state.enter_region_with(#region_kind, __idx);
                            let __item_result = <#ty as ::orzir_core::Parse>::parse(__ctx, __state);
                            __state.exit_region();
                        }
                    } else {
                        quote! {
                            let __item_result = <#ty as ::orzir_core::Parse>::parse(__ctx, __state);
                        }
                    };

                    // backtracking to handle the first optional item
                    let parse_stmt = if field_config.trailing.is_none() {
                        // rolling back
                        quote! {
                            __state.stream.checkpoint();
                            #parse_stmt
                            if let Err(_) = __item_result {
                                __state.stream.rollback();
                                break;
                            }
                            __state.stream.commit();
                            let __item = __item_result.unwrap();
                        }
                    } else {
                        quote! {
                            #parse_stmt
                            let __item = __item_result?;
                        }
                    };

                    let field_parse_loop_body = quote! {
                        #parse_stmt
                        #ident.push(__item);
                        __idx += 1;

                        if let ::orzir_core::token!(#sep) = __state.stream.peek()?.kind {
                            __state.stream.consume()?;
                        } else {
                            break;
                        }
                    };

                    let field_parse_loop_body = if let Some(ref trailing) = field_config.trailing {
                        quote! {
                            let mut __idx = 0;
                            loop {
                                if let ::orzir_core::token!(#trailing) = __state.stream.peek()?.kind {
                                    break;
                                }

                                #field_parse_loop_body
                            }
                            __state.stream.expect(::orzir_core::token!(#trailing))?;
                        }
                    } else {
                        quote! {
                            let mut __idx = 0;
                            loop {
                                #field_parse_loop_body
                            }
                        }
                    };

                    let field_parse_loop_body = if let Some(ref leading) = field_config.leading {
                        quote! {
                            if let ::orzir_core::token!(#leading) = __state.stream.peek()?.kind {
                                __state.stream.consume()?;
                                #field_parse_loop_body
                            }
                        }
                    } else {
                        field_parse_loop_body
                    };

                    field_parse_body = quote! {
                        let mut #ident = Vec::new();
                        #field_parse_loop_body
                    }
                } else if is_region {
                    let region_kind = region_kind.ok_or_else(|| {
                        syn::Error::new(ident.span(), "missing region kind attribute")
                    })?;
                    let region_index = region_index.ok_or_else(|| {
                        syn::Error::new(ident.span(), "missing region index attribute")
                    })?;
                    let region_index = match region_index {
                        IndexKind::Single(idx) => quote! { #idx },
                        IndexKind::All => {
                            return Err(syn::Error::new(
                                ident.span(),
                                "region index cannot be `...`",
                            ))
                        }
                    };

                    field_parse_body = quote! {
                        __state.enter_region_with(#region_kind, #region_index);
                        let #ident = <#ty as ::orzir_core::Parse>::parse(__ctx, __state)?;
                        __state.exit_region();
                    }
                } else {
                    field_parse_body = quote! {
                        let #ident = <#ty as ::orzir_core::Parse>::parse(__ctx, __state)?;
                    }
                }

                parse_body.extend(field_parse_body);
            }
            FormatToken::Delimiter(punct) => {
                parse_body.extend(quote! {
                    __state.stream.expect(::orzir_core::token!(#punct))?;
                });
            }
        }
    }

    if let Some(0) = config.num_results {
        // for 0 results, no trailing types are allowed
    } else {
        // for 1 or unknown number of results, trailing types should be parsed
        parse_body.extend(quote! {
            let mut __tys = Vec::new();
            __state.stream.expect(::orzir_core::token!(':'))?;
            let __trailing_start_pos = __state.stream.curr_pos()?;
            if let ::orzir_core::token!('(') = __state.stream.peek()?.kind {
                __state.stream.consume()?;
                loop {
                    let __ty = <::orzir_core::TyObj as ::orzir_core::Parse>::parse(__ctx, __state)?;
                    __tys.push(__ty);
                    if let ::orzir_core::token!(',') = __state.stream.peek()?.kind {
                        __state.stream.consume()?;
                    } else {
                        break;
                    }
                }
                __state.stream.expect(::orzir_core::token!(')'))?;
            } else {
                let __ty = <::orzir_core::TyObj as ::orzir_core::Parse>::parse(__ctx, __state)?;
                __tys.push(__ty);
            }
            let __trailing_end_pos = __state.stream.curr_pos()?;
        });
    }

    let num_results = if let Some(0) = config.num_results {
        quote! { 0 }
    } else if let Some(num) = config.num_results {
        // if there are trailing types and the number is set, do the check
        parse_body.extend(quote! {
            if __tys.len() != #num {
                return Err(::orzir_core::parse_error!(
                    ::orzir_core::Span::new(__trailing_start_pos, __trailing_end_pos),
                    ::orzir_core::ParseErrorKind::InvalidTrailingTypeNumber(#num, __tys.len())
                ));
            }
        });
        quote! { #num }
    } else {
        // if the type is not specified, the number of results is determined by the
        // trailing types
        quote! { __tys.len() }
    };

    // the result names
    if let Some(0) = config.num_results {
        parse_body.extend(quote! {
            let mut __result_names = __state.pop_result_names();
            if !__result_names.is_empty() {
                let mut __span = __result_names[0].span;
                for __name in __result_names.iter().skip(1) {
                    __span = __span.merge(&__name.span);
                }
                return ::orzir_core::parse_error!(
                    __span,
                    ::orzir_core::ParseErrorKind::InvalidResultNumber(0, __result_names.len())
                )
                .into();
            }
        })
    } else {
        parse_body.extend(
        quote! {
            let mut __result_names = __state.pop_result_names();
            let mut __results = Vec::new();
            if __result_names.len() != #num_results {
                if __result_names.is_empty() {
                    return ::orzir_core::parse_error!(
                        ::orzir_core::Span::new(__start_pos, __start_pos),
                        ::orzir_core::ParseErrorKind::InvalidResultNumber(#num_results, 0)
                    )
                    .into();
                }

                let mut __span = __result_names[0].span;
                for __name in __result_names.iter().skip(1) {
                    __span = __span.merge(&__name.span);
                }

                return ::orzir_core::parse_error!(
                    __span,
                    ::orzir_core::ParseErrorKind::InvalidResultNumber(#num_results, __result_names.len())
                )
                .into();
            }

            for (__idx, (__name, __ty)) in __result_names.drain(..).zip(__tys.drain(..)).enumerate() {
                let __result = ::orzir_core::Value::new_op_result(__ctx, __ty, __op, __idx, Some(__name.unwrap_value_name()));
                __results.push(__result);
            }
        }
    );
    }

    let mut construction = TokenStream::new();

    for field in data_struct.fields.iter() {
        let attrs = &field.attrs;

        let is_metadata = attrs.iter().any(|attr| attr.path().is_ident("metadata"));

        if is_metadata {
            continue;
        }

        let result_meta = attrs.iter().find(|attr| attr.path().is_ident("result"));

        if let Some(result_meta) = result_meta {
            let index = result_meta.parse_args::<IndexKind>()?;
            match index {
                IndexKind::All => {
                    // all results
                    construction.extend(quote! { __results, });
                }
                IndexKind::Single(idx) => {
                    // single result
                    construction.extend(quote! { __results[#idx], });
                }
            }
            continue;
        }

        let ident = field.ident.as_ref().unwrap();
        construction.extend(quote! { #ident, });
    }

    let construction = quote! {
        let __op = #data_struct_ident::new(__ctx, __op, #construction);
    };

    let parse_impl = quote! {
        impl ::orzir_core::Parse for #data_struct_ident {
            type Item = ::orzir_core::ArenaPtr<OpObj>;

            fn parse(__ctx: &mut ::orzir_core::Context, __state: &mut ::orzir_core::ParseState) -> ::orzir_core::ParseResult<Self::Item> {

                let __op = __ctx.ops.reserve();
                let __start_pos = __state.stream.curr_pos()?;

                __state.enter_component_from(__op);

                #parse_body

                let __end_pos = __state.stream.curr_pos()?;
                __state.exit_component();

                #construction

                Ok(__op)
            }
        }
    };

    Ok(parse_impl)
}

pub fn derive_parse_impl(ast: &syn::DeriveInput) -> syn::Result<TokenStream> {
    let config = ast
        .attrs
        .iter()
        .find(|attr| attr.path().is_ident("format"))
        .map(|attr| attr.parse_args::<FormatConfig>())
        .transpose()?
        .ok_or_else(|| {
            syn::Error::new_spanned(ast, "invalid format pattern, expected #[format(...)]")
        })?;

    let impls = match &ast.data {
        syn::Data::Struct(data_struct) => derive_parse_struct(&ast.ident, data_struct, &config)?,
        _ => unimplemented!("items other than struct are not supported yet."),
    };

    Ok(impls)
}

pub fn derive_print_impl(ast: &syn::DeriveInput) -> syn::Result<TokenStream> {
    let config = ast
        .attrs
        .iter()
        .find(|attr| attr.path().is_ident("format"))
        .map(|attr| attr.parse_args::<FormatConfig>())
        .transpose()?
        .ok_or_else(|| {
            syn::Error::new_spanned(ast, "invalid format pattern, expected #[format(...)]")
        })?;

    let impls = match &ast.data {
        syn::Data::Struct(data_struct) => derive_print_struct(&ast.ident, data_struct, &config)?,
        _ => unimplemented!("items other than struct are not supported yet."),
    };

    Ok(impls)
}

#[cfg(test)]
mod tests {
    use quote::quote;

    #[test]
    fn test_0() {
        let src = quote! {
            #[format(pattern = "{lhs} , {rhs}", num_results = 1)]
            pub struct IAddOp {
                #[metadata]
                metadata: OpMetadata,

                #[result(0)]
                result: ArenaPtr<Value>,

                #[operand(0)]
                lhs: ArenaPtr<Value>,

                #[operand(1)]
                rhs: ArenaPtr<Value>,
            }
        };

        let ast = syn::parse2::<syn::DeriveInput>(src).unwrap();
        let output = super::derive_parse_impl(&ast).unwrap();
        println!("{}", output);
        let ast = syn::parse_file(&output.to_string()).unwrap();
        let ast = prettyplease::unparse(&ast);
        println!("{}", ast);
    }

    #[test]
    fn test_1() {
        let src = quote! {
            #[format(pattern = "{lhs} , {rhs}", num_results = 1)]
            pub struct IAddOp {
                #[metadata]
                metadata: OpMetadata,

                #[result(0)]
                result: ArenaPtr<Value>,

                #[operand(0)]
                lhs: ArenaPtr<Value>,

                #[operand(1)]
                rhs: ArenaPtr<Value>,
            }
        };

        let ast = syn::parse2::<syn::DeriveInput>(src).unwrap();
        let output = super::derive_print_impl(&ast).unwrap();
        println!("{}", output);
        let ast = syn::parse_file(&output.to_string()).unwrap();
        let ast = prettyplease::unparse(&ast);
        println!("{}", ast);
    }
}
