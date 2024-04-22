use std::collections::HashMap;

use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::spanned::Spanned;

use crate::op::{FieldIdent, IndexKind, OpDeriveInfo, OpFieldMeta, RegionMeta};

/// A format token is embraced by `{}` or just a tokenizer-compatible delimiter.
///
/// Other tokenized strings are not supported yet.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum FormatToken {
    Field(String),
    Delimiter(String),
    Whitespace(String),
    Tokenized(String),
}

/// Check if a character is a valid delimiter.
fn is_delimiter(c: char) -> bool {
    matches!(
        c,
        ':' | '=' | '(' | ')' | '{' | '}' | '[' | ']' | '<' | '>' | ',' | ';' | '*' | '-'
    )
}

impl FormatToken {
    /// Parse a format token from a string.
    fn from_str(token: &str) -> syn::Result<Self> {
        if token.starts_with('{') && token.ends_with('}') {
            Ok(Self::Field(token[1..token.len() - 1].to_string()))
        } else if token == "{{" || token == "}}" {
            Ok(Self::Delimiter(token.chars().next().unwrap().to_string()))
        } else if token == "->" || (token.len() == 1 && token.chars().all(is_delimiter)) {
            Ok(Self::Delimiter(token.to_string()))
        } else if token.chars().all(char::is_whitespace) {
            Ok(Self::Whitespace(token.to_string()))
        } else {
            Ok(Self::Tokenized(token.to_string()))
        }
    }

    /// Convert the token to the corresponding `TokenKind`
    fn to_token(&self) -> TokenStream {
        match self {
            Self::Delimiter(delimiter) => {
                if delimiter.len() == 1 {
                    let ch = delimiter.chars().next().unwrap();
                    quote! { ::orzir_core::TokenKind::Char(#ch) }
                } else if delimiter == "->" {
                    quote! { ::orzir_core::TokenKind::Arrow }
                } else {
                    unreachable!("invalid delimiter {}", delimiter);
                }
            }
            Self::Tokenized(s) => {
                quote! { ::orzir_core::TokenKind::Tokenized(#s.to_string()) }
            }
            _ => unreachable!("should not convert field to token"),
        }
    }

    /// Generate the print statements for a delimiter.
    #[allow(clippy::let_and_return)]
    fn generate_printer(&self) -> TokenStream {
        match self {
            Self::Delimiter(delimiter) => {
                let delimiter = delimiter.as_str();
                quote! {
                    write!(__state.buffer, "{}", #delimiter)?;
                }
            }
            Self::Whitespace(w) => {
                let w = w.as_str();
                quote! {
                    write!(__state.buffer, "{}", #w)?;
                }
            }
            Self::Tokenized(s) => {
                let s = s.as_str();
                quote! {
                    write!(__state.buffer, "{}", #s)?;
                }
            }
            _ => unreachable!("should not generate printer for field"),
        }
    }
}

/// The format pattern.
struct FormatPattern {
    tokens: Vec<FormatToken>,
}

impl FormatPattern {
    fn from_str(pattern: &str) -> syn::Result<Self> {
        let mut idx = 0;
        let mut buffer = String::new();

        let mut tokens = Vec::new();

        let chars = pattern.chars().collect::<Vec<_>>();

        while idx < chars.len() {
            let curr_char = chars[idx];

            match curr_char {
                '{' => {
                    if idx + 1 < chars.len() && chars[idx + 1] == '{' {
                        tokens.push(FormatToken::from_str("{{")?);
                        idx += 1;
                    } else {
                        while idx < chars.len() && chars[idx] != '}' {
                            buffer.push(chars[idx]);
                            idx += 1;
                        }
                        if chars[idx] != '}' {
                            return Err(syn::Error::new(
                                Span::call_site(),
                                "unexpected end of format pattern",
                            ));
                        }
                        buffer.push('}');
                        tokens.push(FormatToken::from_str(buffer.as_str())?);
                    }
                }
                '}' => {
                    if idx + 1 < chars.len() && chars[idx + 1] == '}' {
                        tokens.push(FormatToken::from_str("}}")?);
                        idx += 1;
                    } else {
                        return Err(syn::Error::new(
                            Span::call_site(),
                            "unexpected '}' in format pattern",
                        ));
                    }
                }
                '-' => {
                    if idx + 1 < chars.len() && chars[idx + 1] == '>' {
                        tokens.push(FormatToken::from_str("->")?);
                        idx += 1;
                    } else {
                        tokens.push(FormatToken::from_str("-")?);
                    }
                }
                c if c.is_whitespace() => {
                    while idx < chars.len() && chars[idx].is_whitespace() {
                        buffer.push(chars[idx]);
                        idx += 1;
                    }
                    idx -= 1;
                    tokens.push(FormatToken::from_str(buffer.as_str())?);
                }
                c if is_delimiter(c) => {
                    tokens.push(FormatToken::from_str(&curr_char.to_string())?);
                }
                _ => {
                    while idx < chars.len()
                        && !chars[idx].is_whitespace()
                        && !is_delimiter(chars[idx])
                    {
                        buffer.push(chars[idx]);
                        idx += 1;
                    }
                    tokens.push(FormatToken::from_str(buffer.as_str())?);
                }
            }

            buffer.clear();
            idx += 1;
        }

        Ok(Self { tokens })
    }
}

/// The format kind.
///
/// TODO: This can be determined by examining the `derive` attribute.
enum FormatKind {
    Op,
    Ty,
    Other,
}

/// The format meta for the struct.
struct FormatMeta {
    /// The format pattern.
    pattern: FormatPattern,
    /// The format kind.
    kind: FormatKind,
    /// The number of results, if this is an operation.
    num_results: Option<usize>,
}

impl syn::parse::Parse for FormatMeta {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut pattern = None;
        let mut kind = FormatKind::Other;
        let mut num_results = None;

        while !input.is_empty() {
            let ident: syn::Ident = input.parse()?;
            match ident.to_string().as_str() {
                "pattern" => {
                    input.parse::<syn::Token![=]>()?;
                    let pattern_str: syn::LitStr = input.parse()?;
                    pattern = Some(FormatPattern::from_str(&pattern_str.value())?);
                }
                "kind" => {
                    input.parse::<syn::Token![=]>()?;
                    let kind_str: syn::LitStr = input.parse()?;
                    match kind_str.value().as_str() {
                        "op" => kind = FormatKind::Op,
                        "ty" => kind = FormatKind::Ty,
                        _ => kind = FormatKind::Other,
                    }
                }
                "num_results" => {
                    input.parse::<syn::Token![=]>()?;
                    num_results = Some(input.parse::<syn::LitInt>()?.base10_parse()?);
                }
                _ => {
                    return Err(syn::Error::new(ident.span(), "unknown format attribute"));
                }
            }

            if input.peek(syn::Token![,]) {
                input.parse::<syn::Token![,]>()?;
            }
        }

        Ok(Self {
            pattern: pattern
                .ok_or_else(|| syn::Error::new(input.span(), "missing format pattern"))?,
            kind,
            num_results,
        })
    }
}

/// The repeat meta for the field.
struct RepeatMeta {
    /// The separator.
    sep: Option<FormatPattern>,
    /// The leading delimiter.
    leading: Option<FormatToken>,
    /// The trailing delimiter.
    trailing: Option<FormatToken>,
}

impl syn::parse::Parse for RepeatMeta {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut sep = None;
        let mut leading = None;
        let mut trailing = None;

        while !input.is_empty() {
            let ident: syn::Ident = input.parse()?;
            match ident.to_string().as_str() {
                "sep" => {
                    input.parse::<syn::Token![=]>()?;
                    let sep_str: syn::LitStr = input.parse()?;
                    let sep_pattern = FormatPattern::from_str(&sep_str.value())?;
                    sep = Some(sep_pattern);
                }
                "leading" => {
                    input.parse::<syn::Token![=]>()?;
                    leading = Some(FormatToken::from_str(
                        &input.parse::<syn::LitStr>()?.value(),
                    )?);
                }
                "trailing" => {
                    input.parse::<syn::Token![=]>()?;
                    trailing = Some(FormatToken::from_str(
                        &input.parse::<syn::LitStr>()?.value(),
                    )?);
                }
                _ => {
                    return Err(syn::Error::new(ident.span(), "unknown repeat attribute"));
                }
            }

            if input.peek(syn::Token![,]) {
                input.parse::<syn::Token![,]>()?;
            }
        }

        Ok(Self {
            sep,
            leading,
            trailing,
        })
    }
}

/// The format information for the struct.
struct FormatInfo {
    meta: FormatMeta,
    repeats: HashMap<FieldIdent, RepeatMeta>,
}

impl FormatInfo {
    fn from_ast(ast: &syn::DeriveInput) -> syn::Result<Self> {
        let mut meta = None;
        let mut repeats = HashMap::new();

        for attr in &ast.attrs {
            if attr.path().is_ident("format") {
                let meta_ = attr.parse_args::<FormatMeta>()?;
                if meta.is_some() {
                    return Err(syn::Error::new(attr.span(), "duplicate format attribute"));
                }
                meta = Some(meta_);
            }
        }

        if let syn::Data::Struct(ref data_struct) = ast.data {
            for (idx, field) in data_struct.fields.iter().enumerate() {
                let ident = match field.ident {
                    Some(ref ident) => FieldIdent::Ident(ident.to_string()),
                    None => FieldIdent::Index(idx),
                };

                for attr in field.attrs.iter() {
                    if attr.path().is_ident("repeat") {
                        let repeat_meta = attr.parse_args::<RepeatMeta>()?;
                        if repeats.insert(ident.clone(), repeat_meta).is_some() {
                            return Err(syn::Error::new(attr.span(), "duplicate repeat attribute"));
                        }
                    }
                }
            }
        }

        Ok(Self {
            meta: meta.ok_or_else(|| syn::Error::new(ast.span(), "missing format attribute"))?,
            repeats,
        })
    }
}

/// Generate the parser for a repeat pattern.
fn generate_repeat_parser(
    field_ident: &FieldIdent,
    op_field_meta: &OpFieldMeta,
    repeat_meta: &RepeatMeta,
) -> syn::Result<TokenStream> {
    // field ident will be assigned with the parsed value.
    let field_ident = match field_ident {
        FieldIdent::Ident(field_ident) => syn::Ident::new(field_ident, Span::call_site()),
        FieldIdent::Index(idx) => syn::Ident::new(&format!("arg_{}", idx), Span::call_site()),
    };

    // generate the basic parse stmt.
    let parse_stmts = match op_field_meta {
        OpFieldMeta::Metadata => unreachable!("should not parse metadata field"),
        OpFieldMeta::Region(RegionMeta { index, kind }) => {
            if let IndexKind::Single(_) = index {
                unreachable!("should not parse single region field");
            }

            if kind.is_none() {
                return Err(syn::Error::new(
                    // TODO: Span may not be correct here
                    field_ident.span(),
                    "region field must have a kind attribute",
                ));
            }

            let kind = kind.as_ref().unwrap();

            quote! {
                __state.enter_region_with(#kind, __idx);
                let __item_result = <::orzir_core::Region as ::orzir_core::Parse>::parse(__ctx, __state);
                __state.exit_region();
            }
        }
        OpFieldMeta::Result(index) | OpFieldMeta::Operand(index) => {
            if let IndexKind::Single(_) = index {
                unreachable!("should not parse single result/operand field");
            }
            quote! {
                let __item_result = <::orzir_core::Value as ::orzir_core::Parse>::parse(__ctx, __state);
            }
        }
        OpFieldMeta::Successor(index) => {
            if let IndexKind::Single(_) = index {
                unreachable!("should not parse single successor field");
            }
            quote! {
                let __item_result = <::orzir_core::Successor as ::orzir_core::Parse>::parse(__ctx, __state);
            }
        }
        OpFieldMeta::Other { is_vec, ty } => {
            if !is_vec {
                unreachable!("should not parse non-vec field with repeat attribute");
            }
            quote! {
                let __item_result = <#ty as ::orzir_core::Parse>::parse(__ctx, __state);
            }
        }
    };

    let parse_stmts = match repeat_meta.trailing {
        Some(_) => {
            // if there is a trailing delimiter, just match it to check if break.
            quote! {
                #parse_stmts
                let __item = __item_result?;
            }
        }
        None => {
            // if the trailing is none, handle the first optional item by backtracking
            quote! {
                __state.stream.checkpoint();
                #parse_stmts
                if __item_result.is_err() {
                    __state.stream.rollback();
                    break;
                }
                __state.stream.commit();
                let __item = __item_result.unwrap();
            }
        }
    };

    let parse_stmts = quote! {
        #parse_stmts
        #field_ident.push(__item);
        __idx += 1;
    };

    let parse_stmts = if let Some(sep) = &repeat_meta.sep {
        // get the separator token, skip the whitespace.
        let mut sep_token = None;

        for token in sep.tokens.iter() {
            if let FormatToken::Whitespace(_) = token {
                continue;
            }
            sep_token = Some(token.to_token());
        }

        if let Some(sep_token) = sep_token {
            // TODO: this can be better implemented to support more complex patterns.
            quote! {
                #parse_stmts

                if let #sep_token = __state.stream.peek()?.kind {
                    __state.stream.consume()?;
                } else {
                    break;
                }
            }
        } else {
            // all whitespace, just parse the next item.
            parse_stmts
        }
    } else {
        parse_stmts
    };

    let output = if let Some(trailing) = &repeat_meta.trailing {
        let trailing_token = trailing.to_token();
        quote! {
            let mut #field_ident = Vec::new();
            let mut __idx = 0;
            loop {
                if let #trailing_token = __state.stream.peek()?.kind {
                    break;
                }
                #parse_stmts
            }
            __state.stream.expect(#trailing_token)?;
        }
    } else {
        quote! {
            let mut #field_ident = Vec::new();
            let mut __idx = 0;
            loop {
                #parse_stmts
            }
        }
    };

    let output = if let Some(leading) = &repeat_meta.leading {
        let leading_token = leading.to_token();
        quote! {
            __state.stream.expect(#leading_token)?;
            #output
        }
    } else {
        output
    };

    Ok(output)
}

/// Generat a printer for repeat pattern.
fn generate_repeat_printer(
    field_ident: &FieldIdent,
    op_field_meta: &OpFieldMeta,
    repeat_meta: &RepeatMeta,
) -> syn::Result<TokenStream> {
    let field = match field_ident {
        FieldIdent::Ident(ident) => {
            let ident = syn::Ident::new(ident, Span::call_site());
            quote! { self.#ident }
        }
        FieldIdent::Index(idx) => {
            let index = syn::Index::from(*idx);
            quote! { self.#index }
        }
    };

    let print_stmts = match op_field_meta {
        OpFieldMeta::Metadata => unreachable!("should not print metadata field"),
        OpFieldMeta::Region(RegionMeta { index, .. }) => {
            if let IndexKind::Single(_) = index {
                unreachable!("should not print single region field");
            }
            quote! {
                <::orzir_core::Region as ::orzir_core::Print>::print(__item.deref(&__ctx.regions), __ctx, __state)?;
            }
        }
        OpFieldMeta::Result(index) | OpFieldMeta::Operand(index) => {
            if let IndexKind::Single(_) = index {
                unreachable!("should not print single result/operand field");
            }
            quote! {
                <::orzir_core::Value as ::orzir_core::Print>::print(__item.deref(&__ctx.values), __ctx, __state)?;
            }
        }
        OpFieldMeta::Successor(index) => {
            if let IndexKind::Single(_) = index {
                unreachable!("should not print single successor field");
            }
            quote! {
                <::orzir_core::Successor as ::orzir_core::Print>::print(__item, __ctx, __state)?;
            }
        }
        OpFieldMeta::Other { is_vec, ty } => {
            if !is_vec {
                unreachable!("should not print non-vec field with repeat attribute");
            }
            quote! {
                <#ty as ::orzir_core::Print>::print(__item, __ctx, __state)?;
            }
        }
    };

    let sep_printer = if let Some(sep) = &repeat_meta.sep {
        let mut printer = TokenStream::new();
        for token in sep.tokens.iter() {
            printer.extend(token.generate_printer());
        }
        printer
    } else {
        quote! {
            write!(__state.buffer, " ")?;
        }
    };

    let output = if let Some(leading) = &repeat_meta.leading {
        let leading_printer = leading.generate_printer();
        quote! {
            #leading_printer
            for (__idx, __item) in #field.iter().enumerate() {
                #print_stmts
                if __idx + 1 < #field.len() {
                    #sep_printer
                }
            }
        }
    } else {
        quote! {
            for (__idx, __item) in #field.iter().enumerate() {
                #print_stmts
                if __idx + 1 < #field.len() {
                    #sep_printer
                }
            }
        }
    };

    let output = if let Some(trailing) = &repeat_meta.trailing {
        let trailing_printer = trailing.generate_printer();
        quote! {
            #output
            #trailing_printer
        }
    } else {
        output
    };

    Ok(output)
}

fn generate_field_parser(
    field_ident: &FieldIdent,
    op_field_meta: &OpFieldMeta,
    format_info: &FormatInfo,
) -> syn::Result<TokenStream> {
    match op_field_meta {
        OpFieldMeta::Metadata => {
            // just skip.
            Ok(quote! {})
        }
        OpFieldMeta::Operand(index)
        | OpFieldMeta::Region(RegionMeta { index, .. })
        | OpFieldMeta::Result(index)
        | OpFieldMeta::Successor(index) => match index {
            IndexKind::All | IndexKind::Range(..) => {
                let repeat_meta = format_info.repeats.get(field_ident).unwrap_or(&RepeatMeta {
                    sep: None,
                    leading: None,
                    trailing: None,
                });
                generate_repeat_parser(field_ident, op_field_meta, repeat_meta)
            }
            IndexKind::Single(_) => {
                let field_ident = match field_ident {
                    FieldIdent::Ident(field_ident) => {
                        syn::Ident::new(field_ident, Span::call_site())
                    }
                    FieldIdent::Index(idx) => {
                        syn::Ident::new(&format!("arg_{}", idx), Span::call_site())
                    }
                };

                let parse_stmts = match op_field_meta {
                    OpFieldMeta::Region(RegionMeta { index, kind }) => {
                        if kind.is_none() {
                            return Err(syn::Error::new(
                                // TODO: Span may not be correct here
                                field_ident.span(),
                                "region field must have a kind attribute",
                            ));
                        }

                        let kind = kind.as_ref().unwrap();

                        let index = match index {
                            IndexKind::Single(idx) => idx,
                            _ => unreachable!(),
                        };

                        quote! {
                            __state.enter_region_with(#kind, #index);
                            let #field_ident = <::orzir_core::Region as ::orzir_core::Parse>::parse(__ctx, __state)?;
                            __state.exit_region();
                        }
                    }
                    OpFieldMeta::Result(_) | OpFieldMeta::Operand(_) => {
                        quote! {
                            let #field_ident = <::orzir_core::Value as ::orzir_core::Parse>::parse(__ctx, __state)?;
                        }
                    }
                    OpFieldMeta::Successor(_) => {
                        quote! {
                            let #field_ident = <::orzir_core::Successor as ::orzir_core::Parse>::parse(__ctx, __state)?;
                        }
                    }
                    _ => unreachable!(),
                };

                Ok(parse_stmts)
            }
        },
        OpFieldMeta::Other { is_vec, ty } => {
            if *is_vec {
                let repeat_meta = format_info.repeats.get(field_ident).unwrap_or(&RepeatMeta {
                    sep: None,
                    leading: None,
                    trailing: None,
                });
                generate_repeat_parser(field_ident, op_field_meta, repeat_meta)
            } else {
                let field_ident = match field_ident {
                    FieldIdent::Ident(field_ident) => {
                        syn::Ident::new(field_ident, Span::call_site())
                    }
                    FieldIdent::Index(idx) => {
                        syn::Ident::new(&format!("arg_{}", idx), Span::call_site())
                    }
                };

                let parse_stmts = quote! {
                    let #field_ident = <#ty as ::orzir_core::Parse>::parse(__ctx, __state)?;
                };

                Ok(parse_stmts)
            }
        }
    }
}

fn generate_field_printer(
    field_ident: &FieldIdent,
    op_field_meta: &OpFieldMeta,
    format_info: &FormatInfo,
) -> syn::Result<TokenStream> {
    match op_field_meta {
        OpFieldMeta::Metadata => {
            // just skip.
            Ok(quote! {})
        }
        OpFieldMeta::Operand(index)
        | OpFieldMeta::Region(RegionMeta { index, .. })
        | OpFieldMeta::Result(index)
        | OpFieldMeta::Successor(index) => match index {
            IndexKind::All | IndexKind::Range(..) => {
                let repeat_meta = format_info.repeats.get(field_ident).unwrap_or(&RepeatMeta {
                    sep: None,
                    leading: None,
                    trailing: None,
                });
                generate_repeat_printer(field_ident, op_field_meta, repeat_meta)
            }
            IndexKind::Single(_) => {
                let field = match field_ident {
                    FieldIdent::Ident(field_ident) => {
                        let ident = syn::Ident::new(field_ident, Span::call_site());
                        quote! { self.#ident }
                    }
                    FieldIdent::Index(idx) => {
                        let index = syn::Index::from(*idx);
                        quote! { self.#index }
                    }
                };

                let print_stmts = match op_field_meta {
                    OpFieldMeta::Region(RegionMeta { .. }) => {
                        quote! {
                            <::orzir_core::Region as ::orzir_core::Print>::print(
                                #field.deref(&__ctx.regions),
                                __ctx,
                                __state
                            )?;
                        }
                    }
                    OpFieldMeta::Result(_) | OpFieldMeta::Operand(_) => {
                        quote! {
                            <::orzir_core::Value as ::orzir_core::Print>::print(
                                #field.deref(&__ctx.values),
                                __ctx,
                                __state
                            )?;
                        }
                    }
                    OpFieldMeta::Successor(_) => {
                        quote! {
                            <::orzir_core::Successor as ::orzir_core::Print>::print(
                                &#field,
                                __ctx,
                                __state
                            )?;
                        }
                    }
                    _ => unreachable!(),
                };

                Ok(print_stmts)
            }
        },
        OpFieldMeta::Other { is_vec, ty } => {
            if *is_vec {
                let repeat_meta = format_info.repeats.get(field_ident).unwrap_or(&RepeatMeta {
                    sep: None,
                    leading: None,
                    trailing: None,
                });
                generate_repeat_printer(field_ident, op_field_meta, repeat_meta)
            } else {
                let field = match field_ident {
                    FieldIdent::Ident(field_ident) => {
                        let ident = syn::Ident::new(field_ident, Span::call_site());
                        quote! { self.#ident }
                    }
                    FieldIdent::Index(idx) => {
                        let index = syn::Index::from(*idx);
                        quote! { self.#index }
                    }
                };

                let print_stmts = quote! {
                    <#ty as ::orzir_core::Print>::print(&#field, __ctx, __state)?;
                };

                Ok(print_stmts)
            }
        }
    }
}

fn generate_parser(
    struct_ident: &syn::Ident,
    derive_info: &OpDeriveInfo,
    format_info: &FormatInfo,
) -> syn::Result<TokenStream> {
    let mut parse_stmts = TokenStream::new();

    // format token to field mapping
    let token2field = derive_info
        .fields
        .iter()
        .map(|(field_ident, field_meta)| match field_ident {
            FieldIdent::Ident(ident) => (ident.clone(), (field_ident, field_meta)),
            FieldIdent::Index(idx) => (format!("{}", idx), (field_ident, field_meta)),
        })
        .collect::<HashMap<_, _>>();

    for token in &format_info.meta.pattern.tokens {
        match token {
            FormatToken::Field(field) => {
                let (field_ident, field_meta) = token2field.get(field).ok_or_else(|| {
                    syn::Error::new(
                        // TODO: Better span.
                        Span::call_site(),
                        format!("field `{}` not found in struct", field),
                    )
                })?;
                let field_parser = generate_field_parser(field_ident, field_meta, format_info)?;
                parse_stmts.extend(field_parser);
            }
            FormatToken::Delimiter(_) => {
                let delimiter_token = token.to_token();
                parse_stmts.extend(quote! {
                    __state.stream.expect(#delimiter_token)?;
                });
            }
            FormatToken::Whitespace(_) => {
                // just skip.
            }
            FormatToken::Tokenized(_) => {
                let token = token.to_token();
                parse_stmts.extend(quote! {
                    __state.stream.expect(#token)?;
                });
            }
        }
    }

    if let FormatKind::Op = format_info.meta.kind {
        let mut epilogue = quote! {
            let mut __result_names = __state.pop_result_names();
        };

        if let Some(0) = format_info.meta.num_results {
            // no trailing result types.
            epilogue.extend(quote! {
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
            });
        } else {
            epilogue.extend(quote! {
                let mut __tys = Vec::new();
                __state.stream.expect(::orzir_core::TokenKind::Char(':'))?;
                let __trailing_start_pos = __state.stream.curr_pos()?;

                if let ::orzir_core::TokenKind::Char('(') = __state.stream.peek()?.kind {
                    __state.stream.consume()?;
                    loop {
                        let __ty = <::orzir_core::TyObj as ::orzir_core::Parse>::parse(__ctx, __state)?;
                        __tys.push(__ty);
                        if let ::orzir_core::TokenKind::Char(',') = __state.stream.peek()?.kind {
                            __state.stream.consume()?;
                        } else {
                            break;
                        }
                    }
                    __state.stream.expect(::orzir_core::TokenKind::Char(')'))?;
                } else {
                    let __ty = <::orzir_core::TyObj as ::orzir_core::Parse>::parse(__ctx, __state)?;
                    __tys.push(__ty);
                }
                let __trailing_end_pos = __state.stream.curr_pos()?;
            });

            if let Some(num) = format_info.meta.num_results {
                epilogue.extend(quote! {
                    if __tys.len() != #num {
                        return ::orzir_core::parse_error!(
                            ::orzir_core::Span::new(__trailing_start_pos, __trailing_end_pos),
                            ::orzir_core::ParseErrorKind::InvalidTrailingTypeNumber(
                                #num,
                                __tys.len()
                            )
                        )
                        .into();
                    }

                    if __result_names.len() != #num {
                        let mut __span = __result_names[0].span;
                        for __name in __result_names.iter().skip(1) {
                            __span = __span.merge(&__name.span);
                        }
                        return ::orzir_core::parse_error!(
                            __span,
                            ::orzir_core::ParseErrorKind::InvalidResultNumber(
                                #num,
                                __result_names.len()
                            )
                        )
                        .into();
                    }
                });
            } else {
                epilogue.extend(quote! {
                    if __result_names.len() != __tys.len() {
                        let mut __span = __result_names[0].span;
                        for __name in __result_names.iter().skip(1) {
                            __span = __span.merge(&__name.span);
                        }
                        return ::orzir_core::parse_error!(
                            __span,
                            ::orzir_core::ParseErrorKind::InvalidResultNumber(
                                __tys.len(),
                                __result_names.len()
                            )
                        )
                        .into();
                    }
                });
            }

            epilogue.extend(
                quote! {
                    let mut __results = Vec::new();
                    for (__idx, (__name, __ty)) in __result_names.drain(..).zip(__tys.drain(..)).enumerate() {
                        let __result = ::orzir_core::Value::new_op_result(
                            __ctx,
                            __ty,
                            __op,
                            __idx,
                            Some(__name.unwrap_value_name())
                        );
                        __results.push(__result);
                    }
                }
            );
        }

        let mut result_assign = quote! {};

        let mut construction = quote! {};

        for (field_ident, field_meta) in derive_info.fields.iter() {
            let ident = match field_ident {
                FieldIdent::Ident(ident) => syn::Ident::new(ident, Span::call_site()),
                FieldIdent::Index(index) => {
                    syn::Ident::new(&format!("arg_{}", index), Span::call_site())
                }
            };

            match field_meta {
                OpFieldMeta::Result(index) => {
                    match index {
                        IndexKind::All => {
                            result_assign.extend(quote! {
                                let #ident = __results;
                            });
                        }
                        IndexKind::Range(start, end) => match end {
                            Some(end) => {
                                result_assign.extend(quote! {
                                    let #ident = __results[#start..#end].to_vec();
                                });
                            }
                            None => {
                                result_assign.extend(quote! {
                                    let #ident = __results[#start..].to_vec();
                                });
                            }
                        },
                        IndexKind::Single(idx) => {
                            result_assign.extend(quote! {
                                let #ident = __results[#idx];
                            });
                        }
                    }
                    construction.extend(quote! {
                        #ident,
                    });
                }
                OpFieldMeta::Metadata => match field_ident {
                    FieldIdent::Ident(_) => construction.extend(quote! {
                        #ident: ::orzir_core::OpMetadata::new(__op),
                    }),
                    FieldIdent::Index(_) => construction.extend(quote! {
                        ::orzir_core::OpMetadata::new(__op),
                    }),
                },
                _ => construction.extend(quote! {
                    #ident,
                }),
            }
        }

        let construction = if derive_info.is_named {
            quote! {
                let __instance = Self {
                    #construction
                };
            }
        } else {
            quote! {
                let __instance = Self(
                    #construction
                );
            }
        };

        let construction = quote! {
            #construction
            let __obj = ::orzir_core::OpObj::from(__instance);
            __ctx.ops.fill(__op, __obj);
        };

        parse_stmts = quote! {
            let __op = __ctx.ops.reserve();
            let __start_pos = __state.stream.curr_pos()?;

            __state.enter_component_from(__op);

            #parse_stmts

            let __end_pos = __state.stream.curr_pos()?;
            __state.exit_component();

            #epilogue
            #result_assign
            #construction

            Ok(__op)
        };

        parse_stmts = quote! {
            impl ::orzir_core::Parse for #struct_ident {
                type Item = ::orzir_core::ArenaPtr<::orzir_core::OpObj>;

                fn parse(
                    __ctx: &mut ::orzir_core::Context,
                    __state: &mut ::orzir_core::ParseState
                ) -> ::orzir_core::ParseResult<Self::Item> {
                    #parse_stmts
                }
            }
        }
    } else if let FormatKind::Ty = format_info.meta.kind {
        let mut construction = quote! {};

        for (field_ident, _) in derive_info.fields.iter() {
            let ident = match field_ident {
                FieldIdent::Ident(ident) => syn::Ident::new(ident, Span::call_site()),
                FieldIdent::Index(index) => {
                    syn::Ident::new(&format!("arg_{}", index), Span::call_site())
                }
            };

            construction.extend(quote! {
                #ident,
            });
        }

        let construction = quote! {
            let __ty = #struct_ident::get(__ctx, #construction);
        };

        parse_stmts = quote! {
            #parse_stmts
            #construction
            Ok(__ty)
        };

        parse_stmts = quote! {
            impl ::orzir_core::Parse for #struct_ident {
                type Item = ::orzir_core::ArenaPtr<::orzir_core::TyObj>;

                fn parse(
                    __ctx: &mut ::orzir_core::Context,
                    __state: &mut ::orzir_core::ParseState
                ) -> ::orzir_core::ParseResult<Self::Item> {
                    #parse_stmts
                }
            }
        }
    } else {
        let mut construction = quote! {};

        for (field_ident, _) in derive_info.fields.iter() {
            let ident = match field_ident {
                FieldIdent::Ident(ident) => syn::Ident::new(ident, Span::call_site()),
                FieldIdent::Index(index) => {
                    syn::Ident::new(&format!("arg_{}", index), Span::call_site())
                }
            };

            construction.extend(quote! {
                #ident,
            });
        }

        let construction = if derive_info.is_named {
            quote! {
                let __instance = Self {
                    #construction
                };
            }
        } else {
            quote! {
                let __instance = Self(
                    #construction
                );
            }
        };

        parse_stmts = quote! {
            #parse_stmts
            #construction
            Ok(__instance)
        };

        parse_stmts = quote! {
            impl ::orzir_core::Parse for #struct_ident {
                type Item = Self;

                fn parse(
                    __ctx: &mut ::orzir_core::Context,
                    __state: &mut ::orzir_core::ParseState
                ) -> ::orzir_core::ParseResult<Self::Item> {
                    #parse_stmts
                }
            }
        }
    }

    Ok(parse_stmts)
}

fn generate_printer(
    struct_ident: &syn::Ident,
    derive_info: &OpDeriveInfo,
    format_info: &FormatInfo,
) -> syn::Result<TokenStream> {
    let mut print_stmts = TokenStream::new();

    // format token to field mapping
    let token2field = derive_info
        .fields
        .iter()
        .map(|(field_ident, field_meta)| match field_ident {
            FieldIdent::Ident(ident) => (ident.clone(), (field_ident, field_meta)),
            FieldIdent::Index(idx) => (format!("{}", idx), (field_ident, field_meta)),
        })
        .collect::<HashMap<_, _>>();

    for token in &format_info.meta.pattern.tokens {
        match token {
            FormatToken::Field(field) => {
                let (field_ident, field_meta) = token2field.get(field).ok_or_else(|| {
                    syn::Error::new(
                        Span::call_site(),
                        format!("field `{}` not found in struct", field),
                    )
                })?;
                let field_printer = generate_field_printer(field_ident, field_meta, format_info)?;
                print_stmts.extend(field_printer);
            }
            FormatToken::Delimiter(_) => {
                let delimiter_printer = token.generate_printer();
                print_stmts.extend(delimiter_printer);
            }
            FormatToken::Whitespace(_) => {
                let whitespace_printer = token.generate_printer();
                print_stmts.extend(whitespace_printer);
            }
            FormatToken::Tokenized(_) => {
                let token_printer = token.generate_printer();
                print_stmts.extend(token_printer);
            }
        }
    }

    if let FormatKind::Op = format_info.meta.kind {
        // the trailing types
        if let Some(0) = format_info.meta.num_results {
            // no trailing result types.
        } else {
            print_stmts.extend(quote! {
                let __result_tys = <Self as ::orzir_core::DataFlow>::result_tys(&self, __ctx);
                write!(__state.buffer, " : ")?;
                if __result_tys.len() > 1 {
                    write!(__state.buffer, "(")?;
                }

                for (__idx, __ty) in __result_tys.iter().enumerate() {
                    <::orzir_core::TyObj as ::orzir_core::Print>::print(
                        __ty.deref(&__ctx.tys),
                        __ctx,
                        __state
                    )?;
                    if __idx + 1 < __result_tys.len() {
                        write!(__state.buffer, ", ")?;
                    }
                }

                if __result_tys.len() > 1 {
                    write!(__state.buffer, ")")?;
                }
            });
        }
    }

    let print_stmts = quote! {
        #print_stmts
        Ok(())
    };

    let print_stmts = quote! {
        impl ::orzir_core::Print for #struct_ident {
            fn print(
                &self,
                __ctx: &::orzir_core::Context,
                __state: &mut ::orzir_core::PrintState
            ) -> ::orzir_core::PrintResult<()> {
                #print_stmts
            }
        }
    };

    Ok(print_stmts)
}

fn derive_default_parse(ident: &syn::Ident) -> TokenStream {
    quote! {
        impl orzir_core::Parse for #ident {
            type Item = Self;

            fn parse(
                _: &mut orzir_core::Context,
                state: &mut orzir_core::ParseState
            ) -> orzir_core::ParseResult<Self::Item> {
                let token = state.stream.consume()?;
                if let orzir_core::TokenKind::Tokenized(s) = token.kind {
                    let self_ = <Self as TryFrom<&str>>::try_from(s.as_str())
                        .map_err(|e| orzir_core::parse_error!(token.span, e))?;
                    Ok(self_)
                } else {
                    orzir_core::parse_error!(
                        token.span,
                        orzir_core::ParseErrorKind::InvalidToken(
                            vec![orzir_core::token_wildcard!("...")].into(),
                            token.kind
                        )
                    )
                    .into()
                }
            }
        }
    }
}

fn derive_default_print(ident: &syn::Ident) -> TokenStream {
    quote! {
        impl orzir_core::Print for #ident {
            fn print(
                &self,
                _: &orzir_core::Context,
                state: &mut orzir_core::PrintState
            ) -> orzir_core::PrintResult<()> {
                write!(state.buffer, "{}", self)?;
                Ok(())
            }
        }
    }
}

pub fn derive_parse_impl(ast: &syn::DeriveInput) -> syn::Result<TokenStream> {
    let format_info = FormatInfo::from_ast(ast)?;

    if let FormatKind::Other = format_info.meta.kind {
        return Ok(derive_default_parse(&ast.ident));
    }

    let derive_info = OpDeriveInfo::from_ast(ast)?;
    let parse_impl = generate_parser(&ast.ident, &derive_info, &format_info)?;

    Ok(parse_impl)
}

pub fn derive_print_impl(ast: &syn::DeriveInput) -> syn::Result<TokenStream> {
    let format_info = FormatInfo::from_ast(ast)?;

    if let FormatKind::Other = format_info.meta.kind {
        return Ok(derive_default_print(&ast.ident));
    }

    let derive_info = OpDeriveInfo::from_ast(ast)?;
    let print_impl = generate_printer(&ast.ident, &derive_info, &format_info)?;

    Ok(print_impl)
}

#[cfg(test)]
mod tests {
    use quote::quote;

    #[test]
    fn test_0() {
        let src = quote! {
            #[mnemonic = "arith.iadd"]
            #[format(pattern = "{lhs} plus {rhs}", kind = "op", num_results = 1)]
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
            #[mnemonic = "arith.iadd"]
            #[format(pattern = "{lhs} plus {rhs}", num_results = 1)]
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
