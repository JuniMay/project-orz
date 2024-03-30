use proc_macro2::TokenStream;
use quote::quote;

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
    Punct(String),
}

impl FormatToken {
    fn from_str(s: &str) -> Self {
        match s {
            ":" | "=" | "(" | ")" | "{" | "}" | "[" | "]" | "<" | ">" | "," | ";" | "-" => {
                Self::Punct(s.to_string())
            }
            "->" => Self::Punct(s.to_string()),
            _ => {
                // alphanumeric or underscore
                if s.chars().all(char::is_alphanumeric) || s.chars().all(|c| c == '_') {
                    Self::Ident(s.to_string())
                } else {
                    panic!("invalid format token: {}", s);
                }
            }
        }
    }
}

impl From<FormatToken> for TokenStream {
    fn from(token: FormatToken) -> Self {
        match token {
            FormatToken::Ident(ident) => {
                let ident = syn::Ident::new(&ident, proc_macro2::Span::call_site());
                quote!(#ident)
            }
            FormatToken::Punct(punct) => match punct.as_str() {
                "->" => quote!(::orzir_core::TokenKind::Arrow),
                _ => {
                    let ch = punct.chars().next().unwrap();
                    quote!(::orzir_core::TokenKind::Char(#ch))
                }
            },
        }
    }
}

struct FormatPattern {
    tokens: Vec<FormatToken>,
}

impl FormatPattern {
    fn from_str(s: &str) -> Self {
        let mut tokens = Vec::new();
        let mut iter = s.chars().peekable();

        while let Some(c) = iter.next() {
            match c {
                '{' => {
                    let mut ident = String::new();
                    for c in iter.by_ref() {
                        match c {
                            '}' => {
                                tokens.push(FormatToken::Ident(ident));
                                break;
                            }
                            _ => ident.push(c),
                        }
                    }
                }
                '}' => {
                    if let Some('}') = iter.peek() {
                        iter.next();
                    } else {
                        panic!("unmatched `}}`");
                    }
                }
                _ => {
                    if c.is_whitespace() {
                        continue;
                    }
                    let mut punct = String::new();
                    punct.push(c);
                    if c == '-' && iter.peek() == Some(&'>') {
                        punct.push(iter.next().unwrap());
                    }
                    tokens.push(FormatToken::Punct(punct));
                }
            }
        }

        Self { tokens }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_pattern() {
        let pattern = FormatPattern::from_str("{callee} {symbol},->,,;, {result} : {ty}");
        println!("{:?}", pattern.tokens);
        assert_eq!(pattern.tokens[0], FormatToken::Ident("callee".to_string()));
        assert_eq!(pattern.tokens[1], FormatToken::Ident("symbol".to_string()));
        assert_eq!(pattern.tokens[2], FormatToken::Punct(",".to_string()));
        assert_eq!(pattern.tokens[3], FormatToken::Punct("->".to_string()));
        assert_eq!(pattern.tokens[4], FormatToken::Punct(",".to_string()));
        assert_eq!(pattern.tokens[5], FormatToken::Punct(",".to_string()));
        assert_eq!(pattern.tokens[6], FormatToken::Punct(";".to_string()));
        assert_eq!(pattern.tokens[7], FormatToken::Punct(",".to_string()));
        assert_eq!(pattern.tokens[8], FormatToken::Ident("result".to_string()));
        assert_eq!(pattern.tokens[9], FormatToken::Punct(":".to_string()));
        assert_eq!(pattern.tokens[10], FormatToken::Ident("ty".to_string()));
    }
}
