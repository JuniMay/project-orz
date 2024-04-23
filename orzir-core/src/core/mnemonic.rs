use core::fmt;
use std::{collections::HashMap, fmt::Write};

use super::parse::{ParseErrorKind, ParseState, TokenKind};
use crate::{
    parse_error, token_wildcard, Context, Parse, ParseResult, Print, PrintResult, PrintState,
};

/// A mnemonic segment.
///
/// Mnemonic segment represents one part of a mnemonic, and is punctuated by a
/// dot.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct MnemonicSegment(String);

impl From<&str> for MnemonicSegment {
    fn from(segment: &str) -> Self { Self(segment.to_string()) }
}

impl MnemonicSegment {
    /// Create a new mnemonic segment.
    pub fn new(segment: &str) -> Self { Self(segment.to_string()) }

    /// Get the string of the mnemonic segment.
    pub fn as_str(&self) -> &str { &self.0 }
}

/// A mnemonic.
///
/// A mnemonic is in the format of `dialect.op/attr/ty/...`.
/// Both the primary part and the secondary part are mnemonic segments.
/// The primary part is stored in the context, and the secondary part is stored
/// in the dialect.
///
/// If there are more than two parts in the mnemonic, the first dot will be used
/// to split.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Mnemonic {
    /// The primary part of the mnemonic.
    primary: MnemonicSegment,
    /// The secondary part of the mnemonic.
    secondary: MnemonicSegment,
}

impl Mnemonic {
    /// Create a new mnemonic.
    pub fn new(primary: &str, secondary: &str) -> Self {
        Self {
            primary: MnemonicSegment::new(primary),
            secondary: MnemonicSegment::new(secondary),
        }
    }

    /// Get the primary part of the mnemonic.
    pub fn primary(&self) -> &MnemonicSegment { &self.primary }

    /// Get the secondary part of the mnemonic.
    pub fn secondary(&self) -> &MnemonicSegment { &self.secondary }
}

impl fmt::Display for Mnemonic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}", self.primary.as_str(), self.secondary.as_str())
    }
}

macro_rules! map {
    ($($key:expr => $value:expr),* $(,)?) => {
        {
            let mut map = HashMap::new();
            $(
                map.insert($key, $value);
            )*
            map
        }
    };
}

impl Parse for Mnemonic {
    type Item = Mnemonic;

    fn parse(_: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        let shortcuts = map! {
            "func" => ("func", "func"),
        };

        let token = state.stream.consume()?;
        match token.kind {
            TokenKind::Tokenized(s) => {
                // remove the quotes.
                let s = if s.starts_with('"') && s.ends_with('"') {
                    &s[1..s.len() - 1]
                } else {
                    s.as_str()
                };
                let (primary, secondary) = match s.split_once('.') {
                    Some((primary, secondary)) => (primary, secondary),
                    None => {
                        if let Some(shortcut) = shortcuts.get(s) {
                            *shortcut
                        } else {
                            ("builtin", s)
                        }
                    }
                };
                Ok(Mnemonic::new(primary, secondary))
            }
            _ => parse_error!(
                token.span,
                ParseErrorKind::InvalidToken(vec![token_wildcard!("...")].into(), token.kind)
            )
            .into(),
        }
    }
}

impl Print for Mnemonic {
    fn print(&self, _: &Context, state: &mut PrintState) -> PrintResult<()> {
        if self.primary.as_str() == "builtin" {
            write!(state.buffer, "{}", self.secondary.as_str())?;
        } else {
            write!(
                state.buffer,
                "{}.{}",
                self.primary.as_str(),
                self.secondary.as_str()
            )?;
        }

        Ok(())
    }
}
