use anyhow::Result;

use crate::{Context, Parse, TokenStream};

use super::parse::TokenKind;

/// A mnemonic segment.
///
/// Mnemonic segment represents one part of a mnemonic, and is punctuated by a dot.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct MnemonicSegment(String);

impl MnemonicSegment {
    /// Create a new mnemonic segment.
    pub fn new(segment: &str) -> Self {
        Self(segment.to_string())
    }

    /// Get the string of the mnemonic segment.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// A mnemonic.
///
/// A mnemonic is in the format of `dialect.op/attr/ty/...`.
/// Both the primary part and the secondary part are mnemonic segments.
/// The primary part is stored in the context, and the secondary part is stored in the dialect.
///
/// If there are more than two parts in the mnemonic, the first dot will be used to split.
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
    pub fn primary(&self) -> &MnemonicSegment {
        &self.primary
    }

    /// Get the secondary part of the mnemonic.
    pub fn secondary(&self) -> &MnemonicSegment {
        &self.secondary
    }
}

impl Parse for Mnemonic {
    type Arg = ();
    type Item = Mnemonic;

    fn parse(_: (), _: &mut Context, stream: &mut TokenStream) -> Result<Self::Item> {
        let token = stream.consume()?;
        match token.kind {
            TokenKind::Tokenized(ref s) => {
                let (primary, secondary) = match s.split_once('.') {
                    Some((primary, secondary)) => (primary, secondary),
                    None => ("builtin", s.as_str()),
                };
                Ok(Mnemonic::new(primary, secondary))
            }
            TokenKind::Quoted(ref s) => {
                let (primary, secondary) = match s.split_once('.') {
                    Some((primary, secondary)) => (primary, secondary),
                    None => ("builtin", s.as_str()),
                };
                Ok(Mnemonic::new(primary, secondary))
            }
            _ => anyhow::bail!("expect a mnemonic."),
        }
    }
}
