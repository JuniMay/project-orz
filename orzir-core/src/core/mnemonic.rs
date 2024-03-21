/// A mnemonic segment.
///
/// Mnemonic segment represents one part of a mnemonic, and is punctuated by a dot.
#[derive(Debug, Hash, PartialEq, Eq)]
pub struct MnemonicSegment(String);

/// A mnemonic.
///
/// A mnemonic is in the format of `dialect.op/attr/ty/...`.
/// Both the primary part and the secondary part are mnemonic segments.
/// The primary part is stored in the context, and the secondary part is stored in the dialect.
///
/// If there are more than two parts in the mnemonic, the first dot will be used to split.
#[derive(Debug, Hash, PartialEq, Eq)]
pub struct Mnemonic {
    /// The primary part of the mnemonic.
    primary: MnemonicSegment,
    /// The secondary part of the mnemonic.
    secondary: MnemonicSegment,
}
