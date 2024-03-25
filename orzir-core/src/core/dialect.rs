use std::collections::HashMap;

use super::{mnemonic::MnemonicSegment, operation::OpParseFn, ty::TypeParseFn};
use crate::Mnemonic;

/// A dialect.
pub struct Dialect {
    /// The mnemonic of the dialect.
    mnemonic: MnemonicSegment,
    /// The operations and their parse functions.
    ops: HashMap<Mnemonic, OpParseFn>,
    /// The types and their parse functions.
    types: HashMap<Mnemonic, TypeParseFn>,
}

impl Dialect {
    /// Create an empty dialect from a mnemonic.
    pub fn new(mnemonic: MnemonicSegment) -> Self {
        Self {
            mnemonic,
            ops: HashMap::new(),
            types: HashMap::new(),
        }
    }

    /// Get the mnemonic of the dialect.
    pub fn mnemonic(&self) -> MnemonicSegment { self.mnemonic.clone() }

    /// Add an operation and its parse function.
    pub fn add_op(&mut self, mnemonic: Mnemonic, parse_fn: OpParseFn) {
        self.ops.insert(mnemonic, parse_fn);
    }

    /// Add a type and its parse function.
    pub fn add_type(&mut self, mnemonic: Mnemonic, parse_fn: TypeParseFn) {
        self.types.insert(mnemonic, parse_fn);
    }

    /// Get the operation parse function.
    pub fn get_op_parse_fn(&self, mnemonic: &Mnemonic) -> Option<&OpParseFn> {
        self.ops.get(mnemonic)
    }

    /// Get the type parse function.
    pub fn get_type_parse_fn(&self, mnemonic: &Mnemonic) -> Option<&TypeParseFn> {
        self.types.get(mnemonic)
    }
}
