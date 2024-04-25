use std::collections::HashMap;

use crate::{Mnemonic, MnemonicSegment, OpParseFn, TyParseFn};

/// A dialect.
///
/// Dialects define the operations and types that are available in a specific
/// language. This is the same as dialects in the MLIR, which make it possible
/// to extend the framework with new operations and types.
pub struct Dialect {
    /// The mnemonic of the dialect.
    mnemonic: MnemonicSegment,
    /// The operations and their parse functions.
    ops: HashMap<Mnemonic, OpParseFn>,
    /// The types and their parse functions.
    tys: HashMap<Mnemonic, TyParseFn>,
}

impl Dialect {
    /// Create an empty dialect from a mnemonic.
    pub fn new(mnemonic: MnemonicSegment) -> Self {
        Self {
            mnemonic,
            ops: HashMap::new(),
            tys: HashMap::new(),
        }
    }

    /// Get the mnemonic of the dialect.
    pub fn mnemonic(&self) -> MnemonicSegment { self.mnemonic.clone() }

    /// Add an operation and its parse function.
    pub fn add_op(&mut self, mnemonic: Mnemonic, parse_fn: OpParseFn) {
        self.ops.insert(mnemonic, parse_fn);
    }

    /// Add a type and its parse function.
    pub fn add_ty(&mut self, mnemonic: Mnemonic, parse_fn: TyParseFn) {
        self.tys.insert(mnemonic, parse_fn);
    }

    /// Get the operation parse function.
    pub fn get_op_parse_fn(&self, mnemonic: &Mnemonic) -> Option<&OpParseFn> {
        self.ops.get(mnemonic)
    }

    /// Get the type parse function.
    pub fn get_ty_parse_fn(&self, mnemonic: &Mnemonic) -> Option<&TyParseFn> {
        self.tys.get(mnemonic)
    }
}
