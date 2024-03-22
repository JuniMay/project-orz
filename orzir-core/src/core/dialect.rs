use std::collections::HashMap;

use crate::Mnemonic;

use super::{mnemonic::MnemonicSegment, operation::OpParseFn, ty::TypeParseFn};

pub struct Dialect {
    mnemonic: MnemonicSegment,
    ops: HashMap<Mnemonic, OpParseFn>,
    types: HashMap<Mnemonic, TypeParseFn>,
}

impl Dialect {
    pub fn new(mnemonic: MnemonicSegment) -> Self {
        Self {
            mnemonic,
            ops: HashMap::new(),
            types: HashMap::new(),
        }
    }

    pub fn mnemonic(&self) -> MnemonicSegment {
        self.mnemonic.clone()
    }

    pub fn add_op(&mut self, mnemonic: Mnemonic, parse_fn: OpParseFn) {
        self.ops.insert(mnemonic, parse_fn);
    }

    pub fn add_type(&mut self, mnemonic: Mnemonic, parse_fn: TypeParseFn) {
        self.types.insert(mnemonic, parse_fn);
    }

    pub fn get_op_parse_fn(&self, mnemonic: &Mnemonic) -> Option<&OpParseFn> {
        self.ops.get(mnemonic)
    }

    pub fn get_type_parse_fn(&self, mnemonic: &Mnemonic) -> Option<&TypeParseFn> {
        self.types.get(mnemonic)
    }
}
