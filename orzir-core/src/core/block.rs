use crate::support::storage::ArenaPtr;

use super::value::Value;

#[derive(Debug, Default)]
pub struct Block {
    /// Arguments of the block.
    args: Vec<ArenaPtr<Value>>,
    /// If this block is an entry.
    is_entry: bool,
}

impl Block {
    pub(crate) fn add_arg(&mut self, arg: ArenaPtr<Value>) -> usize {
        self.args.push(arg);
        self.args.len() - 1
    }

    pub(crate) fn args(&self) -> &[ArenaPtr<Value>] {
        &self.args
    }

    pub(crate) fn is_entry(&self) -> bool {
        self.is_entry
    }

    pub(crate) fn set_entry(&mut self, is_entry: bool) {
        self.is_entry = is_entry;
    }
}
