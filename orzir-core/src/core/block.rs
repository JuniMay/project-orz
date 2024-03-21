use crate::support::storage::ArenaPtr;

use super::value::Value;

#[derive(Debug)]
pub struct Block {
    /// Arguments of the block.
    args: Vec<ArenaPtr<Value>>,
}
