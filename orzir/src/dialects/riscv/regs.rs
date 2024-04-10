use std::fmt::Write;

use orzir_macros::{Parse, Print, Ty, Verify};

/// Integer/General-purpose register of the RISC-V architecture
#[derive(Debug, Hash, PartialEq, Eq, Ty, Parse, Print, Verify)]
#[mnemonic = "rv.ireg"]
#[format(pattern = "< {0} >", kind = "ty")]
pub struct IReg(usize);

/// Floating point register
#[derive(Debug, Hash, PartialEq, Eq, Ty, Parse, Print, Verify)]
#[mnemonic = "rv.freg"]
#[format(pattern = "< {0} >", kind = "ty")]
pub struct FReg(usize);
