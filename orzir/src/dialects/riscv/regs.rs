use orzir_macros::{Parse, Print, Ty, Verify};

use crate::verifiers::*;

/// Integer/General-purpose register of the RISC-V architecture
#[derive(Debug, Hash, PartialEq, Eq, Ty, Parse, Print, Verify)]
#[mnemonic = "rv.ireg"]
#[format(pattern = "", kind = "ty")]
#[verifiers(IntegerLikeTy)]
pub struct IReg;

/// Floating point register
#[derive(Debug, Hash, PartialEq, Eq, Ty, Parse, Print, Verify)]
#[mnemonic = "rv.freg"]
#[format(pattern = "", kind = "ty")]
#[verifiers(FloatLikeTy)]
pub struct FReg;
