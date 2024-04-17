//! Arbitrary precision integer.
//!
//! This module provides an arbitrary precision integer with signedless
//! semantics, and can be used in the arithmetic operations.
//!
//! The [ApInt] is a runtime fixed-width integer, i.e., unless explicitly
//! resized (or do operation on two integers with different width), the width of
//! the integer will not change after the arithmetic operations.
//!
//! The [ApInt] type is signedless and can be regarded as an arbitrary width
//! integer register. It is up to the operation to interpret the integer as
//! signed or unsigned.
//!
//! Note that the implementation is not very efficient currently, some
//! optimizations may be needed in the future.

use core::fmt;

use thiserror::Error;

use crate::{delimiter, parse_error, token_wildcard, Parse, Print};

/// A chunk in the [ApInt].
pub type ApIntChunk = u64;

/// An arbitrary precision integer with signedless semantics.
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct ApInt {
    /// The width of the integer in bits.
    width: usize,
    /// The chunks of the integer.
    ///
    /// The bits higher than the width should always be kept as `0`s.
    chunks: Vec<ApIntChunk>,
}

impl fmt::Debug for ApInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // hexadecimal
        write!(f, "ApInt ({} bits): ", self.width)?;
        write!(f, "0x")?;
        for chunk in self.chunks.iter().rev() {
            write!(f, "{:016x}", chunk)?;
        }
        Ok(())
    }
}

impl ApInt {
    /// Create a `0` with given width.
    pub fn zero(width: usize) -> Self {
        // ceil division to get the number of chunks
        let num_chunks = (width + ApIntChunk::BITS as usize - 1) / ApIntChunk::BITS as usize;
        Self {
            width,
            chunks: vec![0; num_chunks],
        }
    }

    /// Check if the integer is zero.
    pub fn is_zero(&self) -> bool { self.chunks.iter().all(|c| *c == 0) }

    /// Create a `1` with given width.
    pub fn one(width: usize) -> Self {
        let mut apint = Self::zero(width);
        apint.chunks[0] = 1;
        apint
    }

    /// Check if the integer is one.
    pub fn is_one(&self) -> bool {
        if self.chunks[0] != 1 {
            return false;
        }
        for chunk in self.chunks.iter().skip(1) {
            if *chunk != 0 {
                return false;
            }
        }
        true
    }

    /// Get the width of the integer.
    pub fn width(&self) -> usize { self.width }

    /// Get the mask of the last chunk.
    fn last_chunk_mask(&self) -> ApIntChunk {
        let bits = self.width % ApIntChunk::BITS as usize;
        if bits == 0 {
            // this chunk is full, the width is a multiple of the chunk size
            ApIntChunk::MAX
        } else {
            // this chunk is not full, mask the bits
            (1 << bits) - 1
        }
    }

    /// Truncate the last chunk to the last bit according to the width.
    fn truncate_last_chunk(&mut self) {
        *self.chunks.last_mut().unwrap() &= self.last_chunk_mask();
    }

    /// Inplace bitwise or operation.
    pub fn inplace_bitor(&mut self, other: &Self) {
        if self.width != other.width {
            panic!("the width of the two integers are not the same")
        }

        for (a, b) in self.chunks.iter_mut().zip(other.chunks.iter()) {
            *a |= *b;
        }
    }

    /// Inplace bitwise and operation.
    pub fn inplace_bitand(&mut self, other: &Self) {
        if self.width != other.width {
            panic!("the width of the two integers are not the same")
        }

        for (a, b) in self.chunks.iter_mut().zip(other.chunks.iter()) {
            *a &= *b;
        }
    }

    /// Inplace bitwise xor operation.
    pub fn inplace_bitxor(&mut self, other: &Self) {
        if self.width != other.width {
            panic!("the width of the two integers are not the same")
        }

        for (a, b) in self.chunks.iter_mut().zip(other.chunks.iter()) {
            *a ^= *b;
        }
    }

    /// Inplace bitwise not operation.
    pub fn inplace_bitnot(&mut self) {
        for chunk in self.chunks.iter_mut() {
            *chunk = !*chunk;
        }
        self.truncate_last_chunk();
    }

    /// Inplace addition operation.
    pub fn zeroext(&mut self, width: usize) {
        if width <= self.width {
            return;
        }
        let num_chunks = (width + ApIntChunk::BITS as usize - 1) / ApIntChunk::BITS as usize;
        self.chunks.resize(num_chunks, 0);
        self.width = width;
        self.truncate_last_chunk();
    }

    /// Inplace addition operation.
    pub fn signext(&mut self, width: usize) {
        if width <= self.width {
            return;
        }
        let old_width = self.width;
        let sign = self.highest_bit();
        self.zeroext(width);
        if sign {
            let mut ones = ApInt::all_ones(width - old_width);
            ones.inplace_widening_shl(old_width);
            self.inplace_bitor(&ones);
        }
    }

    /// Consumes the integer and zero extends it.
    pub fn into_signext(mut self, width: usize) -> Self {
        self.signext(width);
        self
    }

    /// Consumes the integer and zero extends it.
    pub fn into_zeroext(mut self, width: usize) -> Self {
        self.zeroext(width);
        self
    }

    /// Inplace addition operation.
    pub fn truncate(&mut self, width: usize) -> Self {
        if width >= self.width {
            panic!("truncation width is not smaller than the integer width");
        }

        let mut high = ApInt::zero(self.width - width);
        self.width = width;

        let num_chunks = (width + ApIntChunk::BITS as usize - 1) / ApIntChunk::BITS as usize;
        for (i, chunk) in self.chunks.drain(num_chunks..).enumerate() {
            high.chunks[i] = chunk;
        }

        // the number of bits of the last chunk of low
        let num_low_bits = (width % ApIntChunk::BITS as usize) as u32;
        // if the number of bits is not a multiple of the chunk size
        if num_low_bits != 0 {
            // shift left by the number of bits to be patched to the lowest chunk
            high.shl_by_bit(ApIntChunk::BITS - num_low_bits);
            // get the patch bits (the highest remaining bits of the last chunk of low)
            let patch_bits = self.chunks.last().unwrap() >> num_low_bits;
            // patch the lowest bits of the last chunk of low
            high.chunks[0] |= patch_bits;
            // clear the highest bits of the last chunk of low
            self.truncate_last_chunk();
        }

        high
    }

    /// Consumes the integer and truncates it.
    pub fn into_truncated(mut self, width: usize) -> (Self, Self) {
        let high = self.truncate(width);
        (self, high)
    }

    /// Inplace addition and return the carry.
    pub fn inplace_add(&mut self, rhs: &Self) -> bool {
        if self.width != rhs.width {
            panic!("the width of the two integers are not the same")
        }

        let mut carry = false;

        for (a, b) in self.chunks.iter_mut().zip(rhs.chunks.iter()) {
            let (sum, carry_0) = a.overflowing_add(*b);
            let (sum, carry_1) = sum.overflowing_add(u64::from(carry));
            *a = sum;
            carry = carry_0 || carry_1;
        }

        let last_chunk = *self.chunks.last().unwrap();
        self.truncate_last_chunk();
        carry |= *self.chunks.last().unwrap() != last_chunk;

        carry
    }

    /// Inplace subtraction and return the borrow.
    pub fn inplace_sub(&mut self, rhs: &Self) -> bool {
        if self.width != rhs.width {
            panic!("the width of the two integers are not the same")
        }

        let mut borrow = false;
        for (a, b) in self.chunks.iter_mut().zip(rhs.chunks.iter()) {
            let (diff, borrow_0) = a.overflowing_sub(*b);
            let (diff, borrow_1) = diff.overflowing_sub(u64::from(borrow));
            *a = diff;
            borrow = borrow_0 || borrow_1;
        }

        let last_chunk = *self.chunks.last().unwrap();
        self.truncate_last_chunk();
        borrow |= *self.chunks.last().unwrap() != last_chunk;

        borrow
    }

    /// Shift left by chunk number.
    fn shl_by_chunk(&mut self, chunk_shamt: usize) {
        if chunk_shamt == 0 {
            return;
        }

        let num_chunks = self.chunks.len();
        if chunk_shamt >= num_chunks {
            self.chunks.iter_mut().for_each(|c| *c = 0);
            return;
        }

        for i in (0..num_chunks - chunk_shamt).rev() {
            self.chunks[i + chunk_shamt] = self.chunks[i];
        }

        for i in 0..chunk_shamt {
            self.chunks[i] = 0;
        }
    }

    /// Shift left by bit number.
    fn shl_by_bit(&mut self, shamt: u32) {
        if shamt >= ApIntChunk::BITS {
            panic!("shamt is larger than the width of a chunk");
        }

        if shamt == 0 {
            return;
        }

        // the number of bits shifted within a chunk
        let num_low_bits = ApIntChunk::BITS - shamt;
        // the overflowed part of the last chunk
        let mut patch_bits = 0u64;

        for chunk in self.chunks.iter_mut() {
            let new_patch_bits = *chunk >> num_low_bits;
            *chunk = (*chunk << shamt) | patch_bits;
            patch_bits = new_patch_bits;
        }

        self.truncate_last_chunk();
    }

    /// Inplace shift left and widen the integer.
    pub fn inplace_widening_shl(&mut self, shamt: usize) {
        self.zeroext(self.width + shamt);
        self.shl_by_chunk(shamt / ApIntChunk::BITS as usize);
        self.shl_by_bit((shamt % ApIntChunk::BITS as usize) as u32);
    }

    /// Inplace shift left and return the overflow.
    pub fn inplace_carrying_shl(&mut self, shamt: usize) -> Self {
        let old_width = self.width;
        self.inplace_widening_shl(shamt);
        self.truncate(old_width)
    }

    /// Get the highest bit of the integer.
    pub fn highest_bit(&self) -> bool {
        let last_chunk_bits = (self.width % ApIntChunk::BITS as usize) as u32;
        let last_chunk_bits = if last_chunk_bits == 0 {
            ApIntChunk::BITS
        } else {
            last_chunk_bits
        };
        let last_chunk_leading_zeros = self.chunks.last().unwrap().leading_zeros();
        match ApIntChunk::BITS.cmp(&(last_chunk_bits + last_chunk_leading_zeros)) {
            std::cmp::Ordering::Equal => true,
            std::cmp::Ordering::Less => false,
            std::cmp::Ordering::Greater => unreachable!(),
        }
    }

    /// Get the lowest bit of the integer.
    pub fn all_ones(width: usize) -> Self {
        let mut apint = ApInt::zero(width);
        for chunk in apint.chunks.iter_mut() {
            *chunk = ApIntChunk::MAX;
        }
        apint.truncate_last_chunk();
        apint
    }

    /// Inplace negation.
    pub fn inplace_neg(&mut self) {
        self.inplace_bitnot();
        self.inplace_add(&ApInt::one(self.width));
    }

    /// Inplace absolute value and return the sign.
    pub fn inplace_abs(&mut self) -> bool {
        if self.highest_bit() {
            self.inplace_neg();
            true
        } else {
            false
        }
    }

    /// Consumes the integer and return the absolute value and the sign.
    pub fn into_abs(mut self) -> (Self, bool) {
        let sign = self.inplace_abs();
        (self, sign)
    }

    /// Inplace widening unsigned multiplication by a chunk.
    ///
    /// This operation widen the integer by one chunk width.
    pub fn inplace_widening_umul_chunk(&mut self, chunk: ApIntChunk) {
        let mut carry = 0u128;

        for a in self.chunks.iter_mut() {
            let product = u128::from(*a) * u128::from(chunk) + carry;
            *a = product as ApIntChunk;
            carry = product >> ApIntChunk::BITS;
        }
        self.zeroext(self.width + ApIntChunk::BITS as usize);
        *self.chunks.last_mut().unwrap() = carry as ApIntChunk;
    }

    /// Shrinks the integer to minimum width.
    pub fn shrink_to_fit(&mut self) {
        let mut width = self.width;
        while width > 1 && self.chunks.last().unwrap() == &0 {
            self.chunks.pop();
            width -= ApIntChunk::BITS as usize;
        }
        let num_chunks = self.chunks.len();
        let last_chunk_width = ApIntChunk::BITS - self.chunks.last().unwrap().leading_zeros();
        let new_width = (num_chunks - 1) * ApIntChunk::BITS as usize + last_chunk_width as usize;
        self.width = new_width;
    }

    /// Consumes the integer and return the shrunk integer.
    pub fn into_shrunk(self) -> Self {
        let mut apint = self;
        apint.shrink_to_fit();
        apint
    }

    /// Inplace carrying unsigned multiplication by a chunk.
    pub fn inplace_carrying_umul_chunk(&mut self, chunk: ApIntChunk) -> Self {
        let old_width = self.width;
        self.inplace_widening_umul_chunk(chunk);
        self.truncate(old_width)
    }

    /// Inplace widening unsigned multiplication.
    pub fn inplace_widening_umul(&mut self, rhs: &Self) {
        if self.width != rhs.width {
            panic!("the width of the two integers are not the same")
        }

        if self.width * 2 <= ApIntChunk::BITS as usize {
            let product = self.chunks[0] * rhs.chunks[0];
            self.zeroext(self.width * 2);
            self.chunks[0] = product;
            return;
        }

        let num_chunks =
            (self.width * 2 + ApIntChunk::BITS as usize - 1) / ApIntChunk::BITS as usize;
        // the temporary result of the multiplication
        let mut tmp_result: Vec<u128> = vec![0; num_chunks];

        for (i, chunk) in self.chunks.drain(..).enumerate() {
            let mut widened = rhs.clone();
            widened.inplace_widening_umul_chunk(chunk);
            for (j, r) in widened.chunks.drain(..).enumerate() {
                tmp_result[i + j] += u128::from(r);
            }
        }

        let mut carry = 0u128;
        for r in tmp_result.iter_mut() {
            let sum = *r + carry;
            *r = sum;
            carry = sum >> ApIntChunk::BITS;
        }

        for r in tmp_result.iter() {
            self.chunks.push(*r as ApIntChunk);
        }

        self.width *= 2;
    }

    /// Inplace widening signed multiplication.
    pub fn inplace_widening_smul(&mut self, rhs: &Self) {
        let lhs_sign = self.inplace_abs();
        let (rhs, rhs_sign) = rhs.clone().into_abs();

        self.inplace_widening_umul(&rhs);

        if lhs_sign ^ rhs_sign {
            self.inplace_neg();
        }
    }

    /// Inplace carrying signed multiplication, return the overflow.
    pub fn inplace_carrying_umul(&mut self, rhs: &Self) -> Self {
        let old_width = self.width;
        self.inplace_widening_umul(rhs);
        self.truncate(old_width)
    }

    /// Inplace carrying signed multiplication, return the overflow.
    pub fn inplace_carrying_smul(&mut self, rhs: &Self) -> Self {
        let old_width = self.width;
        self.inplace_widening_smul(rhs);
        self.truncate(old_width)
    }

    /// Inplace logical shift right and return the discarded bits.
    pub fn inplace_lshr(&mut self, shamt: usize) -> Self {
        let old_width = self.width;
        let mut truncated = self.truncate(shamt);
        truncated.zeroext(old_width);
        std::mem::swap(self, &mut truncated);
        truncated
    }

    /// Inplace arithmetic shift right and return the discarded bits.
    pub fn inplace_ashr(&mut self, shamt: usize) -> Self {
        let old_width = self.width;
        let mut truncated = self.truncate(shamt);
        truncated.signext(old_width);
        std::mem::swap(self, &mut truncated);
        truncated
    }

    /// Unsigned division and return the remainder.
    pub fn inplace_udiv(&mut self, divisor: &Self) -> Self {
        if self.width != divisor.width {
            panic!("the width of the two integers are not the same")
        }

        let width = self.width;
        let mut remainder = ApInt::zero(width);

        for _ in 0..width {
            let set_bit = if remainder.ge(divisor) {
                remainder.inplace_sub(divisor);
                true
            } else {
                false
            };

            let carry = self.inplace_carrying_shl(1);
            self.chunks[0] |= u64::from(set_bit);

            remainder.inplace_carrying_shl(1);
            remainder.chunks[0] |= u64::from(!carry.is_zero());
        }

        let set_bit = if remainder.ge(divisor) {
            remainder.inplace_sub(divisor);
            true
        } else {
            false
        };

        let _carry = self.inplace_carrying_shl(1);
        self.chunks[0] |= u64::from(set_bit);

        remainder
    }

    /// Signed division and return the remainder.
    pub fn inplace_sdiv(&mut self, divisor: &Self) -> Self {
        let lhs_sign = self.inplace_abs();
        let (rhs, rhs_sign) = divisor.clone().into_abs();

        let mut remainder = self.inplace_udiv(&rhs);

        if lhs_sign ^ rhs_sign {
            self.inplace_neg();
        }

        if lhs_sign {
            remainder.inplace_neg();
        }

        remainder
    }
}

impl From<Vec<ApIntChunk>> for ApInt {
    fn from(chunks: Vec<ApIntChunk>) -> Self {
        let width = chunks.len() * ApIntChunk::BITS as usize;
        Self { width, chunks }
    }
}

impl From<u8> for ApInt {
    fn from(value: u8) -> Self {
        let mut apint = ApInt::zero(8);
        apint.chunks[0] = value as ApIntChunk;
        apint
    }
}

impl From<i8> for ApInt {
    fn from(value: i8) -> Self {
        let sign = value < 0;
        let mut apint = ApInt::zero(8);
        apint.chunks[0] = value.unsigned_abs() as ApIntChunk;
        if sign {
            apint.inplace_neg();
        }
        apint
    }
}

impl From<u16> for ApInt {
    fn from(value: u16) -> Self {
        let mut apint = ApInt::zero(16);
        apint.chunks[0] = value as ApIntChunk;
        apint
    }
}

impl From<i16> for ApInt {
    fn from(value: i16) -> Self {
        let sign = value < 0;
        let mut apint = ApInt::zero(16);
        apint.chunks[0] = value.unsigned_abs() as ApIntChunk;
        if sign {
            apint.inplace_neg();
        }
        apint
    }
}

impl From<u32> for ApInt {
    fn from(value: u32) -> Self {
        let mut apint = ApInt::zero(32);
        apint.chunks[0] = value as ApIntChunk;
        apint
    }
}

impl From<i32> for ApInt {
    fn from(value: i32) -> Self {
        let sign = value < 0;
        let mut apint = ApInt::zero(32);
        apint.chunks[0] = value.unsigned_abs() as ApIntChunk;
        if sign {
            apint.inplace_neg();
        }
        apint
    }
}

impl From<u64> for ApInt {
    fn from(value: u64) -> Self {
        let mut apint = ApInt::zero(64);
        apint.chunks[0] = value as ApIntChunk;
        apint
    }
}

impl From<i64> for ApInt {
    fn from(value: i64) -> Self {
        let sign = value < 0;
        let mut apint = ApInt::zero(64);
        apint.chunks[0] = value.unsigned_abs() as ApIntChunk;
        if sign {
            apint.inplace_neg();
        }
        apint
    }
}

impl PartialOrd for ApInt {
    /// Compare two integers as unsigned integers.
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self.width != other.width {
            // if there are `1` in the higher bits of the integer with larger width,
            // the integer is larger
            if self.width > other.width {
                // check the higher chunks of self
                for chunk in self.chunks.iter().skip(other.chunks.len()) {
                    if *chunk != 0 {
                        return Some(std::cmp::Ordering::Greater);
                    }
                }
            } else {
                // check the higher chunks of other
                for chunk in other.chunks.iter().skip(self.chunks.len()) {
                    if *chunk != 0 {
                        return Some(std::cmp::Ordering::Less);
                    }
                }
            }
            // if no higher bits are set, just compare as the same width
        }
        for (a, b) in self.chunks.iter().zip(other.chunks.iter()).rev() {
            match a.cmp(b) {
                std::cmp::Ordering::Equal => continue,
                ord => return Some(ord),
            }
        }
        Some(std::cmp::Ordering::Equal)
    }
}

impl Ord for ApInt {
    /// Compare two integers as unsigned integers.
    fn cmp(&self, other: &Self) -> std::cmp::Ordering { self.partial_cmp(other).unwrap() }
}

#[derive(Debug, Error)]
pub enum ApIntParseError {
    #[error("invalid literal: {0}")]
    InvalidLiteral(String),

    #[error("integer out of range, expected width: {0}, actual width: {1}")]
    OutOfRange(usize, usize),
}

impl TryFrom<&str> for ApInt {
    type Error = ApIntParseError;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        if s == "true" {
            return Ok(ApInt::one(1));
        } else if s == "false" {
            return Ok(ApInt::zero(1));
        }

        let radix = if s.starts_with("0x") {
            16
        } else if s.starts_with("0b") {
            2
        } else if s.starts_with("0o") {
            8
        } else {
            10
        };

        let s = s
            .trim_start_matches("0x")
            .trim_start_matches("0b")
            .trim_start_matches("0o");

        let (s, bits) = if let Some(idx) = s.find('i') {
            let (s, bits) = s.split_at(idx);
            let width = bits
                .trim_start_matches('i')
                .parse::<usize>()
                .map_err(|_| ApIntParseError::InvalidLiteral(s.to_string()))?;
            (s, Some(width))
        } else {
            (s, None)
        };

        let mut apint = ApInt::zero(1);

        for c in s.chars() {
            let digit = c
                .to_digit(radix)
                .ok_or_else(|| ApIntParseError::InvalidLiteral(s.to_string()))?;
            apint.inplace_widening_umul_chunk(radix as ApIntChunk);
            let digit = ApInt::from(digit);

            if apint.width > digit.width {
                apint.inplace_add(&digit.into_zeroext(apint.width));
            } else {
                apint.zeroext(digit.width);
                apint.inplace_add(&digit);
            }

            apint = apint.into_shrunk();
        }

        if let Some(bits) = bits {
            if bits < apint.width {
                return Err(ApIntParseError::OutOfRange(bits, apint.width));
            } else {
                apint = apint.into_zeroext(bits);
            }
        }

        Ok(apint)
    }
}

impl Parse for ApInt {
    type Item = Self;

    fn parse(
        _: &mut crate::Context,
        state: &mut crate::ParseState,
    ) -> crate::ParseResult<Self::Item> {
        let neg = matches!(state.stream.consume_if(delimiter!('-'))?, Some(_));
        let token = state.stream.consume()?;
        let mut value = match token.kind {
            crate::TokenKind::Tokenized(s) => {
                ApInt::try_from(s).map_err(|e| parse_error!(token.span, e))?
            }
            _ => {
                return parse_error!(
                    token.span,
                    crate::ParseErrorKind::InvalidToken(
                        vec![token_wildcard!("...")].into(),
                        token.kind
                    )
                )
                .into();
            }
        };

        if neg {
            value.inplace_neg();
        }

        Ok(value)
    }
}

impl Print for ApInt {
    fn print(&self, _: &crate::Context, state: &mut crate::PrintState) -> crate::PrintResult<()> {
        use std::fmt::Write;
        write!(state.buffer, "{:x}", self)?;
        Ok(())
    }
}

impl TryFrom<String> for ApInt {
    type Error = ApIntParseError;

    fn try_from(value: String) -> Result<Self, Self::Error> { ApInt::try_from(value.as_str()) }
}

impl fmt::Binary for ApInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "0b")?;
        let last_chunk_width = self.width % ApIntChunk::BITS as usize;
        let last_chunk_width = if last_chunk_width == 0 {
            ApIntChunk::BITS as usize
        } else {
            last_chunk_width
        };
        write!(
            f,
            "{:0width$b}",
            self.chunks.last().unwrap(),
            width = last_chunk_width
        )?;
        for chunk in self.chunks.iter().rev().skip(1) {
            write!(f, "{:064b}", chunk)?;
        }
        write!(f, "i{}", self.width)?;
        Ok(())
    }
}

impl fmt::LowerHex for ApInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "0x")?;
        let last_chunk_width = self.width % ApIntChunk::BITS as usize;
        let last_chunk_width = if last_chunk_width == 0 {
            ApIntChunk::BITS as usize / 4
        } else {
            (last_chunk_width + 3) / 4
        };
        if last_chunk_width != 0 {
            write!(
                f,
                "{:0width$x}",
                self.chunks.last().unwrap(),
                width = last_chunk_width
            )?;
        }
        for chunk in self.chunks.iter().rev().skip(1) {
            write!(f, "{:016x}", chunk)?;
        }
        write!(f, "i{}", self.width)?;
        Ok(())
    }
}

impl fmt::UpperHex for ApInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "0x")?;
        let last_chunk_width = self.width % ApIntChunk::BITS as usize;
        let last_chunk_width = if last_chunk_width == 0 {
            ApIntChunk::BITS as usize / 4
        } else {
            (last_chunk_width + 3) / 4
        };
        write!(
            f,
            "{:0width$X}",
            self.chunks.last().unwrap(),
            width = last_chunk_width
        )?;
        for chunk in self.chunks.iter().rev().skip(1) {
            write!(f, "{:016X}", chunk)?;
        }
        write!(f, "i{}", self.width)?;
        Ok(())
    }
}

impl fmt::Display for ApInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::new();
        let mut tmp = self.clone();

        while !tmp.is_zero() {
            let remainder = tmp.inplace_udiv(&ApInt::from(10u32));
            s.push_str(&remainder.chunks[0].to_string());
        }

        if s.is_empty() {
            s.push('0');
        }

        write!(f, "{}", s.chars().rev().collect::<String>())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_inplace_neg_0() {
        let mut a = ApInt::from(123u32);
        a.inplace_neg();
        assert_eq!(a.width, 32);
        assert_eq!(a.chunks, vec![0xffffff85u64]);
    }

    #[test]
    fn test_inplace_neg_1() {
        let mut a = ApInt::from(123u32).into_zeroext(128);
        a.inplace_neg();
        assert_eq!(a.width, 128);
        assert_eq!(a.chunks, vec![0xffffffffffffff85u64, 0xffffffffffffffff]);
    }

    #[test]
    fn test_fmt_binary() {
        let a = ApInt::from(0x123u32).into_truncated(9).0;
        assert_eq!(format!("{:b}", a), "0b100100011i9");
    }

    #[test]
    fn test_fmt_lower_hex() {
        let a = ApInt::from(vec![0xffffffffffffffff, 0x1])
            .into_truncated(65)
            .0;
        assert_eq!(format!("{:x}", a), "0x1ffffffffffffffffi65");
    }

    #[test]
    fn test_fmt_upper_hex() {
        let a = ApInt::from(vec![0xffffffffffffffff, 0x1])
            .into_truncated(65)
            .0;
        assert_eq!(format!("{:X}", a), "0x1FFFFFFFFFFFFFFFFi65");
    }

    #[test]
    fn test_to_string() {
        let a = ApInt::from(123u32);
        assert_eq!(a.to_string(), "123");
    }

    #[test]
    fn test_from_str_0() {
        let a = ApInt::try_from("0x82345678").unwrap();
        let expected = ApInt::from(0x82345678u32);
        assert_eq!(a, expected);
    }

    #[test]
    fn test_from_str_1() {
        let a = ApInt::try_from("0b1010101010101010").unwrap();
        let expected = ApInt::from(0b1010101010101010u16);
        assert_eq!(a, expected);
    }

    #[test]
    fn test_from_str_2() {
        let a = ApInt::try_from("0o123").unwrap();
        let expected = ApInt::from(0o123u8).into_truncated(7).0;
        assert_eq!(a, expected);
    }

    #[test]
    fn test_from_str_3() {
        let a = ApInt::try_from("1234567890i34").unwrap();
        let expected = ApInt::from(1234567890u32).into_zeroext(34);
        assert_eq!(a, expected);
    }

    #[test]
    fn test_from_signed_0() {
        let a = ApInt::from(-1i8);
        assert_eq!(a.width, 8);
        assert_eq!(a.chunks, vec![0xffu64,]);
    }

    #[test]
    fn test_from_signed_1() {
        let a = ApInt::from(-5i16);
        assert_eq!(a.width, 16);
        assert_eq!(a.chunks, vec![0xfffbu64,]);
    }

    #[test]
    fn test_from_signed_2() {
        let a = ApInt::from(-5i32);
        assert_eq!(a.width, 32);
        assert_eq!(a.chunks, vec![0xffff_fffbu64,]);
    }

    #[test]
    fn test_from_signed_3() {
        let a = ApInt::from(-16i64);
        assert_eq!(a.width, 64);
        assert_eq!(a.chunks, vec![0xffff_ffff_ffff_fff0u64,]);
    }

    #[test]
    fn test_from_str_4() {
        let a =
            ApInt::try_from("0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef")
                .unwrap();
        let expected = ApInt::from(vec![
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
        ])
        .into_truncated(253)
        .0;
        assert_eq!(a, expected);
    }

    #[test]
    fn test_highest_bit() {
        let a = ApInt::from(0x12345678u32);
        assert!(!a.highest_bit());
        let a = ApInt::from(0x82345678u32);
        assert!(a.highest_bit());
    }

    #[test]
    fn test_ord_0() {
        let a = ApInt::from(123u32).into_zeroext(128);
        let b = ApInt::from(256u32);
        assert!(a < b);
    }

    #[test]
    fn test_ord_1() {
        let a = ApInt::from(vec![0, 0x1]);
        let b = ApInt::from(256u32);
        assert!(a > b);
    }

    #[test]
    fn test_signext_0() {
        let a = ApInt::from(0x12345678u32).into_truncated(29).0;
        let a = a.into_signext(64);
        assert_eq!(a.chunks, vec![0xfffffffff2345678u64]);
    }

    #[test]
    fn test_inplace_add() {
        let mut a = ApInt::from(0x12345678u32);
        let b = ApInt::from(0x87654321u32);
        let carry = a.inplace_add(&b);
        assert_eq!(a.chunks, vec![0x99999999]);
        assert!(!carry);
    }

    #[test]
    fn test_inplace_add_carry_0() {
        let mut a = ApInt::from(0x12345678u32);
        let b = ApInt::from(0xf7654321u32);
        let carry = a.inplace_add(&b);
        assert_eq!(a.chunks, vec![0x09999999]);
        assert!(carry);
    }

    #[test]
    fn test_inplace_add_carry_1() {
        let mut a = ApInt::from(vec![0x123456781234u64, 0x56784321u64])
            .into_truncated(96)
            .0;
        let b = ApInt::from(vec![0xf76543214321u64, 0xf3211234u64])
            .into_truncated(96)
            .0;

        let carry = a.inplace_add(&b);

        assert_eq!(a.chunks, vec![0x1099999995555u64, 0x49995555u64]);
        assert!(carry);
    }

    #[test]
    fn test_inplace_add_carry_2() {
        let mut a = ApInt::from(vec![0xffffffff88888888u64, 0xffffffffu64])
            .into_truncated(96)
            .0;
        let b = ApInt::from(vec![0xffffffff88888888u64, 0xffffffffu64])
            .into_truncated(96)
            .0;

        let carry = a.inplace_add(&b);

        assert_eq!(a.chunks, vec![0xffffffff11111110u64, 0xffffffffu64]);
        assert!(carry);
    }

    #[test]
    fn test_truncate_0() {
        let a = ApInt::from(vec![
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
        ]);
        let (low, high) = a.into_truncated(96);

        assert_eq!(low.chunks, vec![0x1234567890abcdefu64, 0x90abcdefu64]);
        assert_eq!(high.chunks, vec![0x90abcdef12345678u64, 0x12345678u64]);
    }

    #[test]
    fn test_truncate_1() {
        let a = ApInt::from(vec![
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
        ]);
        let (low, high) = a.into_truncated(128);

        assert_eq!(
            low.chunks,
            vec![0x1234567890abcdefu64, 0x1234567890abcdefu64]
        );
        assert_eq!(high.chunks, vec![0x1234567890abcdefu64]);
    }

    #[test]
    fn test_truncate_2() {
        let a = ApInt::from(vec![
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
        ]);
        let (low, high) = a.into_truncated(32);

        assert_eq!(low.chunks, vec![0x90abcdefu64]);
        assert_eq!(
            high.chunks,
            vec![0x90abcdef12345678u64, 0x90abcdef12345678u64, 0x12345678u64]
        );
    }

    #[test]
    fn test_truncate_3() {
        let a = ApInt::from(vec![
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
        ]);
        let (low, high) = a.into_truncated(8);

        assert_eq!(low.chunks, vec![0xefu64]);
        assert_eq!(
            high.chunks,
            vec![
                0xef1234567890abcdu64,
                0xef1234567890abcdu64,
                0x1234567890abcdu64
            ]
        );
    }

    #[test]
    fn test_truncate_4() {
        let a = ApInt::from(vec![
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
        ]);
        let (low, high) = a.into_truncated(64);

        assert_eq!(low.chunks, vec![0x1234567890abcdefu64]);
        assert_eq!(
            high.chunks,
            vec![0x1234567890abcdefu64, 0x1234567890abcdefu64]
        );
    }

    #[test]
    fn test_inplace_sub_borrow_0() {
        let mut a = ApInt::from(0x12345678u32);
        let b = ApInt::from(0x87654321u32);
        let borrow = a.inplace_sub(&b);
        assert_eq!(a.chunks, vec![0x8acf1357u64]);
        assert!(borrow);
    }

    #[test]
    fn test_inplace_sub_0() {
        let a = ApInt::from(0x12345678u32);
        let mut b = ApInt::from(0x87654321u32);
        let borrow = b.inplace_sub(&a);
        assert_eq!(b.chunks, vec![0x7530eca9u64]);
        assert!(!borrow);
    }

    #[test]
    fn test_inplace_sub_2() {
        let mut a = ApInt::from(0x12345678u32);
        let b = ApInt::from(0x12345678u32);
        let borrow = a.inplace_sub(&b);
        assert_eq!(a.chunks, vec![0]);
        assert!(!borrow);
    }

    #[test]
    fn test_inplace_sub_1() {
        let mut a = ApInt::from(vec![0x1122334455667788u64, 0x9900aabbccddeeffu64]);
        let b = ApInt::from(vec![0x2233445566778899u64, 0x00aabbccddeeff22u64]);

        let borrow = a.inplace_sub(&b);

        assert_eq!(a.chunks, vec![0xeeeeeeeeeeeeeeefu64, 0x9855eeeeeeeeefdcu64]);
        assert!(!borrow);
    }

    #[test]
    fn test_inplace_sub_borrow_1() {
        let a = ApInt::from(vec![0x1122334455667788u64, 0x9900aabbccddeeffu64]);
        let mut b = ApInt::from(vec![0x2233445566778899u64, 0x00aabbccddeeff22u64]);

        let borrow = b.inplace_sub(&a);

        assert!(borrow);
        assert_eq!(b.chunks, vec![0x1111111111111111u64, 0x67aa111111111023u64]);
    }

    #[test]
    fn test_widening_umul_chunk_0() {
        let mut a = ApInt::from(vec![0x1234567890abcdefu64, 0x1234u64])
            .into_truncated(80)
            .0;
        let b = 0x1234u64;
        a.inplace_widening_umul_chunk(b);
        assert_eq!(a.width, 144);
        assert_eq!(a.chunks, vec![0x60b60aa97760a28cu64, 0x14b5bdbu64, 0]);
    }

    #[test]
    fn test_widening_umul_chunk_1() {
        let mut a = ApInt::from(123u32);
        let b = 1234u64;

        a.inplace_widening_umul_chunk(b);

        assert_eq!(a.width, 96);
        assert_eq!(a.chunks, vec![0x250e6, 0]);
    }

    #[test]
    fn test_carrying_umul_chunk_0() {
        let mut a = ApInt::from(123u32).into_truncated(8).0;
        let b = 1234u64;

        let carry = a.inplace_carrying_umul_chunk(b);

        assert_eq!(a.chunks, vec![0xe6]);
        assert_eq!(a.width, 8);
        assert_eq!(carry.chunks, vec![0x250]);
        assert_eq!(carry.width, 64);
    }

    #[test]
    fn test_carrying_umul_chunk_1() {
        let mut a = ApInt::from(vec![0x1234567890abcdefu64, 0x1234u64])
            .into_truncated(80)
            .0;
        let b = 0x1234u64;

        let carry = a.inplace_carrying_umul_chunk(b);

        assert_eq!(a.chunks, vec![0x60b60aa97760a28cu64, 0x5bdbu64]);
        assert_eq!(a.width, 80);
        assert_eq!(carry.chunks, vec![0x14b]);
        assert_eq!(carry.width, 64);
    }

    #[test]
    fn test_carrying_shl_0() {
        let mut a = ApInt::from(0x12345678u32);
        let carry = a.inplace_carrying_shl(4);
        assert_eq!(a.chunks, vec![0x23456780u64]);
        assert_eq!(a.width, 32);
        assert_eq!(carry.chunks, vec![1]);
        assert_eq!(carry.width, 4);
    }

    #[test]
    fn test_carrying_shl_1() {
        let mut a = ApInt::from(vec![0x1234567890abcdefu64, 0x0000567890abcdefu64])
            .into_truncated(112)
            .0;
        let carry = a.inplace_carrying_shl(72);
        assert_eq!(a.chunks, vec![0, 0x00007890abcdef00u64]);
        assert_eq!(a.width, 112);
        // 0x56_7890_abcd_ef12_3456
        assert_eq!(carry.chunks, vec![0x7890abcdef123456u64, 0x56u64]);
        assert_eq!(carry.width, 72);
    }

    #[test]
    fn test_widening_shl_0() {
        let mut a = ApInt::from(0x12345678u32);
        a.inplace_widening_shl(4);
        assert_eq!(a.chunks, vec![0x123456780u64]);
        assert_eq!(a.width, 36);
    }

    #[test]
    fn test_widening_shl_1() {
        let mut a = ApInt::from(vec![0x1234567890abcdefu64, 0x0000567890abcdefu64])
            .into_truncated(112)
            .0;
        a.inplace_widening_shl(72);
        assert_eq!(
            a.chunks,
            vec![0, 0x34567890abcdef00u64, 0x00567890abcdef12u64]
        );
        assert_eq!(a.width, 184);
    }

    #[test]
    fn test_widening_umul_0() {
        let mut a = ApInt::from(vec![
            0xffffffffffffffffu64,
            0xffffffffffffffffu64,
            0xffffffffffffffffu64,
        ]);
        let b = ApInt::from(vec![
            0xffffffffffffffffu64,
            0xffffffffffffffffu64,
            0xffffffffffffffffu64,
        ]);

        a.inplace_widening_umul(&b);

        assert_eq!(
            a.chunks,
            vec![
                0x0000000000000001,
                0,
                0,
                0xfffffffffffffffe,
                0xffffffffffffffff,
                0xffffffffffffffff,
            ]
        );

        assert_eq!(a.width, 384);
    }

    #[test]
    fn test_widening_umul_1() {
        let mut a = ApInt::from(vec![
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
        ]);

        let b = ApInt::from(vec![
            0xfedcba9876543210u64,
            0xfedcba9876543210u64,
            0xfedcba9876543210u64,
        ]);

        a.inplace_widening_umul(&b);

        assert_eq!(
            a.chunks,
            vec![
                0x236d88fe55618cf0u64,
                0x58fab207783af122u64,
                0x8e87db109b145554u64,
                0x7d39f21d132a9fa6u64,
                0x47acc913f0513b74u64,
                0x121fa00acd77d742u64,
            ]
        );

        assert_eq!(a.width, 384);
    }

    #[test]
    fn test_widening_umul_2() {
        let mut a = ApInt::from(114514u32);
        let b = ApInt::from(1919810u32);

        a.inplace_widening_umul(&b);

        assert_eq!(a.width, 64);
        assert_eq!(a.chunks, [0x332fca5924u64])
    }

    #[test]
    fn test_carrying_umul_0() {
        let mut a = ApInt::from(0x12345678u32);
        let b = ApInt::from(0x87654321u32);
        let carry = a.inplace_carrying_umul(&b);
        assert_eq!(a.chunks, vec![0x70b88d78u64]);
        assert_eq!(carry.chunks, vec![0x9a0cd05u64]);
    }

    #[test]
    fn test_carrying_umul_1() {
        let mut a = ApInt::from(vec![
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
        ]);

        let b = ApInt::from(vec![
            0xfedcba9876543210u64,
            0xfedcba9876543210u64,
            0xfedcba9876543210u64,
        ]);

        let carry = a.inplace_carrying_umul(&b);

        assert_eq!(
            a.chunks,
            vec![
                0x236d88fe55618cf0u64,
                0x58fab207783af122u64,
                0x8e87db109b145554u64,
            ]
        );

        assert_eq!(
            carry.chunks,
            vec![
                0x7d39f21d132a9fa6u64,
                0x47acc913f0513b74u64,
                0x121fa00acd77d742u64,
            ]
        );
    }

    #[test]
    fn test_inplace_lshr_0() {
        let mut a = ApInt::from(vec![
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
        ]);

        let overflowed = a.inplace_lshr(64);

        assert_eq!(a.width, 192);
        assert_eq!(
            a.chunks,
            vec![0x1234567890abcdefu64, 0x1234567890abcdefu64, 0]
        );
        assert_eq!(overflowed.width, 64);
        assert_eq!(overflowed.chunks, vec![0x1234567890abcdefu64]);
    }

    #[test]
    fn test_inplace_lshr_1() {
        let mut a = ApInt::from(0x123u16).into_truncated(12).0;

        let overflowed = a.inplace_lshr(4);

        assert_eq!(a.width, 12);
        assert_eq!(a.chunks, vec![0x012]);
        assert_eq!(overflowed.width, 4);
        assert_eq!(overflowed.chunks, vec![0x3]);
    }

    #[test]
    fn test_inplace_lshr_2() {
        let mut a = ApInt::from(vec![0x1234567890abcdefu64, 0xfedcba9876543210u64]);

        let overflowed = a.inplace_lshr(68);

        assert_eq!(a.width, 128);
        assert_eq!(a.chunks, vec![0x0fedcba987654321u64, 0]);
        assert_eq!(overflowed.width, 68);
        assert_eq!(overflowed.chunks, vec![0x1234567890abcdefu64, 0]);
    }

    #[test]
    fn test_unsigned_div_rem_0() {
        let mut a = ApInt::from(5u32);
        let b = ApInt::from(2u32);

        let remainder = a.inplace_udiv(&b);

        assert_eq!(a.width, 32);
        assert_eq!(a.chunks, vec![0x2]);
        assert_eq!(remainder.width, 32);
        assert_eq!(remainder.chunks, vec![0x1]);
    }

    #[test]
    fn test_unsigned_div_rem_1() {
        let mut a = ApInt::from(vec![
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
        ]);

        let b = ApInt::from(vec![0xfedcba9876543210u64, 0xfedcba9876543210u64, 0]);
        // 0x124924923f07fffe, 0xea383d1d6c286420fc6c9395fcd4320f
        let remainder = a.inplace_udiv(&b);

        assert_eq!(a.width, 192);
        assert_eq!(a.chunks, vec![0x124924923f07fffeu64, 0, 0]);
        assert_eq!(remainder.width, 192);
        assert_eq!(
            remainder.chunks,
            vec![0xfc6c9395fcd4320fu64, 0xea383d1d6c286420u64, 0]
        );
    }

    fn test_abs(a: ApInt, b: ApInt) {
        let (result, _) = a.into_abs();
        assert_eq!(result, b);
    }

    #[test]
    fn test_abs_0() {
        test_abs(
            ApInt::from(0xfffffffu32).into_truncated(28).0,
            ApInt::from(1u32).into_truncated(28).0,
        );

        test_abs(ApInt::from(0xfffffffeu32), ApInt::from(2u32));

        test_abs(
            ApInt::from(vec![
                0xfffffffffffffff1u64,
                0xffffffffffffffffu64,
                0xffffffffffffffffu64,
            ]),
            ApInt::from(vec![0xfu64, 0, 0]),
        )
    }

    #[test]
    fn test_widenging_smul_0() {
        let mut a = ApInt::from(vec![0xfffffffffffffff0u64, 0xffffffffffffffffu64]);
        let b = ApInt::from(vec![0xffffffffffffffffu64, 0xffffffffffffffffu64]);

        a.inplace_widening_smul(&b);

        assert_eq!(a.width, 256);
        assert_eq!(a.chunks, vec![0x10, 0, 0, 0]);
    }

    #[test]
    fn test_carrying_smul_0() {
        let mut a = ApInt::from(0x114514u32);
        let b = ApInt::from(0xffffffffu32);

        let carry = a.inplace_carrying_smul(&b);

        assert_eq!(a.width, 32);
        assert_eq!(a.chunks, vec![0xffeebaecu64]);

        assert_eq!(carry.width, 32);
        assert_eq!(carry.chunks, vec![0xffffffffu64]);
    }

    #[test]
    fn test_signed_div_rem_0() {
        let mut a = ApInt::from(5u32);
        let b = ApInt::from(2u32);

        let remainder = a.inplace_sdiv(&b);

        assert_eq!(a.width, 32);
        assert_eq!(a.chunks, vec![0x2]);
        assert_eq!(remainder.width, 32);
        assert_eq!(remainder.chunks, vec![0x1]);
    }

    #[test]
    fn test_signed_div_rem_1() {
        let mut a = ApInt::from(0x7u32);
        let b = ApInt::from(0xfffffffcu32); // -4

        let remainder = a.inplace_sdiv(&b);

        assert_eq!(a.width, 32);
        assert_eq!(a.chunks, vec![0xffffffffu64]); // -1
        assert_eq!(remainder.width, 32);
        assert_eq!(remainder.chunks, vec![0x3]);
    }

    #[test]
    fn test_inplace_ashr_0() {
        let mut a = ApInt::from(vec![0x1234567890abcdefu64, 0xfedcba9876543210u64]);

        let overflowed = a.inplace_ashr(68);

        assert_eq!(a.width, 128);
        assert_eq!(a.chunks, vec![0xffedcba987654321u64, 0xffffffffffffffffu64]);
        assert_eq!(overflowed.width, 68);
        assert_eq!(overflowed.chunks, vec![0x1234567890abcdefu64, 0]);
    }

    #[test]
    fn test_inplace_ashr_1() {
        let mut a = ApInt::from(0x100u32).into_truncated(9).0;
        let overflowed = a.inplace_ashr(8);

        assert_eq!(a.width, 9);
        assert_eq!(a.chunks, vec![0x1ffu64]);
        assert_eq!(overflowed.width, 8);
        assert_eq!(overflowed.chunks, vec![0]);
    }
}
