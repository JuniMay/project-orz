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
    /// Create a new zero integer with given width.
    pub fn new(width: usize) -> Self {
        // ceil division to get the number of chunks
        let num_chunks = (width + ApIntChunk::BITS as usize - 1) / ApIntChunk::BITS as usize;
        Self {
            width,
            chunks: vec![0; num_chunks],
        }
    }

    /// Create a `0` with given width.
    pub fn zero(width: usize) -> Self { Self::new(width) }

    /// Check if the integer is zero.
    pub fn is_zero(&self) -> bool { self.chunks.iter().all(|c| *c == 0) }

    /// Create a `1` with given width.
    pub fn one(width: usize) -> Self {
        let mut apint = Self::zero(width);
        apint.chunks[0] = 1;
        apint
    }

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

    /// Sign extend the integer to the new width.
    pub fn signext(mut self, width: usize) -> Self {
        if width <= self.width {
            return self;
        }

        let sign = self.highest_bit();

        if sign {
            let ones = ApInt::all_ones(width - self.width).widening_shl(self.width);
            self = self.zeroext(width) | ones;
        } else {
            self = self.zeroext(width);
        }

        self
    }

    /// Zero extend the integer to the new width.
    pub fn zeroext(mut self, width: usize) -> Self {
        if width <= self.width {
            return self;
        }

        let num_chunks = (width + ApIntChunk::BITS as usize - 1) / ApIntChunk::BITS as usize;
        self.chunks.resize(num_chunks, 0);
        self.width = width;
        self.truncate_last_chunk();
        self
    }

    /// Truncate the integer into two parts, the first part has the given width
    ///
    /// This need to shift all the chunks to the left for the higher part and
    /// patch the lowest bits.
    ///
    /// This can be used to implement the shift right operation.
    ///
    /// # Panics
    ///
    /// Panics if the truncation width is not smaller than the integer width.
    pub fn into_truncated(self, width: usize) -> (Self, Self) {
        if width >= self.width {
            panic!("truncation width is not smaller than the integer width");
        }

        let mut orig = self;
        let mut low_part = ApInt::new(width);
        let mut high_part = ApInt::new(orig.width - width);

        low_part.chunks = orig.chunks.drain(0..low_part.chunks.len()).collect();

        for (i, chunk) in orig.chunks.drain(..).enumerate() {
            high_part.chunks[i] = chunk;
        }

        // the number of bits of the last chunk of low_part
        let num_low_bits = (width % ApIntChunk::BITS as usize) as u32;
        // if the number of bits is not a multiple of the chunk size
        if num_low_bits != 0 {
            // shift left by the number of bits to be patched to the lowest bits
            high_part.shl_by_bit(ApIntChunk::BITS - num_low_bits);
            // get the patch bits (the highest remaining bits of the last chunk of low_part)
            let patch_bits = low_part.chunks.last().unwrap() >> num_low_bits;
            // patch the lowest bits of the last chunk of low_part
            high_part.chunks[0] |= patch_bits;
            // clear the highest bits of the last chunk of low_part
            *low_part.chunks.last_mut().unwrap() &= low_part.last_chunk_mask();
        }

        (low_part, high_part)
    }

    /// Addition with carrying, returns the carry.
    ///
    /// The carry will occur if the sum exceeds the `width`.
    ///
    /// This operation is signless and under the complement representation.
    ///
    /// # Panics
    ///
    /// Panics if the width of the two integers are not the same.
    pub fn carrying_add(&self, rhs: &Self) -> (Self, bool) {
        if self.width != rhs.width {
            panic!("the width of the two integers are not the same")
        }

        let width = self.width;

        let mut result = ApInt::new(width);

        let mut carry = false;
        for ((a, b), r) in self
            .chunks
            .iter()
            .zip(rhs.chunks.iter())
            .zip(result.chunks.iter_mut())
        {
            let (sum, carry_0) = a.overflowing_add(*b);
            let (sum, carry_1) = sum.overflowing_add(u64::from(carry));
            *r = sum;
            carry = carry_0 || carry_1;
        }

        // check the last chunk mask
        let last_chunk_mask = result.last_chunk_mask();
        let last_chunk_unmasked = *result.chunks.last().unwrap();
        let last_chunk = result.chunks.last_mut().unwrap();

        *last_chunk &= last_chunk_mask;
        carry |= last_chunk_unmasked != *last_chunk;

        (result, carry)
    }

    /// Subtraction with carrying, returns the borrow.
    ///
    /// The borrow will occur if the difference is negative.
    ///
    /// This operation is signless and under the complement representation.
    ///
    /// # Panics
    ///
    /// Panics if the width of the two integers are not the same.
    pub fn borrowing_sub(&self, rhs: &Self) -> (Self, bool) {
        if self.width != rhs.width {
            panic!("the width of the two integers are not the same")
        }

        let width = self.width;

        let mut result = ApInt::new(width);

        let mut borrow = false;
        for ((a, b), r) in self
            .chunks
            .iter()
            .zip(rhs.chunks.iter())
            .zip(result.chunks.iter_mut())
        {
            let (diff, borrow_0) = a.overflowing_sub(*b);
            let (diff, borrow_1) = diff.overflowing_sub(u64::from(borrow));
            *r = diff;
            borrow = borrow_0 || borrow_1
        }

        // check the last chunk mask
        let last_chunk_mask = result.last_chunk_mask();
        let last_chunk_unmasked = *result.chunks.last().unwrap();
        let last_chunk = result.chunks.last_mut().unwrap();

        *last_chunk &= last_chunk_mask;
        borrow |= last_chunk_unmasked != *last_chunk;

        (result, borrow)
    }

    /// Shift the integer to the left by `shamt` chunks.
    ///
    /// This will not modify each chunk, buf only shift. The overflowed part
    /// will be discarded.
    ///
    /// This operation is signless.
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

    /// Shift the integer to the left by `shamt` bits and discard the
    /// overflowed.
    ///
    /// # Panics
    ///
    /// Panics if `shamt` is larger than the width of a chunk.
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

    /// Shift left and extend the width by `shamt` bits.
    ///
    /// This operation is signless.
    pub fn widening_shl(&self, shamt: usize) -> Self {
        let new_width = self.width + shamt;
        let mut result = self.clone().zeroext(new_width);

        let chunk_shamt = shamt / ApIntChunk::BITS as usize;
        let bit_shamt = shamt % ApIntChunk::BITS as usize;

        result.shl_by_chunk(chunk_shamt);
        result.shl_by_bit(bit_shamt as u32);

        result
    }

    /// Shift left and truncate the width.
    ///
    /// This operation is signless.
    pub fn carrying_shl(&self, shamt: usize) -> (Self, Self) {
        let old_width = self.width;
        self.widening_shl(shamt).into_truncated(old_width)
    }

    /// Get the highest bit of the integer.
    ///
    /// This can be used to check the sign of the integer.
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

    /// Get an all `1` mask
    pub fn all_ones(width: usize) -> Self {
        let mut apint = ApInt::new(width);
        for chunk in apint.chunks.iter_mut() {
            *chunk = ApIntChunk::MAX;
        }
        apint.truncate_last_chunk();
        apint
    }

    /// Get the absolute value as a complement representation and the sign.
    pub fn abs(&self) -> (Self, bool) {
        let width = self.width;
        if self.highest_bit() {
            (!self.clone() + ApInt::one(width), true)
        } else {
            (self.clone(), false)
        }
    }

    /// Multiply the integer by a chunk and extend the width by the chunk size.
    ///
    /// The full multiplication is currently nightly in Rust, so here just use
    /// the u128.
    ///
    /// This operation treat the integer as unsigned.
    pub fn widening_umul_chunk(&self, chunk: ApIntChunk) -> Self {
        let mut result = ApInt::new(self.width + ApIntChunk::BITS as usize);
        let mut carry = 0u128;

        for (a, r) in self.chunks.iter().zip(result.chunks.iter_mut()) {
            let product = u128::from(*a) * u128::from(chunk) + carry;
            *r = product as ApIntChunk;
            carry = product >> ApIntChunk::BITS;
        }
        *result.chunks.last_mut().unwrap() = carry as ApIntChunk;
        result
    }

    /// Shrink the integer to a minimum width.
    pub fn into_shrunk(self) -> Self {
        let mut apint = self;
        let mut width = apint.width;
        while width > 1 && apint.chunks.last().unwrap() == &0 {
            apint.chunks.pop();
            width -= ApIntChunk::BITS as usize;
        }
        // check last chunk's leading zeros to calculate the new width
        let num_chunks = apint.chunks.len();
        let last_chunk_width = ApIntChunk::BITS - apint.chunks.last().unwrap().leading_zeros();
        let new_width = (num_chunks - 1) * ApIntChunk::BITS as usize + last_chunk_width as usize;
        apint.width = new_width;
        apint
    }

    /// Multiply the integer by a chunk and truncate the width.
    ///
    /// This operation treat the integer as unsigned.
    pub fn carrying_umul_chunk(&self, chunk: ApIntChunk) -> (Self, Self) {
        let old_width = self.width;
        self.widening_umul_chunk(chunk).into_truncated(old_width)
    }

    /// Multiply the integer by another integer, produce a double width integer.
    pub fn widening_umul(&self, rhs: &Self) -> Self {
        if self.width != rhs.width {
            panic!("the width of the two integers are not the same")
        }

        if self.width * 2 <= ApIntChunk::BITS as usize {
            // the width is small enough to use the chunk multiplication
            let lhs = self.chunks[0];
            let rhs = rhs.chunks[0];
            // as the width is smaller than half of the chunk size, the product
            // will not overflow
            let product = lhs * rhs;
            return ApInt::from(product).zeroext(self.width * 2);
        }

        let width = self.width;

        let mut result = ApInt::new(width * 2);

        // the temporary result of the multiplication
        let mut tmp_result: Vec<u128> = vec![0; result.chunks.len()];

        for (i, chunk) in self.chunks.iter().enumerate() {
            let widened = rhs.widening_umul_chunk(*chunk);
            for (j, r) in widened.chunks.iter().enumerate() {
                tmp_result[i + j] += u128::from(*r);
            }
        }

        // propagate the carry
        let mut carry = 0u128;
        for (_i, r) in tmp_result.iter_mut().enumerate() {
            let sum = *r + carry;
            *r = sum;
            carry = sum >> ApIntChunk::BITS;
        }

        for (i, r) in tmp_result.iter().enumerate() {
            result.chunks[i] = *r as ApIntChunk;
        }

        result
    }

    pub fn widening_smul(&self, rhs: &Self) -> Self {
        let (lhs, lhs_sign) = self.abs();
        let (rhs, rhs_sign) = rhs.abs();

        let product = lhs.widening_umul(&rhs);
        let width = product.width;

        if lhs_sign ^ rhs_sign {
            !product + ApInt::one(width)
        } else {
            product
        }
    }

    /// Multiply the integer by another integer and truncate the width.
    ///
    /// This operation treat the integer as unsigned.
    pub fn carrying_umul(&self, rhs: &Self) -> (Self, Self) {
        let old_width = self.width;
        self.widening_umul(rhs).into_truncated(old_width)
    }

    /// Multiply the integer by another integer and truncate the width.
    ///
    /// This operation treat the integer as signed.
    pub fn carrying_smul(&self, rhs: &Self) -> (Self, Self) {
        let old_width = self.width;
        self.widening_smul(rhs).into_truncated(old_width)
    }

    /// Shift the integer to the right by `shamt` bits logically.
    ///
    /// The overflowed part will be returned.
    pub fn overflowing_lshr(&self, shamt: usize) -> (Self, Self) {
        let old_width = self.width;
        let (overflowed, result) = self.clone().into_truncated(shamt);
        (result.zeroext(old_width), overflowed)
    }

    /// Shift the integer to the right by `shamt` bits arithmetically.
    ///
    /// The sign bit will be extended to the higher bits.
    pub fn overflowing_ashr(&self, shamt: usize) -> (Self, Self) {
        let old_width = self.width;
        let (overflowed, result) = self.clone().into_truncated(shamt);
        let result = result.signext(old_width);
        debug_assert!(result.width == old_width);
        (result, overflowed)
    }

    /// Division with remainder.
    ///
    /// This operation treat the integers as unsigned.
    pub fn unsigned_div_rem(&self, other: &Self) -> (Self, Self) {
        if self.width != other.width {
            panic!("the width of the two integers are not the same")
        }

        let width = self.width;

        let divisor = other.clone();

        let mut remainder = ApInt::new(width);
        let mut quotient = self.clone();

        for _ in 0..width {
            let set_bit = if remainder >= divisor {
                remainder = remainder.borrowing_sub(&divisor).0;
                true
            } else {
                false
            };

            let (shifted_quotient, carry) = quotient.carrying_shl(1);
            quotient = shifted_quotient;
            quotient.chunks[0] |= u64::from(set_bit);

            let shifted_remainder = remainder.carrying_shl(1).0;
            remainder = shifted_remainder;
            remainder.chunks[0] |= u64::from(!carry.is_zero());
        }

        let set_bit = if remainder >= divisor {
            remainder = remainder.borrowing_sub(&divisor).0;
            true
        } else {
            false
        };

        let (shifted_quotient, _carry) = quotient.carrying_shl(1);
        quotient = shifted_quotient;
        quotient.chunks[0] |= u64::from(set_bit);

        (quotient, remainder)
    }

    /// Division with remainder.
    ///
    /// This operation treat the integers as signed.
    pub fn signed_div_rem(&self, other: &Self) -> (Self, Self) {
        let (lhs, lhs_sign) = self.abs();
        let (rhs, rhs_sign) = other.abs();

        let (quotient, remainder) = lhs.unsigned_div_rem(&rhs);

        let remainder_sign = lhs_sign;
        let quotient_sign = lhs_sign ^ rhs_sign;
        let remainder_width = remainder.width;
        let quotient_width = quotient.width;

        let remainder = if remainder_sign {
            !remainder + ApInt::one(remainder_width)
        } else {
            remainder
        };

        let quotient = if quotient_sign {
            !quotient + ApInt::one(quotient_width)
        } else {
            quotient
        };

        (quotient, remainder)
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
        let mut apint = ApInt::new(8);
        apint.chunks[0] = value as ApIntChunk;
        apint
    }
}

impl From<i8> for ApInt {
    fn from(value: i8) -> Self {
        let abs = value.unsigned_abs();
        let apint = ApInt::from(abs);
        -apint
    }
}

impl From<u16> for ApInt {
    fn from(value: u16) -> Self {
        let mut apint = ApInt::new(16);
        apint.chunks[0] = value as ApIntChunk;
        apint
    }
}

impl From<i16> for ApInt {
    fn from(value: i16) -> Self {
        let abs = value.unsigned_abs();
        let apint = ApInt::from(abs);
        -apint
    }
}

impl From<u32> for ApInt {
    fn from(value: u32) -> Self {
        let mut apint = ApInt::new(32);
        apint.chunks[0] = value as ApIntChunk;
        apint
    }
}

impl From<i32> for ApInt {
    fn from(value: i32) -> Self {
        let abs = value.unsigned_abs();
        let apint = ApInt::from(abs);
        -apint
    }
}

impl From<u64> for ApInt {
    fn from(value: u64) -> Self {
        let mut apint = ApInt::new(64);
        apint.chunks[0] = value as ApIntChunk;
        apint
    }
}

impl From<i64> for ApInt {
    fn from(value: i64) -> Self {
        let abs = value.unsigned_abs();
        let apint = ApInt::from(abs);
        -apint
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

impl std::ops::Add for ApInt {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output { self.carrying_add(&rhs).0 }
}

impl std::ops::Sub for ApInt {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output { self.borrowing_sub(&rhs).0 }
}

impl std::ops::BitAnd for ApInt {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        if self.width != rhs.width {
            panic!("the width of the two integers are not the same")
        }

        let mut result = ApInt::new(self.width);
        for ((a, b), r) in self
            .chunks
            .iter()
            .zip(rhs.chunks.iter())
            .zip(result.chunks.iter_mut())
        {
            *r = *a & *b;
        }
        result
    }
}

impl std::ops::BitOr for ApInt {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        if self.width != rhs.width {
            panic!("the width of the two integers are not the same")
        }

        let mut result = ApInt::new(self.width);
        for ((a, b), r) in self
            .chunks
            .iter()
            .zip(rhs.chunks.iter())
            .zip(result.chunks.iter_mut())
        {
            *r = *a | *b;
        }
        result
    }
}

impl std::ops::BitXor for ApInt {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        if self.width != rhs.width {
            panic!("the width of the two integers are not the same")
        }

        let mut result = ApInt::new(self.width);
        for ((a, b), r) in self
            .chunks
            .iter()
            .zip(rhs.chunks.iter())
            .zip(result.chunks.iter_mut())
        {
            *r = *a ^ *b;
        }
        result
    }
}

impl std::ops::Not for ApInt {
    type Output = Self;

    fn not(self) -> Self::Output {
        let mut result = ApInt::new(self.width);
        for (r, a) in result.chunks.iter_mut().zip(self.chunks.iter()) {
            *r = !*a;
        }
        result.truncate_last_chunk();
        result
    }
}

impl std::ops::Neg for ApInt {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let width = self.width;
        !self + ApInt::one(width)
    }
}

impl std::ops::Shl<usize> for ApInt {
    type Output = Self;

    fn shl(self, shamt: usize) -> Self::Output { self.carrying_shl(shamt).0 }
}

impl std::ops::Shr<usize> for ApInt {
    type Output = Self;

    fn shr(self, shamt: usize) -> Self::Output {
        let (result, _) = self.overflowing_lshr(shamt);
        result
    }
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
            apint = apint.widening_umul_chunk(radix as ApIntChunk);
            let digit = ApInt::from(digit);

            if apint.width > digit.width {
                apint = digit.zeroext(apint.width) + apint;
            } else {
                apint = apint.zeroext(digit.width) + digit;
            }

            apint = apint.into_shrunk();
        }

        if let Some(bits) = bits {
            if bits < apint.width {
                return Err(ApIntParseError::OutOfRange(bits, apint.width));
            } else {
                apint = apint.zeroext(bits);
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
        let value = match token.kind {
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
        Ok(if neg { -value } else { value })
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
            let (quotient, remainder) = tmp.unsigned_div_rem(&ApInt::from(10u32));
            s.push_str(&remainder.chunks[0].to_string());
            tmp = quotient;
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
        let expected = ApInt::from(1234567890u32).zeroext(34);
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
        let a = ApInt::from(123u32).zeroext(128);
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
        let a = a.signext(64);
        assert_eq!(a.chunks, vec![0xfffffffff2345678u64]);
    }

    #[test]
    fn test_carrying_add() {
        let a = ApInt::from(0x12345678u32);
        let b = ApInt::from(0x87654321u32);
        let (result, carry) = a.carrying_add(&b);
        assert_eq!(result.chunks, vec![0x99999999]);
        assert!(!carry);
    }

    #[test]
    fn test_carrying_add_carry_0() {
        let a = ApInt::from(0x12345678u32);
        let b = ApInt::from(0xf7654321u32);
        let (result, carry) = a.carrying_add(&b);
        assert_eq!(result.chunks, vec![0x09999999]);
        assert!(carry);
    }

    #[test]
    fn test_carrying_add_carry_1() {
        let a = ApInt::from(vec![0x123456781234u64, 0x56784321u64])
            .into_truncated(96)
            .0;
        let b = ApInt::from(vec![0xf76543214321u64, 0xf3211234u64])
            .into_truncated(96)
            .0;

        let (result, carry) = a.carrying_add(&b);

        assert_eq!(result.chunks, vec![0x1099999995555u64, 0x49995555u64]);
        assert!(carry);
    }

    #[test]
    fn test_carrying_add_carry_2() {
        let a = ApInt::from(vec![0xffffffff88888888u64, 0xffffffffu64])
            .into_truncated(96)
            .0;
        let b = ApInt::from(vec![0xffffffff88888888u64, 0xffffffffu64])
            .into_truncated(96)
            .0;

        let (result, carry) = a.carrying_add(&b);

        assert_eq!(result.chunks, vec![0xffffffff11111110u64, 0xffffffffu64]);
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
    fn test_borrowing_sub_borrow_0() {
        let a = ApInt::from(0x12345678u32);
        let b = ApInt::from(0x87654321u32);
        let (result, borrow) = a.borrowing_sub(&b);
        assert_eq!(result.chunks, vec![0x8acf1357u64]);
        assert!(borrow);
    }

    #[test]
    fn test_borrowing_sub_0() {
        let a = ApInt::from(0x12345678u32);
        let b = ApInt::from(0x87654321u32);
        let (result, borrow) = b.borrowing_sub(&a);
        assert_eq!(result.chunks, vec![0x7530eca9u64]);
        assert!(!borrow);
    }

    #[test]
    fn test_borrowing_sub_2() {
        let a = ApInt::from(0x12345678u32);
        let b = ApInt::from(0x12345678u32);
        let (result, borrow) = a.borrowing_sub(&b);
        assert_eq!(result.chunks, vec![0]);
        assert!(!borrow);
    }

    #[test]
    fn test_borrowing_sub_1() {
        let a = ApInt::from(vec![0x1122334455667788u64, 0x9900aabbccddeeffu64]);
        let b = ApInt::from(vec![0x2233445566778899u64, 0x00aabbccddeeff22u64]);

        let (result, borrow) = a.borrowing_sub(&b);

        assert_eq!(
            result.chunks,
            vec![0xeeeeeeeeeeeeeeefu64, 0x9855eeeeeeeeefdcu64]
        );
        assert!(!borrow);
    }

    #[test]
    fn test_borrowing_sub_borrow_1() {
        let a = ApInt::from(vec![0x1122334455667788u64, 0x9900aabbccddeeffu64]);
        let b = ApInt::from(vec![0x2233445566778899u64, 0x00aabbccddeeff22u64]);

        let (result, borrow) = b.borrowing_sub(&a);

        assert!(borrow);
        assert_eq!(
            result.chunks,
            vec![0x1111111111111111u64, 0x67aa111111111023u64]
        );
    }

    #[test]
    fn test_widening_umul_chunk_0() {
        let a = ApInt::from(vec![0x1234567890abcdefu64, 0x1234u64])
            .into_truncated(80)
            .0;
        let b = 0x1234u64;
        let result = a.widening_umul_chunk(b);
        assert_eq!(result.width, 144);
        assert_eq!(result.chunks, vec![0x60b60aa97760a28cu64, 0x14b5bdbu64, 0]);
    }

    #[test]
    fn test_widening_umul_chunk_1() {
        let a = ApInt::from(123u32);
        let b = 1234u64;

        let result = a.widening_umul_chunk(b);

        assert_eq!(result.width, 96);
        assert_eq!(result.chunks, vec![0x250e6, 0]);
    }

    #[test]
    fn test_carrying_umul_chunk_0() {
        let a = ApInt::from(123u32).into_truncated(8).0;
        let b = 1234u64;

        let (result, carry) = a.carrying_umul_chunk(b);

        assert_eq!(result.chunks, vec![0xe6]);
        assert_eq!(result.width, 8);
        assert_eq!(carry.chunks, vec![0x250]);
        assert_eq!(carry.width, 64);
    }

    #[test]
    fn test_carrying_umul_chunk_1() {
        let a = ApInt::from(vec![0x1234567890abcdefu64, 0x1234u64])
            .into_truncated(80)
            .0;
        let b = 0x1234u64;

        let (result, carry) = a.carrying_umul_chunk(b);

        assert_eq!(result.chunks, vec![0x60b60aa97760a28cu64, 0x5bdbu64]);
        assert_eq!(result.width, 80);
        assert_eq!(carry.chunks, vec![0x14b]);
        assert_eq!(carry.width, 64);
    }

    #[test]
    fn test_carrying_shl_0() {
        let a = ApInt::from(0x12345678u32);
        let (result, carry) = a.carrying_shl(4);
        assert_eq!(result.chunks, vec![0x23456780u64]);
        assert_eq!(result.width, 32);
        assert_eq!(carry.chunks, vec![1]);
        assert_eq!(carry.width, 4);
    }

    #[test]
    fn test_carrying_shl_1() {
        let a = ApInt::from(vec![0x1234567890abcdefu64, 0x0000567890abcdefu64])
            .into_truncated(112)
            .0;
        let (result, carry) = a.carrying_shl(72);
        assert_eq!(result.chunks, vec![0, 0x00007890abcdef00u64]);
        assert_eq!(result.width, 112);
        // 0x56_7890_abcd_ef12_3456
        assert_eq!(carry.chunks, vec![0x7890abcdef123456u64, 0x56u64]);
        assert_eq!(carry.width, 72);
    }

    #[test]
    fn test_widening_shl_0() {
        let a = ApInt::from(0x12345678u32);
        let result = a.widening_shl(4);
        assert_eq!(result.chunks, vec![0x123456780u64]);
        assert_eq!(result.width, 36);
    }

    #[test]
    fn test_widening_shl_1() {
        let a = ApInt::from(vec![0x1234567890abcdefu64, 0x0000567890abcdefu64])
            .into_truncated(112)
            .0;
        let result = a.widening_shl(72);
        assert_eq!(
            result.chunks,
            vec![0, 0x34567890abcdef00u64, 0x00567890abcdef12u64]
        );
        assert_eq!(result.width, 184);
    }

    #[test]
    fn test_widening_umul_0() {
        let a = ApInt::from(vec![
            0xffffffffffffffffu64,
            0xffffffffffffffffu64,
            0xffffffffffffffffu64,
        ]);
        let b = ApInt::from(vec![
            0xffffffffffffffffu64,
            0xffffffffffffffffu64,
            0xffffffffffffffffu64,
        ]);

        let result = a.widening_umul(&b);

        assert_eq!(
            result.chunks,
            vec![
                0x0000000000000001,
                0,
                0,
                0xfffffffffffffffe,
                0xffffffffffffffff,
                0xffffffffffffffff,
            ]
        );

        assert_eq!(result.width, 384);
    }

    #[test]
    fn test_widening_umul_1() {
        let a = ApInt::from(vec![
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
        ]);

        let b = ApInt::from(vec![
            0xfedcba9876543210u64,
            0xfedcba9876543210u64,
            0xfedcba9876543210u64,
        ]);

        let result = a.widening_umul(&b);

        assert_eq!(
            result.chunks,
            vec![
                0x236d88fe55618cf0u64,
                0x58fab207783af122u64,
                0x8e87db109b145554u64,
                0x7d39f21d132a9fa6u64,
                0x47acc913f0513b74u64,
                0x121fa00acd77d742u64,
            ]
        );

        assert_eq!(result.width, 384);
    }

    #[test]
    fn test_widening_umul_2() {
        let a = ApInt::from(114514u32);
        let b = ApInt::from(1919810u32);

        let result = a.widening_umul(&b);

        assert_eq!(result.width, 64);
        assert_eq!(result.chunks, [0x332fca5924u64])
    }

    #[test]
    fn test_carrying_umul() {
        let a = ApInt::from(0x12345678u32);
        let b = ApInt::from(0x87654321u32);
        let (lhs, rhs) = a.carrying_umul(&b);
        assert_eq!(lhs.chunks, vec![0x70b88d78u64]);
        assert_eq!(rhs.chunks, vec![0x9a0cd05u64]);
    }

    #[test]
    fn test_carrying_umul_1() {
        let a = ApInt::from(vec![
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
        ]);

        let b = ApInt::from(vec![
            0xfedcba9876543210u64,
            0xfedcba9876543210u64,
            0xfedcba9876543210u64,
        ]);

        let (result, carry) = a.carrying_umul(&b);

        assert_eq!(
            result.chunks,
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
    fn test_overflowing_lshr_0() {
        let a = ApInt::from(vec![
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
        ]);

        let (result, overflowed) = a.overflowing_lshr(64);

        assert_eq!(result.width, 192);
        assert_eq!(
            result.chunks,
            vec![0x1234567890abcdefu64, 0x1234567890abcdefu64, 0]
        );
        assert_eq!(overflowed.width, 64);
        assert_eq!(overflowed.chunks, vec![0x1234567890abcdefu64]);
    }

    #[test]
    fn test_overflowing_lshr_1() {
        let a = ApInt::from(0x123u16).into_truncated(12).0;

        let (result, overflowed) = a.overflowing_lshr(4);

        assert_eq!(result.width, 12);
        assert_eq!(result.chunks, vec![0x012]);
        assert_eq!(overflowed.width, 4);
        assert_eq!(overflowed.chunks, vec![0x3]);
    }

    #[test]
    fn test_overflowing_lshr_2() {
        let a = ApInt::from(vec![0x1234567890abcdefu64, 0xfedcba9876543210u64]);

        let (result, overflowed) = a.overflowing_lshr(68);

        assert_eq!(result.width, 128);
        assert_eq!(result.chunks, vec![0x0fedcba987654321u64, 0]);
        assert_eq!(overflowed.width, 68);
        assert_eq!(overflowed.chunks, vec![0x1234567890abcdefu64, 0]);
    }

    #[test]
    fn test_unsigned_div_rem_0() {
        let a = ApInt::from(5u32);
        let b = ApInt::from(2u32);

        let (quotient, remainder) = a.unsigned_div_rem(&b);

        assert_eq!(quotient.width, 32);
        assert_eq!(quotient.chunks, vec![0x2]);
        assert_eq!(remainder.width, 32);
        assert_eq!(remainder.chunks, vec![0x1]);
    }

    #[test]
    fn test_unsigned_div_rem_1() {
        let a = ApInt::from(vec![
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
        ]);

        let b = ApInt::from(vec![0xfedcba9876543210u64, 0xfedcba9876543210u64, 0]);
        // 0x124924923f07fffe, 0xea383d1d6c286420fc6c9395fcd4320f
        let (quotient, remainder) = a.unsigned_div_rem(&b);

        assert_eq!(quotient.width, 192);
        assert_eq!(quotient.chunks, vec![0x124924923f07fffeu64, 0, 0]);
        assert_eq!(remainder.width, 192);
        assert_eq!(
            remainder.chunks,
            vec![0xfc6c9395fcd4320fu64, 0xea383d1d6c286420u64, 0]
        );
    }

    fn test_abs(a: ApInt, b: ApInt) {
        let (result, _) = a.abs();
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
        let a = ApInt::from(vec![0xfffffffffffffff0u64, 0xffffffffffffffffu64]);
        let b = ApInt::from(vec![0xffffffffffffffffu64, 0xffffffffffffffffu64]);

        let result = a.widening_smul(&b);

        assert_eq!(result.width, 256);
        assert_eq!(result.chunks, vec![0x10, 0, 0, 0]);
    }

    #[test]
    fn test_carrying_smul_0() {
        let a = ApInt::from(0x114514u32);
        let b = ApInt::from(0xffffffffu32);

        let (result, carry) = a.carrying_smul(&b);

        assert_eq!(result.width, 32);
        assert_eq!(result.chunks, vec![0xffeebaecu64]);

        assert_eq!(carry.width, 32);
        assert_eq!(carry.chunks, vec![0xffffffffu64]);
    }

    #[test]
    fn test_signed_div_rem_0() {
        let a = ApInt::from(5u32);
        let b = ApInt::from(2u32);

        let (quotient, remainder) = a.signed_div_rem(&b);

        assert_eq!(quotient.width, 32);
        assert_eq!(quotient.chunks, vec![0x2]);
        assert_eq!(remainder.width, 32);
        assert_eq!(remainder.chunks, vec![0x1]);
    }

    #[test]
    fn test_signed_div_rem_1() {
        let a = ApInt::from(0x7u32);
        let b = ApInt::from(0xfffffffcu32); // -4

        let (quotient, remainder) = a.signed_div_rem(&b);

        assert_eq!(quotient.width, 32);
        assert_eq!(quotient.chunks, vec![0xffffffffu64]); // -1
        assert_eq!(remainder.width, 32);
        assert_eq!(remainder.chunks, vec![0x3]);
    }

    #[test]
    fn test_overflowing_ashr_0() {
        let a = ApInt::from(vec![0x1234567890abcdefu64, 0xfedcba9876543210u64]);

        let (result, overflowed) = a.overflowing_ashr(68);

        assert_eq!(result.width, 128);
        assert_eq!(
            result.chunks,
            vec![0xffedcba987654321u64, 0xffffffffffffffffu64]
        );
        assert_eq!(overflowed.width, 68);
        assert_eq!(overflowed.chunks, vec![0x1234567890abcdefu64, 0]);
    }

    #[test]
    fn test_oveflowing_ashr_1() {
        let a = ApInt::from(0x100u32).into_truncated(9).0;
        let (result, overflowed) = a.overflowing_ashr(8);

        assert_eq!(result.width, 9);
        assert_eq!(result.chunks, vec![0x1ffu64]);
        assert_eq!(overflowed.width, 8);
        assert_eq!(overflowed.chunks, vec![0]);
    }
}
