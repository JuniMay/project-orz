use core::fmt;
use std::cmp::Ordering;

pub type ApUIntChunk = u64;

/// An arbitrary precision integer.
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct ApUInt {
    /// The width of the integer in bits.
    width: usize,
    /// The chunks of the integer.
    chunks: Vec<ApUIntChunk>,
}

impl fmt::Debug for ApUInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // hexadecimal
        write!(f, "ApUInt ({} bits): ", self.width)?;
        write!(f, "0x")?;
        for chunk in self.chunks.iter().rev() {
            write!(f, "{:016x}", chunk)?;
        }
        Ok(())
    }
}

impl ApUInt {
    pub fn new(width: usize) -> Self {
        // ceil division to get the number of chunks
        let num_chunks = (width + ApUIntChunk::BITS as usize - 1) / ApUIntChunk::BITS as usize;
        Self {
            width,
            chunks: vec![0; num_chunks],
        }
    }

    #[inline(always)]
    fn last_chunk_mask(&self) -> ApUIntChunk {
        let bits = self.width % ApUIntChunk::BITS as usize;
        if bits == 0 {
            // this chunk is full, the width is a multiple of the chunk size
            ApUIntChunk::MAX
        } else {
            // this chunk is not full, mask the bits
            (1 << bits) - 1
        }
    }

    pub fn into_resized(self, width: usize) -> Self {
        let mut apint = self;
        apint.width = width;
        let num_chunks = (width + ApUIntChunk::BITS as usize - 1) / ApUIntChunk::BITS as usize;
        apint.chunks.resize(num_chunks, 0);
        apint.chunks[num_chunks - 1] &= apint.last_chunk_mask();
        apint
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
        let mut low_part = ApUInt::new(width);
        let mut high_part = ApUInt::new(orig.width - width);

        low_part.chunks = orig.chunks.drain(0..low_part.chunks.len()).collect();

        for (i, chunk) in orig.chunks.drain(..).enumerate() {
            high_part.chunks[i] = chunk;
        }

        // the number of bits of the last chunk of low_part
        let num_low_bits = (width % ApUIntChunk::BITS as usize) as u32;
        // if the number of bits is not a multiple of the chunk size
        if num_low_bits != 0 {
            // shift left by the number of bits to be patched to the lowest bits
            high_part.shl_by_bit(ApUIntChunk::BITS - num_low_bits);
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
    pub fn carrying_add(self, rhs: &Self) -> (Self, bool) {
        if self.width != rhs.width {
            panic!("the width of the two integers are not the same")
        }

        let width = self.width;

        let mut result = ApUInt::new(width);

        let lhs = self;

        let mut carry = false;
        for ((a, b), r) in lhs
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
    pub fn borrowing_sub(self, rhs: &Self) -> (Self, bool) {
        if self.width != rhs.width {
            panic!("the width of the two integers are not the same")
        }

        let width = self.width;
        let lhs = self;

        let mut result = ApUInt::new(width);

        let mut borrow = false;
        for ((a, b), r) in lhs
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
        if shamt >= ApUIntChunk::BITS {
            panic!("shamt is larger than the width of a chunk");
        }

        if shamt == 0 {
            return;
        }

        // the number of bits shifted within a chunk
        let num_low_bits = ApUIntChunk::BITS - shamt;
        // the overflowed part of the last chunk
        let mut patch_bits = 0u64;

        for chunk in self.chunks.iter_mut() {
            let new_patch_bits = *chunk >> num_low_bits;
            *chunk = (*chunk << shamt) | patch_bits;
            patch_bits = new_patch_bits;
        }

        // check the last chunk mask
        *self.chunks.last_mut().unwrap() &= self.last_chunk_mask();
    }

    /// Shift left and extend the width by `shamt` bits.
    pub fn widening_shl(self, shamt: usize) -> Self {
        let new_width = self.width + shamt;
        let mut orig = self.into_resized(new_width);

        let chunk_shamt = shamt / ApUIntChunk::BITS as usize;
        let bit_shamt = shamt % ApUIntChunk::BITS as usize;

        orig.shl_by_chunk(chunk_shamt);
        orig.shl_by_bit(bit_shamt as u32);

        orig
    }

    /// Shift left and truncate the width.
    pub fn carrying_shl(self, shamt: usize) -> (Self, Self) {
        let old_width = self.width;
        self.widening_shl(shamt).into_truncated(old_width)
    }

    pub fn is_zero(&self) -> bool { self.chunks.iter().all(|c| *c == 0) }

    /// Multiply the integer by a chunk and extend the width by the chunk size.
    ///
    /// The full multiplication is currently nightly in Rust, so here just use
    /// the u128.
    pub fn widening_mul_chunk(self, chunk: ApUIntChunk) -> Self {
        let mut orig = self;
        let mut result = ApUInt::new(orig.width + ApUIntChunk::BITS as usize);
        let mut carry = 0u128;

        for (a, r) in orig.chunks.drain(..).zip(result.chunks.iter_mut()) {
            let product = u128::from(a) * u128::from(chunk) + carry;
            *r = product as ApUIntChunk;
            carry = product >> ApUIntChunk::BITS;
        }
        *result.chunks.last_mut().unwrap() = carry as ApUIntChunk;
        result
    }

    pub fn carrying_mul_chunk(self, chunk: ApUIntChunk) -> (Self, Self) {
        let old_width = self.width;
        self.widening_mul_chunk(chunk).into_truncated(old_width)
    }

    /// Multiply the integer by another integer, produce a double width integer.
    pub fn widening_mul(self, rhs: &Self) -> Self {
        if self.width != rhs.width {
            panic!("the width of the two integers are not the same")
        }

        if self.width * 2 <= ApUIntChunk::BITS as usize {
            // the width is small enough to use the chunk multiplication
            let lhs = self.chunks[0];
            let rhs = rhs.chunks[0];
            // as the width is smaller than half of the chunk size, the product
            // will not overflow
            let product = lhs * rhs;
            return ApUInt::from(product).into_resized(self.width * 2);
        }

        let mut lhs = self;

        let width = lhs.width;

        let mut result = ApUInt::new(width * 2);

        // the temporary result of the multiplication
        let mut tmp_result: Vec<u128> = vec![0; result.chunks.len()];

        for (i, chunk) in lhs.chunks.drain(..).enumerate() {
            let widened = rhs.clone().widening_mul_chunk(chunk);
            for (j, r) in widened.chunks.iter().enumerate() {
                tmp_result[i + j] += u128::from(*r);
            }
        }

        // propagate the carry
        let mut carry = 0u128;
        for (_i, r) in tmp_result.iter_mut().enumerate() {
            let sum = *r + carry;
            *r = sum;
            carry = sum >> ApUIntChunk::BITS;
        }

        for (i, r) in tmp_result.iter().enumerate() {
            result.chunks[i] = *r as ApUIntChunk;
        }

        result
    }

    pub fn carrying_mul(self, rhs: &Self) -> (Self, Self) {
        let old_width = self.width;
        self.widening_mul(rhs).into_truncated(old_width)
    }

    pub fn overflowing_shr(self, shamt: usize) -> (Self, Self) {
        let old_width = self.width;
        let (overflowed, result) = self.into_truncated(shamt);
        (result.into_resized(old_width), overflowed)
    }

    /// Division with remainder.
    pub fn div_rem(self, other: Self) -> (Self, Self) {
        if self.width != other.width {
            panic!("the width of the two integers are not the same")
        }

        let width = self.width;

        let divisor = other;

        let mut remainder = ApUInt::new(width);
        let mut quotient = self;

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
}

impl From<Vec<ApUIntChunk>> for ApUInt {
    fn from(chunks: Vec<ApUIntChunk>) -> Self {
        let width = chunks.len() * ApUIntChunk::BITS as usize;
        Self { width, chunks }
    }
}

impl From<u8> for ApUInt {
    fn from(value: u8) -> Self {
        let mut apint = ApUInt::new(8);
        apint.chunks[0] = value as ApUIntChunk;
        apint
    }
}

impl From<u16> for ApUInt {
    fn from(value: u16) -> Self {
        let mut apint = ApUInt::new(16);
        apint.chunks[0] = value as ApUIntChunk;
        apint
    }
}

impl From<u32> for ApUInt {
    fn from(value: u32) -> Self {
        let mut apint = ApUInt::new(32);
        apint.chunks[0] = value as ApUIntChunk;
        apint
    }
}

impl From<u64> for ApUInt {
    fn from(value: u64) -> Self {
        let mut apint = ApUInt::new(64);
        apint.chunks[0] = value as ApUIntChunk;
        apint
    }
}

impl PartialOrd for ApUInt {
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

impl Ord for ApUInt {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering { self.partial_cmp(other).unwrap() }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ord_0() {
        let a = ApUInt::from(123u32).into_resized(128);
        let b = ApUInt::from(256u32);
        assert!(a < b);
    }

    #[test]
    fn test_ord_1() {
        let a = ApUInt::from(vec![0, 0x1]);
        let b = ApUInt::from(256u32);
        assert!(a > b);
    }

    #[test]
    fn test_resize() {
        let apint = ApUInt::from(0x12345678u32);
        let a = apint.clone().into_resized(16);
        assert_eq!(a.chunks, vec![0x5678]);
        let b = apint.into_resized(8);
        assert_eq!(b.chunks, vec![0x78]);
    }

    #[test]
    fn test_carrying_add() {
        let a = ApUInt::from(0x12345678u32);
        let b = ApUInt::from(0x87654321u32);
        let (result, carry) = a.carrying_add(&b);
        assert_eq!(result.chunks, vec![0x99999999]);
        assert!(!carry);
    }

    #[test]
    fn test_carrying_add_carry_0() {
        let a = ApUInt::from(0x12345678u32);
        let b = ApUInt::from(0xf7654321u32);
        let (result, carry) = a.carrying_add(&b);
        assert_eq!(result.chunks, vec![0x09999999]);
        assert!(carry);
    }

    #[test]
    fn test_carrying_add_carry_1() {
        let a = ApUInt::from(vec![0x123456781234u64, 0x56784321u64]).into_resized(96);
        let b = ApUInt::from(vec![0xf76543214321u64, 0xf3211234u64]).into_resized(96);

        let (result, carry) = a.carrying_add(&b);

        assert_eq!(result.chunks, vec![0x1099999995555u64, 0x49995555u64]);
        assert!(carry);
    }

    #[test]
    fn test_carrying_add_carry_2() {
        let a = ApUInt::from(vec![0xffffffff88888888u64, 0xffffffffu64]).into_resized(96);
        let b = ApUInt::from(vec![0xffffffff88888888u64, 0xffffffffu64]).into_resized(96);

        let (result, carry) = a.carrying_add(&b);

        assert_eq!(result.chunks, vec![0xffffffff11111110u64, 0xffffffffu64]);
        assert!(carry);
    }

    #[test]
    fn test_truncate_0() {
        let a = ApUInt::from(vec![
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
        let a = ApUInt::from(vec![
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
        let a = ApUInt::from(vec![
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
        let a = ApUInt::from(vec![
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
        let a = ApUInt::from(vec![
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
        let a = ApUInt::from(0x12345678u32);
        let b = ApUInt::from(0x87654321u32);
        let (result, borrow) = a.borrowing_sub(&b);
        assert_eq!(result.chunks, vec![0x8acf1357u64]);
        assert!(borrow);
    }

    #[test]
    fn test_borrowing_sub_0() {
        let a = ApUInt::from(0x12345678u32);
        let b = ApUInt::from(0x87654321u32);
        let (result, borrow) = b.borrowing_sub(&a);
        assert_eq!(result.chunks, vec![0x7530eca9u64]);
        assert!(!borrow);
    }

    #[test]
    fn test_borrowing_sub_2() {
        let a = ApUInt::from(0x12345678u32);
        let b = ApUInt::from(0x12345678u32);
        let (result, borrow) = a.borrowing_sub(&b);
        assert_eq!(result.chunks, vec![0]);
        assert!(!borrow);
    }

    #[test]
    fn test_borrowing_sub_1() {
        let a = ApUInt::from(vec![0x1122334455667788u64, 0x9900aabbccddeeffu64]);
        let b = ApUInt::from(vec![0x2233445566778899u64, 0x00aabbccddeeff22u64]);

        let (result, borrow) = a.borrowing_sub(&b);

        assert_eq!(
            result.chunks,
            vec![0xeeeeeeeeeeeeeeefu64, 0x9855eeeeeeeeefdcu64]
        );
        assert!(!borrow);
    }

    #[test]
    fn test_borrowing_sub_borrow_1() {
        let a = ApUInt::from(vec![0x1122334455667788u64, 0x9900aabbccddeeffu64]);
        let b = ApUInt::from(vec![0x2233445566778899u64, 0x00aabbccddeeff22u64]);

        let (result, borrow) = b.borrowing_sub(&a);

        assert!(borrow);
        assert_eq!(
            result.chunks,
            vec![0x1111111111111111u64, 0x67aa111111111023u64]
        );
    }

    #[test]
    fn test_widening_mul_chunk_0() {
        let a = ApUInt::from(vec![0x1234567890abcdefu64, 0x1234u64]).into_resized(80);
        let b = 0x1234u64;
        let result = a.widening_mul_chunk(b);
        assert_eq!(result.width, 144);
        assert_eq!(result.chunks, vec![0x60b60aa97760a28cu64, 0x14b5bdbu64, 0]);
    }

    #[test]
    fn test_widening_mul_chunk_1() {
        let a = ApUInt::from(123u32);
        let b = 1234u64;

        let result = a.widening_mul_chunk(b);

        assert_eq!(result.width, 96);
        assert_eq!(result.chunks, vec![0x250e6, 0]);
    }

    #[test]
    fn test_carrying_mul_chunk_0() {
        let a = ApUInt::from(123u32).into_resized(8);
        let b = 1234u64;

        let (result, carry) = a.carrying_mul_chunk(b);

        assert_eq!(result.chunks, vec![0xe6]);
        assert_eq!(result.width, 8);
        assert_eq!(carry.chunks, vec![0x250]);
        assert_eq!(carry.width, 64);
    }

    #[test]
    fn test_carrying_mul_chunk_1() {
        let a = ApUInt::from(vec![0x1234567890abcdefu64, 0x1234u64]).into_resized(80);
        let b = 0x1234u64;

        let (result, carry) = a.carrying_mul_chunk(b);

        assert_eq!(result.chunks, vec![0x60b60aa97760a28cu64, 0x5bdbu64]);
        assert_eq!(result.width, 80);
        assert_eq!(carry.chunks, vec![0x14b]);
        assert_eq!(carry.width, 64);
    }

    #[test]
    fn test_carrying_shl_0() {
        let a = ApUInt::from(0x12345678u32);
        let (result, carry) = a.carrying_shl(4);
        assert_eq!(result.chunks, vec![0x23456780u64]);
        assert_eq!(result.width, 32);
        assert_eq!(carry.chunks, vec![1]);
        assert_eq!(carry.width, 4);
    }

    #[test]
    fn test_carrying_shl_1() {
        let a = ApUInt::from(vec![0x1234567890abcdefu64, 0x0000567890abcdefu64]).into_resized(112);
        let (result, carry) = a.carrying_shl(72);
        assert_eq!(result.chunks, vec![0, 0x00007890abcdef00u64]);
        assert_eq!(result.width, 112);
        // 0x56_7890_abcd_ef12_3456
        assert_eq!(carry.chunks, vec![0x7890abcdef123456u64, 0x56u64]);
        assert_eq!(carry.width, 72);
    }

    #[test]
    fn test_widening_shl_0() {
        let a = ApUInt::from(0x12345678u32);
        let result = a.widening_shl(4);
        assert_eq!(result.chunks, vec![0x123456780u64]);
        assert_eq!(result.width, 36);
    }

    #[test]
    fn test_widening_shl_1() {
        let a = ApUInt::from(vec![0x1234567890abcdefu64, 0x0000567890abcdefu64]).into_resized(112);
        let result = a.widening_shl(72);
        assert_eq!(
            result.chunks,
            vec![0, 0x34567890abcdef00u64, 0x00567890abcdef12u64]
        );
        assert_eq!(result.width, 184);
    }

    #[test]
    fn test_widening_mul_0() {
        let a = ApUInt::from(vec![
            0xffffffffffffffffu64,
            0xffffffffffffffffu64,
            0xffffffffffffffffu64,
        ]);
        let b = ApUInt::from(vec![
            0xffffffffffffffffu64,
            0xffffffffffffffffu64,
            0xffffffffffffffffu64,
        ]);

        let result = a.widening_mul(&b);

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
    fn test_widening_mul_1() {
        let a = ApUInt::from(vec![
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
        ]);

        let b = ApUInt::from(vec![
            0xfedcba9876543210u64,
            0xfedcba9876543210u64,
            0xfedcba9876543210u64,
        ]);

        let result = a.widening_mul(&b);

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
    fn test_widening_mul_2() {
        let a = ApUInt::from(114514u32);
        let b = ApUInt::from(1919810u32);

        let result = a.widening_mul(&b);

        assert_eq!(result.width, 64);
        assert_eq!(result.chunks, [0x332fca5924u64])
    }

    #[test]
    fn test_carrying_mul() {
        let a = ApUInt::from(0x12345678u32);
        let b = ApUInt::from(0x87654321u32);
        let (lhs, rhs) = a.carrying_mul(&b);
        assert_eq!(lhs.chunks, vec![0x70b88d78u64]);
        assert_eq!(rhs.chunks, vec![0x9a0cd05u64]);
    }

    #[test]
    fn test_carrying_mul_1() {
        let a = ApUInt::from(vec![
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
        ]);

        let b = ApUInt::from(vec![
            0xfedcba9876543210u64,
            0xfedcba9876543210u64,
            0xfedcba9876543210u64,
        ]);

        let (result, carry) = a.carrying_mul(&b);

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
    fn test_overflowing_shr_0() {
        let a = ApUInt::from(vec![
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
        ]);

        let (result, overflowed) = a.overflowing_shr(64);

        assert_eq!(result.width, 192);
        assert_eq!(
            result.chunks,
            vec![0x1234567890abcdefu64, 0x1234567890abcdefu64, 0]
        );
        assert_eq!(overflowed.width, 64);
        assert_eq!(overflowed.chunks, vec![0x1234567890abcdefu64]);
    }

    #[test]
    fn test_overflowing_shr_1() {
        let a = ApUInt::from(0x123u16).into_resized(12);

        let (result, overflowed) = a.overflowing_shr(4);

        assert_eq!(result.width, 12);
        assert_eq!(result.chunks, vec![0x012]);
        assert_eq!(overflowed.width, 4);
        assert_eq!(overflowed.chunks, vec![0x3]);
    }

    #[test]
    fn test_overflowing_shr_2() {
        let a = ApUInt::from(vec![0x1234567890abcdefu64, 0xfedcba9876543210u64]);

        let (result, overflowed) = a.overflowing_shr(68);

        assert_eq!(result.width, 128);
        assert_eq!(result.chunks, vec![0x0fedcba987654321u64, 0]);
        assert_eq!(overflowed.width, 68);
        assert_eq!(overflowed.chunks, vec![0x1234567890abcdefu64, 0]);
    }

    #[test]
    fn test_div_rem_0() {
        let a = ApUInt::from(5u32);
        let b = ApUInt::from(2u32);

        let (quotient, remainder) = a.div_rem(b);

        assert_eq!(quotient.width, 32);
        assert_eq!(quotient.chunks, vec![0x2]);
        assert_eq!(remainder.width, 32);
        assert_eq!(remainder.chunks, vec![0x1]);
    }

    #[test]
    fn test_div_rem_1() {
        let a = ApUInt::from(vec![
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
            0x1234567890abcdefu64,
        ]);

        let b = ApUInt::from(vec![0xfedcba9876543210u64, 0xfedcba9876543210u64, 0]);
        // 0x124924923f07fffe, 0xea383d1d6c286420fc6c9395fcd4320f
        let (quotient, remainder) = a.div_rem(b);

        assert_eq!(quotient.width, 192);
        assert_eq!(quotient.chunks, vec![0x124924923f07fffeu64, 0, 0]);
        assert_eq!(remainder.width, 192);
        assert_eq!(
            remainder.chunks,
            vec![0xfc6c9395fcd4320fu64, 0xea383d1d6c286420u64, 0]
        );
    }
}
