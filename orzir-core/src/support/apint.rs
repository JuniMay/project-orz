pub type ApUIntChunk = u64;

/// An arbitrary precision integer.
#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub struct ApUInt {
    /// The width of the integer in bits.
    width: usize,
    /// The chunks of the integer.
    chunks: Vec<ApUIntChunk>,
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

    #[inline]
    fn chunk_mask(&self, idx: usize) -> ApUIntChunk {
        if idx == self.chunks.len() - 1 {
            // this is the last chunk
            let bits = self.width % ApUIntChunk::BITS as usize;
            if bits == 0 {
                // this chunk is full, the width is a multiple of the chunk size
                ApUIntChunk::MAX
            } else {
                // this chunk is not full, mask the bits
                (1 << bits) - 1
            }
        } else {
            ApUIntChunk::MAX
        }
    }

    /// Truncate the integer to the given bit width
    ///
    /// This will not only change the length pf the chunks, but also the value
    /// of the last chunk.
    #[inline]
    pub fn truncate(&mut self, width: usize) {
        self.width = width;
        let num_chunks = (width + ApUIntChunk::BITS as usize - 1) / ApUIntChunk::BITS as usize;
        self.chunks.resize(num_chunks, 0);
        self.chunks[num_chunks - 1] &= self.chunk_mask(num_chunks - 1);
    }

    #[inline]
    pub fn into_truncated(self, width: usize) -> Self {
        let mut apint = self;
        apint.truncate(width);
        apint
    }

    /// Addition with carrying, returns the carry.
    ///
    /// The carry will occur if the sum exceeds the `width`.
    pub fn carrying_add(&self, other: &Self) -> (Self, bool) {
        let mut result = ApUInt::new(self.width);
        let mut carry = false;
        for (i, ((a, b), r)) in self
            .chunks
            .iter()
            .zip(other.chunks.iter())
            .zip(result.chunks.iter_mut())
            .enumerate()
        {
            let (sum, carry_0) = a.overflowing_add(*b);
            let (sum, carry_1) = sum.overflowing_add(u64::from(carry));
            let mask = self.chunk_mask(i);
            *r = sum & mask;
            carry = carry_0 || carry_1 || sum != *r;
        }

        (result, carry)
    }

    pub fn carrying_mul(&self, other: &Self) -> (Self, Self) {
        todo!()
    }

    /// Shift the integer to the left by `shamt` bits.
    /// 
    /// Returns the result and the overflowed integer (also an `ApUInt`).
    pub fn carrying_shl(&self, other: &Self) -> (Self, Self) {
        todo!()
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
            return None;
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_truncate() {
        let mut apint = ApUInt::from(0x12345678u32);
        apint.truncate(16);
        assert_eq!(apint.chunks, vec![0x5678]);
        apint.truncate(8);
        assert_eq!(apint.chunks, vec![0x78]);
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
        let a = ApUInt::from(vec![0x123456781234u64, 0x56784321u64]).into_truncated(96);
        let b = ApUInt::from(vec![0xf76543214321u64, 0xf3211234u64]).into_truncated(96);

        let (result, carry) = a.carrying_add(&b);

        assert_eq!(result.chunks, vec![0x1099999995555u64, 0x49995555u64]);
        assert!(carry);
    }
}
