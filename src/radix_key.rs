//! Conversions from scalar types to radix keys, which can be sorted bitwise.

use core::mem;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct RadixKey<const W: usize>([u8; W]);

impl<const W: usize> RadixKey<W> {
    // The key is a byte array, we can access any byte (digit) using an index.
    //
    // Here's why that's slow:
    //
    // If the compiler did at least a half-decent job, the key will be already
    // in a register. There are instructions to access the lowest byte, but to
    // go any higher, the key needs to be stored in memory and the byte has to
    // be loaded from there.
    //
    // The alternative is to right shift the desired byte into the lowest byte
    // of the register and read it from there. A quick benchmark reported up to
    // 20% improvement for the whole sort.

    #[cfg(not(any(target_pointer_width = "32", target_pointer_width = "64")))]
    #[inline(always)]
    pub fn bucket(&self, mut digit: usize) -> usize {
        self.0[digit] as usize
    }

    #[cfg(target_pointer_width = "32")]
    #[inline(always)]
    pub fn bucket(&self, mut digit: usize) -> usize {
        let mut key = [0u8; 4];
        if W == 1 {
            return self.0[0] as usize;
        } else if W <= 4 {
            key[..W].copy_from_slice(&self.0);
        } else if W == 8 {
            if digit < 4 {
                key.copy_from_slice(&self.0[0..4]);
            } else {
                key.copy_from_slice(&self.0[4..8]);
                digit -= 4;
            }
        } else if W == 16 {
            if digit < 4 {
                key.copy_from_slice(&self.0[0..4]);
            } else if digit < 8 {
                key.copy_from_slice(&self.0[4..8]);
                digit -= 4;
            } else if digit < 12 {
                key.copy_from_slice(&self.0[8..12]);
                digit -= 8;
            } else {
                key.copy_from_slice(&self.0[12..16]);
                digit -= 12;
            }
        } else {
            return self.0[digit] as usize;
        }
        ((u64::from_le_bytes(key) >> (digit * 8)) & 0xFF) as usize
    }

    #[cfg(target_pointer_width = "64")]
    #[inline(always)]
    pub fn bucket(&self, mut digit: usize) -> usize {
        let mut key = [0u8; 8];
        if W == 1 {
            return self.0[0] as usize;
        } else if W <= 8 {
            key[..W].copy_from_slice(&self.0);
        } else if W == 16 {
            if digit < 8 {
                key.copy_from_slice(&self.0[0..8]);
            } else {
                key.copy_from_slice(&self.0[8..16]);
                digit -= 8;
            }
        } else {
            return self.0[digit] as usize;
        }
        ((u64::from_le_bytes(key) >> (digit * 8)) & 0xFF) as usize
    }
}

#[cfg(test)]
impl<const W: usize> PartialOrd for RadixKey<W> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
impl<const W: usize> Ord for RadixKey<W> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        core::iter::zip(self.0, other.0)
            // Compare each byte
            .map(|(a, b)| a.cmp(&b))
            // The most significant bytes are at the back
            .rfind(|&o| o != core::cmp::Ordering::Equal)
            .unwrap_or(core::cmp::Ordering::Equal)
    }
}

/// Implements `From` for unsigned integer types.
macro_rules! key_impl_unsigned {
    ($($t:ty)*) => ($( key_impl_unsigned!($t as $t); )*);
    ($t:ty as $t2:ty) => (
        impl From<$t> for RadixKey<{core::mem::size_of::<$t>()}> {
            #[inline(always)]
            fn from(v: $t) -> Self {
                Self((v as $t2).to_le_bytes())
            }
        }
    );
}

key_impl_unsigned! { u8 u16 u32 u64 u128 usize }

key_impl_unsigned!(bool as u8);
key_impl_unsigned!(char as u32);

/// Implements `From` for signed integer types.
///
/// Signed integers are mapped to unsigned integers of the same width.
///
/// # Conversion
///
/// In two's complement, negative integers have the most significant bit set.
/// When we cast to an unsigned integer, we end up with negative integers
/// ordered after positive integers. To correct the order, we flip the sign bit.
///
/// ```plaintext
/// -128: 1000_0000    0000_0000
///   -1: 1111_1111    0111_0000
///    0: 0000_0000 -> 1000_0000
///    1: 0000_0001    1000_0001
///  128: 0111_1111    1111_1111
/// ```
macro_rules! key_impl_signed {
    ($($t:ty)*) => ($(
        impl From<$t> for RadixKey<{core::mem::size_of::<$t>()}> {
            #[inline(always)]
            fn from(v: $t) -> Self {
                const BIT_COUNT: usize = 8 * mem::size_of::<$t>();
                const SIGN_BIT: $t = 1 << (BIT_COUNT-1);
                Self((v ^ SIGN_BIT).to_le_bytes())
            }
        }
    )*)
}

key_impl_signed! { i8 i16 i32 i64 i128 isize }

/// Implements `From` for floating-point number types.
///
/// Floating-point numbers are mapped to unsigned integers of the same width.
///
/// # Conversion
///
/// IEEE 754 floating point numbers have a sign bit, an exponent, and a
/// mantissa. We can treat the exponent and the mantissa as a single block
/// denoting the magnitude.
///
/// This leaves us with a sign-magnitude representation. Magnitude increases
/// away from zero and the sign bit tells us in which direction.
///
/// After transmuting to unsigned integers, we have two problems:
/// - because of the sign bit, negative numbers end up after the positive
/// - negative numbers go in the opposite direction, because we went from
///     sign-magnitude representation (increases away from zero) to two's
///     complement (increases away from negative infinity)
///
/// To fix these problems, we:
/// - flip the sign bit, this makes negative numbers sort before positive
/// - flip the magnitude bits of negative numbers, this reverses the order of
///     negative values
///
/// This gives us a simple way to map floating-point numbers to unsigned
/// integers:
/// - sign bit 0: flip the sign bit
/// - sign bit 1: flip all the bits
///
/// These are halfs (~`f16`) for brevity, `f32` and `f64` only have more bits in
/// the middle.
///
/// ```plaintext
/// negative NaN  1_11111_xxxxxxxxx1    0_00000_xxxxxxxxx0
/// NEG_INFINITY  1_11111_0000000000    0_00000_1111111111
/// MIN           1_11110_1111111111 -> 0_00001_0000000000  flip all the bits
/// -1.0          1_01111_0000000000    0_10000_1111111111
/// MAX_NEGATIVE  1_00000_0000000001    0_11111_1111111110
/// -0.0          1_00000_0000000000    0_11111_1111111111
/// --------------------------------------------------------------------------
/// 0.0           0_00000_0000000000    1_00000_0000000000
/// MIN_POSITIVE  0_00000_0000000001    1_00000_0000000001
/// 1.0           0_01111_0000000000 -> 1_01111_0000000000  flip the sign bit
/// MAX           0_11110_1111111111    1_11110_1111111111
/// INFINITY      0_11111_0000000000    1_11111_0000000000
/// positive NaN  0_11111_xxxxxxxxx1    1_11111_xxxxxxxxx1
/// ```
///
/// # Special values
///
/// As shown above, infinities are sorted correctly before and after min and max
/// values. NaN values, depending on their sign bit, end up in two blocks at the
/// very beginning and at the very end.
macro_rules! key_impl_float {

    // signed_key type is needed for arithmetic right shift
    ($($t:ty as $signed_key:ty),*) => ($(
        impl From<$t> for RadixKey<{core::mem::size_of::<$t>()}> {
            #[inline(always)]
            fn from(v: $t) -> Self {
                const BIT_COUNT: usize = 8 * mem::size_of::<$t>();
                // all floats need to have the sign bit flipped
                const FLIP_SIGN_MASK: $signed_key = 1 << (BIT_COUNT-1); // 0x800...

                let bits = v.to_bits() as $signed_key;
                // negative floats need to have the rest flipped as well, extend the sign bit to the
                // whole width with arithmetic right shift to get a flip mask 0x00...0 or 0xFF...F
                let flip_negative_mask = bits >> (BIT_COUNT-1);

                Self((bits ^ (flip_negative_mask | FLIP_SIGN_MASK)).to_le_bytes())
            }
        }
    )*)
}

key_impl_float! { f32 as i32, f64 as i64 }

#[cfg(test)]
mod tests {
    //! Tests that `to_radix_key` implementations preserve the order of the
    //! values. Tests use `std::slice::sort_by_key` to make sure that the
    //! sorting function is reliable.

    use super::*;

    #[test]
    fn test_key_bool() {
        assert!(RadixKey::from(false) < RadixKey::from(true));
    }

    #[test]
    fn test_key_char() {
        #[rustfmt::skip]
        let mut actual = [
            '\u{0}',     '\u{1}',     '\u{F}',     '\u{7F}',    // 1-byte sequence
            '\u{80}',    '\u{81}',    '\u{FF}',    '\u{7FF}',   // 2-byte sequence
            '\u{800}',   '\u{801}',   '\u{FFF}',   '\u{FFFF}',  // 3-byte sequence
            '\u{10000}', '\u{10001}', '\u{FFFFF}', '\u{10FFFF}' // 4-byte sequence
        ];
        let expected = actual;
        actual.reverse();
        actual.sort_by_key(|&v| RadixKey::from(v));
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_key_numeric() {
        macro_rules! implement {
            ($($t:ident)*) => ($(
                let mut actual = [
                    core::$t::MIN, core::$t::MIN+1, core::$t::MIN / 2,
                    core::$t::MIN >> (mem::size_of::<$t>() * 8 / 2),
                    core::$t::MAX, core::$t::MAX-1, core::$t::MAX / 2,
                    core::$t::MAX >> (mem::size_of::<$t>() * 8 / 2),
                    (-1i8) as $t, 0, 1,
                ];
                let mut expected = actual;
                expected.sort();
                actual.sort_by_key(|&v| RadixKey::from(v));
                assert_eq!(actual, expected);
            )*)
        }
        implement! {
            u8 u16 u32 u64 u128 usize
            i8 i16 i32 i64 i128 isize
        }
    }

    #[test]
    #[allow(clippy::inconsistent_digit_grouping)]
    fn test_key_float() {
        {
            // F32
            #[allow(clippy::unusual_byte_groupings)]
            let mut actual = [
                f32::from_bits(0b1_11111111_11111111111111111111111), // negative NaN
                f32::from_bits(0b1_11111111_00000000000000000000001), // negative NaN
                f32::from_bits(0b1_11111111_00000000000000000000000), // negative infinity
                f32::from_bits(0b1_11111110_11111111111111111111111), // min
                f32::from_bits(0b1_01111111_00000000000000000000000), // negative one
                f32::from_bits(0b1_01111110_11111111111111111111111), // smallest larger than negative one
                f32::from_bits(0b1_00000001_00000000000000000000000), // max negative
                f32::from_bits(0b1_00000000_11111111111111111111111), // min negative subnormal
                f32::from_bits(0b1_00000000_00000000000000000000001), // max negative subnormal
                f32::from_bits(0b1_00000000_00000000000000000000000), // negative zero
                f32::from_bits(0b0_00000000_00000000000000000000000), // positive zero
                f32::from_bits(0b0_00000000_00000000000000000000001), // min positive subnormal
                f32::from_bits(0b0_00000000_11111111111111111111111), // max positive subnormal
                f32::from_bits(0b0_00000001_00000000000000000000000), // min positive
                f32::from_bits(0b0_01111110_11111111111111111111111), // largest smaller than positive one
                f32::from_bits(0b0_01111111_00000000000000000000000), // positive one
                f32::from_bits(0b0_11111110_11111111111111111111111), // max
                f32::from_bits(0b0_11111111_00000000000000000000000), // positive infinity
                f32::from_bits(0b0_11111111_00000000000000000000001), // positive NaN
                f32::from_bits(0b0_11111111_11111111111111111111111), // positive NaN
            ];
            let expected = actual;
            actual.reverse();
            actual.sort_by_key(|&v| RadixKey::from(v));
            for (a, e) in actual.iter().zip(expected.iter()) {
                assert_eq!(a.to_bits(), e.to_bits());
            }
        }
        {
            // F64
            #[rustfmt::skip]
            #[allow(clippy::unusual_byte_groupings)]
            let mut actual = [
                f64::from_bits(0b1_11111111111_1111111111111111111111111111111111111111111111111111), // negative NaN
                f64::from_bits(0b1_11111111111_0000000000000000000000000000000000000000000000000001), // negative NaN
                f64::from_bits(0b1_11111111111_0000000000000000000000000000000000000000000000000000), // negative infinity
                f64::from_bits(0b1_11111111110_1111111111111111111111111111111111111111111111111111), // min
                f64::from_bits(0b1_01111111111_0000000000000000000000000000000000000000000000000000), // negative one
                f64::from_bits(0b1_01111111110_1111111111111111111111111111111111111111111111111111), // min larger than negative one
                f64::from_bits(0b1_00000000001_0000000000000000000000000000000000000000000000000000), // max negative
                f64::from_bits(0b1_00000000000_1111111111111111111111111111111111111111111111111111), // min negative subnormal
                f64::from_bits(0b1_00000000000_0000000000000000000000000000000000000000000000000001), // max negative subnormal
                f64::from_bits(0b1_00000000000_0000000000000000000000000000000000000000000000000000), // negative zero
                f64::from_bits(0b0_00000000000_0000000000000000000000000000000000000000000000000000), // positive zero
                f64::from_bits(0b0_00000000000_0000000000000000000000000000000000000000000000000001), // min positive subnormal
                f64::from_bits(0b0_00000000000_1111111111111111111111111111111111111111111111111111), // max positive subnormal
                f64::from_bits(0b0_00000000001_0000000000000000000000000000000000000000000000000000), // min positive
                f64::from_bits(0b0_01111111110_1111111111111111111111111111111111111111111111111111), // max smaller than positive one
                f64::from_bits(0b0_01111111111_0000000000000000000000000000000000000000000000000000), // positive one
                f64::from_bits(0b0_11111111110_1111111111111111111111111111111111111111111111111111), // max
                f64::from_bits(0b0_11111111111_0000000000000000000000000000000000000000000000000000), // positive infinity
                f64::from_bits(0b0_11111111111_0000000000000000000000000000000000000000000000000001), // positive NaN
                f64::from_bits(0b0_11111111111_1111111111111111111111111111111111111111111111111111), // positive NaN
            ];
            let expected = actual;
            actual.reverse();
            actual.sort_by_key(|&v| RadixKey::from(v));
            for (a, e) in actual.iter().zip(expected.iter()) {
                assert_eq!(a.to_bits(), e.to_bits());
            }
        }
    }
}
