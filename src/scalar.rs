
//! Conversions from scalar types to radix keys, which can be sorted bitwise.

use core::mem;

use crate::sort::RadixKey;

/// Scalar types which can be converted to radix sorting keys.
pub trait Scalar: Copy + private::Sealed {

    type ToRadixKey: RadixKey;

    /// Maps the value to a radix sorting key, preserving the sorting order.
    fn to_radix_key(self) -> Self::ToRadixKey;
}

/// Implements `Scalar` for an unsigned integer type(s).
/// 
/// Since we use unsigned integers as radix sorting keys, we directly return the
/// value.
macro_rules! key_impl_unsigned {
    ($($t:ty)*) => ($( key_impl_unsigned!($t => $t); )*);
    ($t:ty => $radix_key:ty) => (
        impl Scalar for $t {
            type ToRadixKey = $radix_key;
            #[inline(always)]
            fn to_radix_key(self) -> Self::ToRadixKey {
                self as $radix_key
            }
        }
    )
}

key_impl_unsigned! { u8 u16 u32 u64 u128 }

#[cfg(target_pointer_width = "16")]
key_impl_unsigned!(usize => u16);

#[cfg(target_pointer_width = "32")]
key_impl_unsigned!(usize => u32);

#[cfg(target_pointer_width = "64")]
key_impl_unsigned!(usize => u64);

#[cfg(target_pointer_width = "128")]
key_impl_unsigned!(usize => u128);

key_impl_unsigned!(bool => u8);
key_impl_unsigned!(char => u32);


/// Implements `Scalar` for a signed integer type(s).
/// 
/// Signed integers are mapped to unsigned integers of the same width.
/// 
/// # Conversion
/// 
/// In two's complement, negative integers have the most significant bit set.
/// When we cast to an unsigned integer, we end up with negative integers
/// ordered after positive integers. To correct the order, we flip the sign bit.
/// 
/// ```ignore
/// -128: 1000_0000    0000_0000
///   -1: 1111_1111    0111_0000
///    0: 0000_0000 -> 1000_0000
///    1: 0000_0001    1000_0001
///  128: 0111_1111    1111_1111
/// ```
macro_rules! key_impl_signed {
    ($($t:ty => $radix_key:ty),*) => ($(
        impl Scalar for $t {
            type ToRadixKey = $radix_key;
            #[inline(always)]
            fn to_radix_key(self) -> Self::ToRadixKey {
                const BIT_COUNT: usize = 8 * mem::size_of::<$t>();
                const SIGN_BIT: $radix_key = 1 << (BIT_COUNT-1);
                (self as $radix_key) ^ SIGN_BIT
            }
        }
    )*)
}

key_impl_signed! {
    i8 => u8,
    i16 => u16,
    i32 => u32,
    i64 => u64,
    i128 => u128
}

#[cfg(target_pointer_width = "16")]
key_impl_signed!(isize => u16);

#[cfg(target_pointer_width = "32")]
key_impl_signed!(isize => u32);

#[cfg(target_pointer_width = "64")]
key_impl_signed!(isize => u64);

#[cfg(target_pointer_width = "128")]
key_impl_signed!(isize => u128);


/// Implements `Scalar` for a floating-point number type(s).
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
/// ```ignore
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
    ($($t:ty => $radix_key:ty : $signed_key:ty),*) => ($(
        impl Scalar for $t {
            type ToRadixKey = $radix_key;
            #[inline(always)]
            fn to_radix_key(self) -> Self::ToRadixKey {
                const BIT_COUNT: usize = 8 * mem::size_of::<$t>();
                // all floats need to have the sign bit flipped
                const FLIP_SIGN_MASK: $radix_key = 1 << (BIT_COUNT-1); // 0x800...

                let bits = self.to_bits();
                // negative floats need to have the rest flipped as well, extend the sign bit to the
                // whole width with arithmetic right shift to get a flip mask 0x00...0 or 0xFF...F
                let flip_negative_mask = ((bits as $signed_key) >> (BIT_COUNT-1)) as $radix_key;

                bits ^ (flip_negative_mask | FLIP_SIGN_MASK)
            }
        }
    )*)
}

key_impl_float! {
    f32 => u32 : i32,
    f64 => u64 : i64
}


mod private {
    /// This trait serves as a seal for the `Scalar` trait to prevent downstream
    /// implementations.
    pub trait Sealed {}
    macro_rules! sealed_impl { ($($t:ty)*) => ($(
        impl Sealed for $t {}
    )*) }
    sealed_impl! {
        bool char
        u8 u16 u32 u64 u128 usize
        i8 i16 i32 i64 i128 isize
        f32 f64
    }
}


#[cfg(test)]
mod tests {
    //! Tests that `to_radix_key` implementations preserve the order of the
    //! values. Tests use `std::slice::sort_by_key` to make sure that the
    //! sorting function is reliable.

    use super::*;

    #[test]
    fn test_key_bool() {
        assert!(false.to_radix_key() < true.to_radix_key());
    }

    #[test]
    fn test_key_char() {
        let mut actual = [
            '\u{0}',     '\u{1}',     '\u{F}',     '\u{7F}',    // 1-byte sequence
            '\u{80}',    '\u{81}',    '\u{FF}',    '\u{7FF}',   // 2-byte sequence
            '\u{800}',   '\u{801}',   '\u{FFF}',   '\u{FFFF}',  // 3-byte sequence
            '\u{10000}', '\u{10001}', '\u{FFFFF}', '\u{10FFFF}' // 4-byte sequence
        ];
        let expected = actual.clone();
        actual.reverse();
        actual.sort_by_key(|v| v.to_radix_key());
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
                let mut expected = actual.clone();
                expected.sort();
                actual.sort_by_key(|v| v.to_radix_key());
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
        {   // F32
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
            actual.sort_by_key(|v| v.to_radix_key());
            for (a, e) in actual.iter().zip(expected.iter()) {
                assert_eq!(a.to_bits(), e.to_bits());
            }
        }
        {   // F64
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
            actual.sort_by_key(|v| v.to_radix_key());
            for (a, e) in actual.iter().zip(expected.iter()) {
                assert_eq!(a.to_bits(), e.to_bits());
            }
        }
    }

}
