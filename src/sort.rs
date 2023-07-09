//! Implementations of radix keys and sorting functions.

use core::{mem, ops::Add};

use crate::{double_buffer::DoubleBuffer, radix_key::RadixKey};

const BUCKET_COUNT: usize = 256;

#[derive(Clone)]
pub struct Config {
    skip_single_value_digits: bool,
}

impl Config {
    pub const fn with_value_based_optimizations() -> Self {
        Self {
            skip_single_value_digits: true,
        }
    }

    pub const fn without_value_based_optimizations() -> Self {
        Self {
            skip_single_value_digits: false,
        }
    }

    pub const fn skip_single_value_digits(&self) -> bool {
        self.skip_single_value_digits
    }
}

impl Default for Config {
    fn default() -> Self {
        Self::with_value_based_optimizations()
    }
}

/// Dispatches the sort. Chooses the smallest offset type that can represent all
/// positions in the slice.
pub(crate) fn dispatch_sort<T, F, const W: usize>(slice: &mut [T], key_fn: F, config: Config)
where
    F: FnMut(&T) -> RadixKey<W>,
{
    // Sorting has no meaningful behavior on zero-sized types.
    if mem::size_of::<T>() == 0 {
        return;
    }

    // Choose the offset type based on the length of the slice.
    match slice.len() {
        len if len < 2 => (),
        len if len <= core::u8::MAX as usize => {
            sort::<u8, T, _, W>(slice, key_fn, config);
        }
        #[cfg(not(target_pointer_width = "16"))]
        len if len <= core::u16::MAX as usize => {
            sort::<u16, T, _, W>(slice, key_fn, config);
        }
        #[cfg(not(any(target_pointer_width = "16", target_pointer_width = "32")))]
        len if len <= core::u32::MAX as usize => {
            sort::<u32, T, _, W>(slice, key_fn, config);
        }
        #[cfg(not(any(
            target_pointer_width = "16",
            target_pointer_width = "32",
            target_pointer_width = "64"
        )))]
        len if len <= core::u64::MAX as usize => {
            sort::<u64, T, _, W>(slice, key_fn, config);
        }
        _ => {
            sort::<usize, T, _, W>(slice, key_fn, config);
        }
    }
}

/// Sorts the slice based on the keys returned by the key function.
///
/// # Panics
///
/// Panics on a best effort basis if the key function returned different keys
/// when called repeatedly with the same parameter.
#[inline(never)]
fn sort<O, T, F, const W: usize>(input: &mut [T], mut key_fn: F, config: Config)
where
    O: Offset,
    F: FnMut(&T) -> RadixKey<W>,
{
    // In the worst case (`u128` key, `input.len() >= u32::MAX`) uses 32 KiB on
    // the stack.
    let mut bucket_sizes = [[O::ZERO; BUCKET_COUNT]; W];

    calc_bucket_sizes(input, &mut bucket_sizes, &mut key_fn);

    let skip_digit = if config.skip_single_value_digits() {
        calc_skip_digits(input, &bucket_sizes, &mut key_fn)
    } else {
        [false; W]
    };

    let bucket_offsets = convert_bucket_sizes_to_offsets(&mut bucket_sizes, &skip_digit);

    // Drop impl of DoubleBuffer ensures that `input` is consistent,
    // e.g. in case of panic in the key function.
    let mut buffer = DoubleBuffer::new(input);

    // This is the main sorting loop. We sort the elements by each digit of the
    // key, starting from the least-significant. After sorting by the last, most
    // significant digit, our elements are sorted.
    #[allow(clippy::needless_range_loop)]
    for digit in 0..W {
        if !skip_digit[digit] {
            if let Err(()) = sort_by_digit(&mut buffer, &bucket_offsets[digit], digit, &mut key_fn)
            {
                // The bucket sizes do not match expected sizes, the key
                // function is unreliable (programming mistake).
                panic!(
                    "The key function is not reliable: when called repeatedly, \
                    it returned different keys for the same element."
                )
            }
        }
    }
}

/// Calculates the bucket sizes.
fn calc_bucket_sizes<O, T, F, const W: usize>(
    input: &[T],
    bucket_sizes: &mut [[O; BUCKET_COUNT]; W],
    mut key_fn: F,
) where
    O: Offset,
    F: FnMut(&T) -> RadixKey<W>,
{
    for t in input.iter() {
        let key = key_fn(t);
        #[allow(clippy::needless_range_loop)]
        for digit in 0..W {
            bucket_sizes[digit][key.bucket(digit)].increment();
        }
    }
}

/// For each digit, check if all the elements are in the same bucket.
/// If so, we can skip the whole digit. Instead of checking all the buckets,
/// we pick a key and check whether the bucket contains all the elements.
fn calc_skip_digits<O, T, F, const W: usize>(
    input: &[T],
    bucket_sizes: &[[O; BUCKET_COUNT]; W],
    mut key_fn: F,
) -> [bool; W]
where
    O: Offset,
    F: FnMut(&T) -> RadixKey<W>,
{
    let mut skip_digit = [false; W];
    let len = input.len();
    let first_key = key_fn(input.first().unwrap());
    #[allow(clippy::needless_range_loop)]
    for digit in 0..W {
        let first_bucket = first_key.bucket(digit);
        let skip = bucket_sizes[digit][first_bucket].as_usize() == len;
        skip_digit[digit] = skip;
    }
    skip_digit
}

/// Turns the histogram/bucket sizes in-place into bucket offsets by calculating
/// a prefix sum.
///
/// ```plaintext
/// Sizes:     |---b1---|-b2-|---b3---|----b4----|
/// Offsets:   0        b1   b1+b2    b1+b2+b3
/// ```
fn convert_bucket_sizes_to_offsets<'a, O, const W: usize>(
    bucket_sizes: &'a mut [[O; BUCKET_COUNT]; W],
    skip_digit: &[bool; W],
) -> &'a [[O; BUCKET_COUNT]; W]
where
    O: Offset,
{
    for digit in 0..W {
        if !skip_digit[digit] {
            let mut offset_acc = O::ZERO;
            for size in bucket_sizes[digit].iter_mut() {
                *size = offset_acc.get_and_add(*size);
            }
        }
    }

    bucket_sizes
}

/// Sorts the buffer by a single digit of the key. The sort is stable.
///
/// If the key function returns different keys when called repeatedly with the
/// same parameter, the sort order is not specified and an error might be
/// returned on a best effort basis. If an error is returned, the buffer is not
/// swapped, i.e. the read part contains the original data.
fn sort_by_digit<O, T, F, const W: usize>(
    buffer: &mut DoubleBuffer<T>,
    init_offsets: &[O; BUCKET_COUNT],
    digit: usize,
    mut key_fn: F,
) -> Result<(), ()>
where
    O: Offset,
    F: FnMut(&T) -> RadixKey<W>,
{
    // Make a copy. We need the original to check that all buckets were filled.
    let mut offsets = *init_offsets;

    buffer.scatter(|t| {
        let key = key_fn(t);
        let bucket = key.bucket(digit);
        offsets[bucket].get_and_increment().as_usize()
    })?;

    // Check that each bucket had the same number of insertions as we expected.
    // If this is not true, then the key function is unreliable and some
    // elements in the write buffer were not written to.
    //
    // If the key function is unreliable, but the sizes of buckets ended up
    // being the same, it would not get detected. This is sound, the only
    // consequence is that the elements won't be sorted right.
    //
    // The `offsets` array now contains the end offset of each bucket. If the
    // bucket is full, the end offset is equal to the initial offset of the next
    // bucket, i.e. `offset[bucket] == init_offset[bucket+1]`. The end offset of
    // the last bucket should be equal to the buffer length.
    let all_buckets_filled = offsets[0..BUCKET_COUNT - 1] == init_offsets[1..BUCKET_COUNT]
        && offsets[BUCKET_COUNT - 1].as_usize() == buffer.len();

    if all_buckets_filled {
        unsafe {
            // SAFETY: we just ensured that every index was written to.
            buffer.swap();
        }
        Ok(())
    } else {
        Err(())
    }
}

/// Offset type used for bucket ranges. The wrapping addition is used to prevent
/// an unreliable key function (returning different keys for the same element)
/// from overflowing the offset and crashing. We could allow an early crash on
/// overflow here, but checking for it is not free, so we rather do the check
/// after the sorting pass.
trait Offset: Copy + PartialEq + Eq + Add<Output = Self> {
    const ZERO: Self;
    const ONE: Self;

    /// Casts the offset to `usize`.
    fn as_usize(self) -> usize;

    /// Adds to the offset, returning the previous value. The addition wraps around.
    fn get_and_add(&mut self, val: Self) -> Self;

    /// Adds one to the offset, returning the previous value. The addition wraps around.
    fn get_and_increment(&mut self) -> Self {
        self.get_and_add(Self::ONE)
    }

    /// Adds one the offset. The addition wraps around.
    fn increment(&mut self) {
        self.get_and_increment();
    }
}

macro_rules! impl_offset {
    ($($offset_type:ty)*) => ($(
        impl Offset for $offset_type {
            const ZERO: Self = 0;
            const ONE: Self = 1;

            #[inline(always)]
            fn as_usize(self) -> usize {
                self as usize
            }

            #[inline(always)]
            fn get_and_add(&mut self, val: Self) -> Self {
                let res = *self;
                *self = self.wrapping_add(val);
                res
            }
        }
    )*);
}

impl_offset! { u8 u16 u32 u64 usize }
