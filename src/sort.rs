
//! Implementations of radix keys and sorting functions.

use alloc::vec::Vec;
use core::mem;

use crate::Key;

/// Unsigned integers used as sorting keys for radix sort.
/// 
/// These keys can be sorted bitwise. For conversion from scalar types, see
/// [`Scalar::to_radix_key()`].
/// 
/// Mapping of floating point numbers onto unsigned integers is a bit more
/// involved, see the `Key` implementation for details.
/// 
/// [`Scalar::to_radix_key()`]: fn.sort_by_key.html
/// [`Key::to_radix_key`]: fn.sort_by_key.html
pub trait RadixKey: Key {

    /// Sorts the slice using provided key extraction function.
    /// Runs one of the other functions, based on the length of the slice.
    #[inline]
    fn radix_sort<T, F>(slice: &mut[T], mut key_fn: F, unopt: bool)
        where F: FnMut(&T) -> Self
    {
        // Sorting has no meaningful behavior on zero-sized types.
        if mem::size_of::<T>() == 0 {
            return;
        }

        let len = slice.len();
        if len < 2 {
           return;
        }

        #[cfg(any(target_pointer_width = "64", target_pointer_width = "128"))]
        {
            if len <= core::u32::MAX as usize {
                Self::radix_sort_u32(slice, |t| key_fn(t), unopt);
                return;
            }
        }
        
        Self::radix_sort_usize(slice, |t| key_fn(t), unopt);
    }

    /// Sorting for slices with up to u32::MAX elements, which is a majority of
    /// cases. Uses u32 indices for histograms and offsets to save cache space.
    #[cfg(any(target_pointer_width = "64", target_pointer_width = "128"))]
    fn radix_sort_u32<T, F>(slice: &mut[T], key_fn: F, unopt: bool)
        where F: FnMut(&T) -> Self;

    /// Sorting function for slices with up to usize::MAX elements.
    fn radix_sort_usize<T, F>(slice: &mut[T], key_fn: F, unopt: bool)
        where F: FnMut(&T) -> Self;
}

macro_rules! sort_impl {
    ($name:ident, $radix_key_type:ty, $offset_type:ty) => {
        #[inline(never)] // Don't inline, the offset array needs a lot of stack
        fn $name<T, F>(input: &mut [T], mut key_fn: F, unopt: bool)
            where F: FnMut(&T) -> $radix_key_type
        {
            // This implementation is radix 256, so the size of a digit is 8 bits / one byte.
            // You can experiment with different digit sizes by changing this constant, but
            // according to my benchmarks, the overhead from arbitrary shifting and masking
            // will be higher than what you save by having less digits.
            const DIGIT_BITS: usize = 8;

            const RADIX_KEY_BITS: usize = mem::size_of::<$radix_key_type>() * 8;
            
            // Have one bucket for each possible value of the digit
            const BUCKET_COUNT: usize = 1 << DIGIT_BITS;

            const DIGIT_COUNT: usize = (RADIX_KEY_BITS + DIGIT_BITS - 1) / DIGIT_BITS;
            
            let digit_skip_enabled: bool = !unopt;
            
            
            /// Extracts the digit from the key, starting with the least significant digit.
            /// The digit is used as a bucket index.
            #[inline(always)]
            fn extract_digit(key: $radix_key_type, digit: usize) -> usize {
                const DIGIT_MASK: $radix_key_type = ((1 << DIGIT_BITS) - 1) as $radix_key_type;
                ((key >> (digit * DIGIT_BITS)) & DIGIT_MASK) as usize
            }
            

            // In the worst case (u128 key, input len >= u32::MAX) uses 32 KiB on the stack.
            let mut offsets = [[0 as $offset_type; BUCKET_COUNT]; DIGIT_COUNT];
            let mut skip_digit = [false; DIGIT_COUNT];

            {   // Calculate bucket offsets for each digit.

                // Calculate histograms/bucket sizes and store in `offsets`.
                for t in input.iter() {
                    let key = key_fn(t);
                    for digit in 0..DIGIT_COUNT {
                        offsets[digit][extract_digit(key, digit)] += 1;
                    }
                }
                
                if digit_skip_enabled {
                    // For each digit, gheck if all the elements are in the same bucket.
                    // If so, we can skip the whole digit. Instead of checking all the buckets,
                    // we pick a key and check whether the bucket contains all the elements.
                    let last_key = key_fn(input.last().unwrap());
                    for digit in 0..DIGIT_COUNT {
                        let last_bucket = extract_digit(last_key, digit);
                        let skip = offsets[digit][last_bucket] == input.len() as $offset_type;
                        skip_digit[digit] = skip;
                    }
                }
                
                // Turn the histogram/bucket sizes into bucket offsets by calculating a prefix sum.
                // Sizes:     |---b1---|-b2-|---b3---|----b4----|
                // Offsets:   0        b1   b1+b2    b1+b2+b3
                for digit in 0..DIGIT_COUNT {
                    if !(digit_skip_enabled && skip_digit[digit]) {
                        let mut offset_acc = 0;
                        for count in offsets[digit].iter_mut() {
                            let offset = offset_acc;
                            offset_acc += *count;
                            *count = offset;
                        }
                    }
                }

                // The `offsets` array now contains bucket offsets for each digit.
            }
            
            let len = input.len();

            // Drop impl of DoubleBuffer ensures that `input` is consistent,
            // e.g. in case of panic in the key function.
            let mut buffer = DoubleBuffer::new(input);

            // This is the main sorting loop. We sort the elements by each digit of the key,
            // starting from the least-significant. After sorting by the last, most significant
            // digit, our elements are sorted.
            for digit in 0..DIGIT_COUNT {
                if !(digit_skip_enabled && skip_digit[digit]) {

                    // Copy the offsets. We need the original later for a consistency check.
                    // As we write elements into each bucket, we increment the bucket offset
                    // so that it points to the next empty slot.
                    let mut working_offsets: [$offset_type; BUCKET_COUNT] = offsets[digit];

                    for r_pos in 0..len {
                        let t: &T = unsafe {
                            // This is safe, r_pos is in (0..len)
                            buffer.read(r_pos)
                        };
                        
                        let key = key_fn(t);
                        let bucket = extract_digit(key, digit);

                        let offset = &mut working_offsets[bucket];
                        
                        unsafe {
                            // Make sure the offset is in bounds. An unreliable key function, which
                            // returns different keys for the same element when called repeatedly,
                            // can cause offsets to go out of bounds.
                            let w_pos = usize::min(*offset as usize, len - 1);

                            // This is safe, w_pos is in (0..len)
                            buffer.write(w_pos, t);
                        }

                        // Increment the offset of the bucket. Use wrapping add in case the
                        // key function is unreliable and the bucket overflowed.
                        *offset = offset.wrapping_add(1);
                    }

                    // Check that each bucket had the same number of insertions as we expected.
                    // If this is not true, then the key function is unreliable and the write buffer
                    // is not consistent: some elements were overwritten, some were not written to
                    // and contain garbage.
                    //
                    // If the key function is unreliable, but the sizes of buckets ended up being
                    // the same, it would not get detected. This is sound, the only consequence is
                    // that the elements won't be sorted right.
                    {
                        // The `working_offsets` array now contains the end offset of each bucket.
                        // If the bucket is full, the working offset is now equal to the original
                        // offset of the next bucket. The working offset of the last bucket should
                        // be equal to the number of elements.
                        let bucket_sizes_match =
                            working_offsets[0..BUCKET_COUNT-1] == offsets[digit][1..BUCKET_COUNT] &&
                            working_offsets[BUCKET_COUNT-1] == len as $offset_type;
                            
                        if !bucket_sizes_match {
                            // The bucket sizes do not match expected sizes, the key function is
                            // unreliable (programming mistake).
                            //
                            // Drop impl of the double buffer will make sure that the input slice is
                            // consistent. This would happen automatically, but I'm making it
                            // explicit for clarity.
                            drop(buffer);
                            panic!("The key function is not reliable: when called repeatedly, \
                                it returned different keys for the same element.")
                        }
                    }

                    unsafe {
                        // This is safe, we just ensured that the write buffer is consistent.
                        buffer.swap();
                    }
                }
            }

            // In case the result ended up in the temporary buffer, the Drop impl will copy it over
            // to the input slice. This would happen automatically, but I'm making it explicit for
            // clarity.
            drop(buffer);
        }
    }
}

macro_rules! radix_key_impl {
    ($($key_type:ty)*) => ($(
        impl RadixKey for $key_type {
            
            #[cfg(any(target_pointer_width = "64", target_pointer_width = "128"))]
            sort_impl!(radix_sort_u32, $key_type, u32);

            sort_impl!(radix_sort_usize, $key_type, usize);
        }
    )*)
}

radix_key_impl!{ u8 u16 u32 u64 u128 }


/// Double buffer. Allocates a temporary memory the size of the slice, so that
/// elements can be freely reordered from buffer to buffer.
/// 
/// # Consistency
/// 
/// For the purposes of this struct, buffer in a consistent state contains a
/// permutation of elements from the original slice. In other words, elements
/// can be reordered, but not duplicated or lost.
/// 
/// `read_buf` is always consistent. Before calling `swap`, the caller must
/// ensure that `write_buf` is also consistent.
/// 
/// # Drop behavior
/// 
/// Drop impl ensures that the slice this buffer was constructed with is left in
/// a consistent state. If the input slice ended up as `write_buf`, the
/// temporary memory (which is now `read_buf` and therefore consistent) is
/// copied into the slice and the buffers are swapped.
struct DoubleBuffer<'a, T> {
    slice: &'a mut [T],
    _aux: Vec<T>,

    /// Read buffer is read-only and always consistent.
    read_buf: *const T,

    /// Write buffer is write-only. Elements can be present multiple times or
    /// not at all. The caller must ensure that by the time of calling `swap`
    /// it has a complete set of elements and each element is present exactly
    /// once.
    write_buf: *mut T,
}

impl<'a, T> DoubleBuffer<'a, T> {

    fn new(slice: &'a mut [T]) -> DoubleBuffer<'a, T> {
        let mut aux = Vec::with_capacity(slice.len());
        let read_buf = slice.as_ptr();
        let write_buf = aux.as_mut_ptr();
        DoubleBuffer {
            // Hold on to the &mut slice to make sure it outlives the pointer
            // and to prevent writes from the outside
            slice,
            // Hold on to the Vec to make sure it outlives the pointer
            _aux: aux,
            read_buf,
            write_buf,
        }
    }
    
    /// Returns a ref to an element from the read buffer. 
    /// 
    /// Caller must ensure that `index` is in (0..len).
    #[inline(always)]
    unsafe fn read(&self, index: usize) -> &T {
        &*self.read_buf.add(index)
    }
    
    /// Copies the referenced element into the write buffer.
    /// 
    /// Caller must ensure that `index` is in (0..len).
    #[inline(always)]
    unsafe fn write(&self, index: usize, t: &T) {
        self.write_buf
            .add(index)
            .copy_from_nonoverlapping(t as *const T, 1);
    }

    /// Swaps the read and write buffers.
    /// 
    /// Caller must ensure that the write buffer is consistent before calling
    /// this function.
    unsafe fn swap(&mut self) {
        // The cast is ok, we have an exclusive access to both buffers
        // (&mut [T] and Vec<T>). The user guarantees that the write buffer is
        // consistent and therefore it's safe to read from it and use it as a
        // read buffer.
        let temp = self.write_buf as *const T;
        self.write_buf = self.read_buf as *mut T;
        self.read_buf = temp;
    }
}

impl<'a, T> Drop for DoubleBuffer<'a, T> {
    fn drop(&mut self) {
        let input_slice_is_write = self.write_buf as *const T == self.slice.as_ptr();
        if input_slice_is_write {
            // Input slice is the write buffer, copy the consistent state from the read buffer
            unsafe {
                // This is safe, `read_buf` is always consistent and the length is the same.
                self.write_buf.copy_from_nonoverlapping(self.read_buf, self.slice.len());
                self.swap();
            }
        }
    }
}
