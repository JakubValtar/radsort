//! `radsort` is a radix sort implementation for sorting by scalar keys
//! (integers, floats, chars, bools).
//!
//! All built-in scalar types can be used as sorting keys: Booleans, characters,
//! integers, and floating point-numbers. To sort by multiple keys, either
//! combine them into a single key, or run the sort for each key, starting from
//! the least significant key. See [`Key`] for a full list of supported keys.
//!
//! - best and worst-case running time is `O(n)` – see [benchmarks] for more
//! detailed performance characteristics
//! - space complexity is `O(n)` – direct sort allocates temporary storage the
//! size of the slice, for indirect see [`sort_by_cached_key`]
//! - stable, i.e. does not reorder equal elements
//! - uses `#![no_std]`, but needs an allocator
//!
//! This sort can be several times faster than `slice::sort` and
//! `slice::sort_unstable`, typically on large slices (hundreds of elements or
//! more). It performs worse on short slices and when using wide keys
//! (16 bytes). See [benchmarks] to get a better picture of the performance
//! characteristics.
//!
//! `radsort` is an implementation of LSB radix sort, using counting sort to
//! sort the slice by each digit (byte) of the key. As an optimization, the
//! slice is sorted only by digits which differ between the keys. See the
//! [`unopt`] module for more details and functions which don't use this
//! optimization.
//!
//! This implementation is based on radix sort by Pierre Terdiman,
//! published at
//! [http://codercorner.com/RadixSortRevisited.htm](http://codercorner.com/RadixSortRevisited.htm),
//! with select optimizations published by Michael Herf at
//! [http://stereopsis.com/radix.html](http://stereopsis.com/radix.html).
//!
//! # Floating-point numbers
//!
//! Floating-point number keys are effectively sorted according to their partial
//! order (see [`PartialOrd`]), with `NaN` values at the beginning (before the
//! negative infinity) and at the end (after the positive infinity), depending
//! on the sign bit of each `NaN`.
//!
//! # Examples
//!
//! Slices of scalar types (integers, floating-point numbers, Booleans, and
//! characters) can be sorted directly:
//! ```rust
//! let mut data = [2i32, -1, 1, 0, -2];
//!
//! radsort::sort(&mut data);
//!
//! assert_eq!(data, [-2, -1, 0, 1, 2]);
//! ```
//!
//! Use a key extraction function to sort other types:
//! ```rust
//! let mut friends = ["Punchy", "Isabelle", "Sly", "Puddles", "Gladys"];
//!
//! // sort by the length of the string in bytes
//! radsort::sort_by_key(&mut friends, |s| s.len());
//!
//! assert_eq!(friends, ["Sly", "Punchy", "Gladys", "Puddles", "Isabelle"]);
//! ```
//!
//! To sort by two or more keys, either combine them into a single scalar key,
//! or run the sort for each key, starting from the least significant (this
//! works for any stable sort):
//! ```rust
//! # #[derive(Debug, PartialEq)]
//! struct Height { feet: u8, inches: u8, }
//!
//! let mut heights = [
//!     Height { feet: 6, inches: 1 },
//!     Height { feet: 5, inches: 9 },
//!     Height { feet: 6, inches: 0 },
//! ];
//!
//! // Sort per key, starting from the least significant
//! radsort::sort_by_key(&mut heights, |h| h.inches);
//! radsort::sort_by_key(&mut heights, |h| h.feet);
//!
//! assert_eq!(heights, [
//!     Height { feet: 5, inches: 9 },
//!     Height { feet: 6, inches: 0 },
//!     Height { feet: 6, inches: 1 },
//! ]);
//! ```
//!
//! [`Key`]: ./trait.Key.html
//! [`fixed_work`]: ./unopt/index.html
//! [benchmarks]: https://github.com/JakubValtar/radsort/wiki/Benchmarks
//! [`sort_by_cached_key`]: ./fn.sort_by_cached_key.html
//! [`PartialOrd`]: https://doc.rust-lang.org/std/cmp/trait.PartialOrd.html

#![no_std]

extern crate alloc;

use alloc::vec::Vec;

mod double_buffer;
mod radix_key;
mod sort;

use crate::radix_key::RadixKey;
use crate::sort::Profile;

/// Sorts the slice.
///
/// Slice elements can be any scalar type. See [`Key`] for a full list.
///
/// This sort is stable (i.e., does not reorder equal elements) and `O(w n)`,
/// where `w` is the size of the key in bytes.
///
/// Allocates temporary storage the size of the slice.
///
/// # Examples
/// ```rust
/// let mut data = [5i32, -1, 3, 15, -42];
///
/// radsort::sort(&mut data);
///
/// assert_eq!(data, [-42, -1, 3, 5, 15]);
/// ```
/// [`Key`]: trait.Key.html
pub fn sort<T: Key>(slice: &mut [T]) {
    Key::sort_by_key(slice, |v| *v, Profile::Fastest);
}

/// Sorts the slice using a key extraction function.
///
/// Key can be any scalar type. See [`Key`] for a full list.
///
/// This sort is stable (i.e., does not reorder equal elements) and `O(w m n)`,
/// where the key function is `O(m)` and `w` is the size of the key in bytes.
///
/// Allocates temporary storage the size of the slice.
///
/// See [`sort_by_cached_key`] if you use expensive key function or if you need
/// to sort large elements.
///
/// # Panics
///
/// Can panic if the key function returns different keys for the same element
/// when called repeatedly. The panic is on a best-effort basis. In case of
/// panic, the order of elements in the slice is not specified.
///
/// # Examples
///
/// ```rust
/// let mut friends = ["Punchy", "Isabelle", "Sly", "Puddles", "Gladys"];
///
/// // sort by the length of the string in bytes
/// radsort::sort_by_key(&mut friends, |s| s.len());
///
/// assert_eq!(friends, ["Sly", "Punchy", "Gladys", "Puddles", "Isabelle"]);
/// ```
///
/// [`Key`]: trait.Key.html
/// [`sort_by_cached_key`]: fn.sort_by_cached_key.html
pub fn sort_by_key<T, F, K>(slice: &mut [T], mut key_fn: F)
where
    F: FnMut(&T) -> K,
    K: Key,
{
    Key::sort_by_key(slice, |t| key_fn(t), Profile::Fastest);
}

/// Sorts the slice indirectly, using a key extraction function and caching the keys.
///
/// Key can be any scalar type. See [`Key`] for a full list.
///
/// This sort is stable (i.e., does not reorder equal elements) and
/// `O(m n + w n)`, where `w` is the size of the key, and the key function is
/// `O(m)`.
///
/// This function can be significantly faster for sorting by an expensive key
/// function or for sorting large elements.
///
/// For sorting small elements by simple key functions (e.g., functions that are
/// property accesses or basic operations), [`sort_by_key`] is likely to be
/// faster.
///
/// In the worst case, allocates a temporary storage in a `Vec<(K, usize)>`
/// twice the length of the slice.
///
/// # Examples
///
/// ```rust
/// let mut data = ["-6", "2", "15", "-1", "0"];
///
/// radsort::sort_by_cached_key(&mut data, |s| s.parse::<i32>().unwrap());
///
/// assert_eq!(data, ["-6", "-1", "0", "2", "15"]);
/// ```
///
/// [`Key`]: ./trait.Key.html
/// [`sort_by_key`]: fn.sort_by_key.html
pub fn sort_by_cached_key<T, F, K>(slice: &mut [T], key_fn: F)
where
    F: FnMut(&T) -> K,
    K: Key,
{
    sort_by_cached_key_internal(slice, key_fn, Profile::Fastest);
}

/// Functions for sorting the slice with a fixed number of operations per
/// element.
///
/// These functions do not perform optimizations based on element values, making
/// the best-case and the worst-case scenarios the same, which results in a more
/// predictable performance.
///
/// This is useful in contexts sensitive to worst-case performance and for
/// testing, as the number of operations depends only on the slice length, not
/// on the runtime values. Sorting two slices of the same type with the same
/// number of elements and using the same key type will perform the same number
/// of operations and memory accesses.
///
/// Keep in mind that even though the number of memory accesses is the same,
/// the cache and memory access order is still going to make a difference.
pub mod fixed_work {

    use super::*;

    /// Version of [`sort`](../fn.sort.html) which performs a fixed number of
    /// operations per element.
    ///
    /// See the [module documentation](./index.html) for more details.
    pub fn sort<T: Key>(slice: &mut [T]) {
        Key::sort_by_key(slice, |v| *v, Profile::FixedWorkPerElement);
    }

    /// Version of [`sort_by_key`](../fn.sort_by_key.html) which performs a
    /// fixed number of operations per element.
    ///
    /// See the [module documentation](./index.html) for more details.
    pub fn sort_by_key<T, F, K>(slice: &mut [T], mut key_fn: F)
    where
        F: FnMut(&T) -> K,
        K: Key,
    {
        Key::sort_by_key(slice, |t| key_fn(t), Profile::FixedWorkPerElement);
    }

    /// Version of [`sort_by_cached_key`](../fn.sort_by_cached_key.html) which
    /// performs a fixed number of operations per element.
    ///
    /// See the [module documentation](./index.html) for more details.
    pub fn sort_by_cached_key<T, F, K>(slice: &mut [T], key_fn: F)
    where
        F: FnMut(&T) -> K,
        K: Key,
    {
        sort_by_cached_key_internal(slice, key_fn, Profile::FixedWorkPerElement);
    }
}

fn sort_by_cached_key_internal<T, F, K>(slice: &mut [T], mut key_fn: F, profile: Profile)
where
    F: FnMut(&T) -> K,
    K: Key,
{
    // Adapted from std::slice::sort_by_cached_key

    macro_rules! radsort_by_cached_key {
        ($index:ty) => {{
            let mut indices: Vec<(K, $index)> = slice
                .iter()
                .map(|t| key_fn(t))
                .enumerate()
                .map(|(i, k)| (k, i as $index))
                .collect();

            Key::sort_by_key(&mut indices, |(k, _)| *k, profile);

            for i in 0..slice.len() {
                let mut index = indices[i].1;
                while (index as usize) < i {
                    // The previous value was swapped somewhere else. The index to which
                    // the original value was swapped was marked into the index array.
                    // Follow the indices to find out where the original value ended up.
                    index = indices[index as usize].1;
                }
                // Mark down the index to which the current value goes
                indices[i].1 = index;
                slice.swap(i, index as usize);
            }
        }};
    }

    match slice.len() {
        len if len < 2 => (),
        len if len <= core::u8::MAX as usize + 1 => {
            radsort_by_cached_key!(u8);
        }
        #[cfg(not(target_pointer_width = "16"))]
        len if len <= core::u16::MAX as usize + 1 => {
            radsort_by_cached_key!(u16);
        }
        #[cfg(not(any(target_pointer_width = "16", target_pointer_width = "32")))]
        len if len <= core::u32::MAX as usize + 1 => {
            radsort_by_cached_key!(u32);
        }
        #[cfg(not(any(
            target_pointer_width = "16",
            target_pointer_width = "32",
            target_pointer_width = "64"
        )))]
        len if len <= core::u64::MAX as usize + 1 => {
            radsort_by_cached_key!(u64);
        }
        _ => {
            radsort_by_cached_key!(usize);
        }
    }
}

/// Types which can be used as sorting keys.
///
/// Implemented for all scalar types and their tuples.
///
/// Slices of types for which `Key` is implemented can be sorted directly using
/// [`sort`]. Slices of other types can be sorted using [`sort_by_key`] with a
/// key extraction function.
///
/// [`sort`]: fn.sort.html
/// [`sort_by_key`]: fn.sort_by_key.html
pub trait Key: Copy + private::Sealed {
    /// Sorts the slice using `Self` as the type of the key.
    ///
    /// You shouldn't need to call this directly, use one of the functions in
    /// the [crate root](index.html#functions) instead.
    #[doc(hidden)]
    fn sort_by_key<T, F>(slice: &mut [T], key_fn: F, profile: Profile)
    where
        F: FnMut(&T) -> Self;
}

macro_rules! impl_for_scalar { ($($t:ty)*) => ($(
    impl Key for $t {
        #[doc(hidden)]
        fn sort_by_key<T, F>(slice: &mut [T], mut key_fn: F, profile: Profile)
            where F: FnMut(&T) -> Self
        {
            sort::dispatch_sort(slice, |t| RadixKey::from(key_fn(t)), profile);
        }
    }
)*) }

impl_for_scalar! {
    bool char
    u8 u16 u32 u64 u128 usize
    i8 i16 i32 i64 i128 isize
    f32 f64
}

mod private {
    /// This trait serves as a seal for the `Key` trait to prevent downstream
    /// implementations.
    pub trait Sealed {}
    macro_rules! sealed_impl { ($($t:ty)*) => ($(
        impl Sealed for $t {}
    )*) }
    sealed_impl! {
        ()
        bool char
        u8 u16 u32 u64 u128 usize
        i8 i16 i32 i64 i128 isize
        f32 f64
    }
}
