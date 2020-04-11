//! `radsort` is a radix sort implementation for sorting by scalar keys
//! (integers, floats, chars, bools).
//! 
//! All built-in scalar types can be used as sorting keys: Booleans, characters,
//! integers, and floating point-numbers. To sort by multiple keys, put them in
//! a tuple, starting from the most significant key. See [`Key`] for a full list
//! of supported keys.
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
//! To sort by two or more keys, put them in a tuple, starting with the most
//! significant key:
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
//! // sort by feet, if feet are equal, sort by inches
//! radsort::sort_by_key(&mut heights, |h| (h.feet, h.inches));
//! 
//! assert_eq!(heights, [
//!     Height { feet: 5, inches: 9 },
//!     Height { feet: 6, inches: 0 },
//!     Height { feet: 6, inches: 1 },
//! ]);
//! ```
//! 
//! [`Key`]: ./trait.Key.html
//! [`unopt`]: ./unopt/index.html
//! [benchmarks]: https://github.com/JakubValtar/radsort/wiki/Benchmarks
//! [`sort_by_cached_key`]: ./fn.sort_by_cached_key.html
//! [`PartialOrd`]: https://doc.rust-lang.org/std/cmp/trait.PartialOrd.html

#![warn(clippy::all)]

#![no_std]

extern crate alloc;

use alloc::vec::Vec;

mod scalar;
mod sort;

use scalar::Scalar;
use sort::RadixKey;

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
#[inline]
pub fn sort<T: Key>(slice: &mut [T]) {
    Key::sort_by_key(slice, |v| *v, false);
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
#[inline]
pub fn sort_by_key<T, F, K>(slice: &mut [T], mut key_fn: F)
    where F: FnMut(&T) -> K, K: Key
{
    Key::sort_by_key(slice, |t| key_fn(t), false);
}

/// Sorts the slice indirectly, using a key extraction function and caching the keys.
/// 
/// Key can be any scalar type. See [`Key`] for a full list.
/// 
/// This sort is stable (i.e., does not reorder equal elements) and
/// `O(m n + w n)`, where the key function is `O(m)`.
/// 
/// This function can be significantly faster for sorting by an expensive key
/// function or for sorting large elements. The keys are extracted, sorted, and
/// then the elements of the slice are reordered in-place. This saves CPU cycles
/// in case of an expensive key function and saves memory bandwidth in case of
/// large elements.
/// 
/// For sorting small elements by simple key functions (e.g., functions that are
/// property accesses or basic operations), [`sort_by_key`] is likely to be
/// faster.
/// 
/// In the worst case, allocates temporary storage in a `Vec<(K, usize)>` twice
/// the length of the slice.
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
#[inline]
pub fn sort_by_cached_key<T, F, K>(slice: &mut [T], key_fn: F)
    where F: FnMut(&T) -> K, K: Key
{
    sort_by_cached_key_internal(slice, key_fn, false);
}

/// Sorting functions which don't use optimizations based on the values
/// of the keys. Useful for benchmarks and consistent performance.
/// 
/// For each digit (byte) of the key, `radsort` reorders the slice once.
/// Functions in the crate root sort only by the bytes which differ between the
/// keys. This can lead to large differences in sorting time, based on the
/// values in the slice.
/// 
/// For example, sorting `u32` all less than `u8::MAX` will sort only by
/// the least significant byte and skip the three most significant bytes,
/// which are zero; this cuts the sorting time to roughly one quarter, plus
/// the overhead of analyzing the keys.
/// 
/// Unlike functions in the crate root, functions in this module don't use
/// this optimization and sort by all bytes of the key. This leads to worse but
/// more consistent performance. The effects of the CPU cache will still play a
/// role, but at least the number of executed instructions will not depend on
/// the values in the slice, only on the length of the slice and the width of
/// the key type.
pub mod unopt {

    use super::*;

    /// Version of [`sort`](../fn.sort.html) which does not skip digits (bytes).
    /// 
    /// See the [module documentation](./index.html) for more details.
    #[inline]
    pub fn sort<T: Key>(slice: &mut [T]) {
        Key::sort_by_key(slice, |v| *v, true);
    }
    
    /// Version of [`sort_by_key`](../fn.sort_by_key.html) which does not skip digits (bytes).
    /// 
    /// See the [module documentation](./index.html) for more details.
    #[inline]
    pub fn sort_by_key<T, F, K>(slice: &mut [T], mut key_fn: F)
    where F: FnMut(&T) -> K, K: Key
    {
        Key::sort_by_key(slice, |t| key_fn(t), true);
    }
    
    /// Version of [`sort_by_cached_key`](../fn.sort_by_cached_key.html) which does not skip digits (bytes).
    /// 
    /// See the [module documentation](./index.html) for more details.
    #[inline]
    pub fn sort_by_cached_key<T, F, K>(slice: &mut [T], key_fn: F)
        where F: FnMut(&T) -> K, K: Key
    {
        sort_by_cached_key_internal(slice, key_fn, true);
    }
}

#[inline]
fn sort_by_cached_key_internal<T, F, K>(slice: &mut [T], mut key_fn: F, unopt: bool)
    where F: FnMut(&T) -> K, K: Key
{
    // Adapted from std::slice::sort_by_cached_key

    macro_rules! radsort_by_cached_key {
        ($index:ty) => ({
            let mut indices: Vec<(K, $index)> = slice.iter()
                .map(|t| key_fn(t))
                .enumerate()
                .map(|(i, k)| (k, i as $index))
                .collect();

            Key::sort_by_key(&mut indices, |(k, _)| *k, unopt);

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
        })
    }

    let len = slice.len();
    if len < 2 {
        return;
    }

    let sz_u8    = core::mem::size_of::<(K, u8)>();
    let sz_u16   = core::mem::size_of::<(K, u16)>();
    let sz_u32   = core::mem::size_of::<(K, u32)>();
    let sz_usize = core::mem::size_of::<(K, usize)>();

    if sz_u8  < sz_u16   && len <= (core:: u8::MAX as usize + 1) { return radsort_by_cached_key!( u8) }
    if sz_u16 < sz_u32   && len <= (core::u16::MAX as usize + 1) { return radsort_by_cached_key!(u16) }
    if sz_u32 < sz_usize && len <= (core::u32::MAX as usize + 1) { return radsort_by_cached_key!(u32) }

    radsort_by_cached_key!(usize)
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
    // If this crate didn't support tuples, this trait wouldn't be needed and
    // Scalar could be exposed directly to users as the `Key` trait.

    /// Sorts the slice using `Self` as the type of the key.
    /// 
    /// You shouldn't need to call this directly, use one of the functions in
    /// the [crate root](index.html#functions) instead.
    #[doc(hidden)]
    fn sort_by_key<T, F>(slice: &mut [T], key_fn: F, unopt: bool)
        where F: FnMut(&T) -> Self;
}

macro_rules! impl_for_scalar { ($($t:ty)*) => ($(
    impl Key for $t {
        #[doc(hidden)]
        #[inline]
        fn sort_by_key<T, F>(slice: &mut [T], mut key_fn: F, unopt: bool)
            where F: FnMut(&T) -> Self
        {
            RadixKey::radix_sort(slice, |t| key_fn(t).to_radix_key(), unopt);
        }
    }
)*) }

impl_for_scalar! {
    bool char
    u8 u16 u32 u64 u128 usize
    i8 i16 i32 i64 i128 isize
    f32 f64
}

impl<A: Key> Key for (A,) {
    #[doc(hidden)]
    #[inline]
    fn sort_by_key<T, F>(slice: &mut [T], mut key_fn: F, unopt: bool)
        where F: FnMut(&T) -> Self
    {
        A::sort_by_key(slice, |t| key_fn(t).0, unopt);
    }
}

impl<A: Key, B: Key> Key for (A, B) {
    #[doc(hidden)]
    #[inline]
    fn sort_by_key<T, F>(slice: &mut [T], mut key_fn: F, unopt: bool)
        where F: FnMut(&T) -> Self
    {
        B::sort_by_key(slice, |t| key_fn(t).1, unopt);
        A::sort_by_key(slice, |t| key_fn(t).0, unopt);
    }
}

impl<A: Key, B: Key, C: Key> Key for (A, B, C) {
    #[doc(hidden)]
    #[inline]
    fn sort_by_key<T, F>(slice: &mut [T], mut key_fn: F, unopt: bool)
        where F: FnMut(&T) -> Self
    {
        C::sort_by_key(slice, |t| key_fn(t).2, unopt);
        B::sort_by_key(slice, |t| key_fn(t).1, unopt);
        A::sort_by_key(slice, |t| key_fn(t).0, unopt);
    }
}

impl<A: Key, B: Key, C: Key, D: Key> Key for (A, B, C, D) {
    #[doc(hidden)]
    #[inline]
    fn sort_by_key<T, F>(slice: &mut [T], mut key_fn: F, unopt: bool)
        where F: FnMut(&T) -> Self
    {
        D::sort_by_key(slice, |t| key_fn(t).3, unopt);
        C::sort_by_key(slice, |t| key_fn(t).2, unopt);
        B::sort_by_key(slice, |t| key_fn(t).1, unopt);
        A::sort_by_key(slice, |t| key_fn(t).0, unopt);
    }
}

mod private {
    use super::*;
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
    impl<A: Key> Sealed for (A,) {}
    impl<A: Key, B: Key> Sealed for (A, B) {}
    impl<A: Key, B: Key, C: Key> Sealed for (A, B, C) {}
    impl<A: Key, B: Key, C: Key, D: Key> Sealed for (A, B, C, D) {}
}
