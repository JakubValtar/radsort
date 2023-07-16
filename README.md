# radsort

[![Crates.io](https://img.shields.io/crates/v/radsort.svg)](https://crates.io/crates/radsort)
[![Docs](https://docs.rs/radsort/badge.svg)](https://docs.rs/radsort)

Radsort is a stable LSB radix sort with `O(w⋅n)` worst-case time complexity,
`O(w)` stack space and `O(n)` heap space requirements, where `w` is the key
size in bytes and `n` is the number of elements to be sorted.
For a list of supported sorting keys, see the [`Key`] trait. It is implemented for:
- integers, chars, bools: ordering equivalent to their `Ord` implementation,
- floats: ordering equivalent to [`total_cmp`] ordering.
Supports `no-std` with `alloc`.
This sort can be several times faster than `slice::sort` and
`slice::sort_unstable`, typically on large slices (hundreds of elements or
more). It performs worse on short slices and when using wide keys
(16 bytes). See [benchmarks] to get a better picture of the performance
characteristics.
If you value consistency over speed, see the [`fixed_work`] module. It
contains sorting functions that perform a fixed number of operations per
element. This is useful for testing the worst-case scenario, or when you
don't want the values of the sorted elements to affect the performance.
This implementation is based on radix sort by
[Pierre Terdiman](http://codercorner.com/RadixSortRevisited.htm),
with select optimizations published by
[Michael Herf](http://stereopsis.com/radix.html).
# Examples
Slices of scalar types (integers, floating-point numbers, Booleans, and
characters) can be sorted directly:
```rust
let mut data = [2i32, -1, 1, 0, -2];

radsort::sort(&mut data);

assert_eq!(data, [-2, -1, 0, 1, 2]);
```

Use a key extraction function to sort other types:
```rust
let mut friends = ["Punchy", "Isabelle", "Sly", "Puddles", "Gladys"];

// sort by the length of the string in bytes
radsort::sort_by_key(&mut friends, |s| s.len());

assert_eq!(friends, ["Sly", "Punchy", "Gladys", "Puddles", "Isabelle"]);
```

To sort by two or more keys, either combine them into a single scalar key,
or run the sort for each key, starting from the least significant (this
works for any stable sort):
```rust
struct Height { feet: u8, inches: u8, }

let mut heights = [
    Height { feet: 6, inches: 1 },
    Height { feet: 5, inches: 9 },
    Height { feet: 6, inches: 0 },
];

// Sort per key, starting from the least significant
radsort::sort_by_key(&mut heights, |h| h.inches);
radsort::sort_by_key(&mut heights, |h| h.feet);

assert_eq!(heights, [
    Height { feet: 5, inches: 9 },
    Height { feet: 6, inches: 0 },
    Height { feet: 6, inches: 1 },
]);
```

[`Key`]: https://docs.rs/radsort/latest/radsort/trait.Key.html
[`Ord`]: https://doc.rust-lang.org/std/cmp/trait.Ord.html
[`total_cmp`]: https://doc.rust-lang.org/std/primitive.f64.html#method.total_cmp
[`fixed_work`]: https://docs.rs/radsort/latest/radsort/fixed_work/index.html
[benchmarks]: https://github.com/JakubValtar/radsort/wiki/Benchmarks
