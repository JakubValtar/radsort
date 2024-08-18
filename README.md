# radsort

[![Crates.io](https://img.shields.io/crates/v/radsort.svg)](https://crates.io/crates/radsort)
[![Docs](https://docs.rs/radsort/badge.svg)](https://docs.rs/radsort)

`radsort` is a radix sort implementation for sorting by scalar keys
(integers, floats, chars, bools).

All built-in scalar types can be used as sorting keys: Booleans, characters,
integers, and floating point-numbers. To sort by multiple keys, put them in
a tuple, starting from the most significant key. See [`Key`] for a full list
of supported keys.

- best and worst-case running time is `O(n)` – see [benchmarks] for more
detailed performance characteristics
- space complexity is `O(n)` – allocates temporary storage the
size of the slice, for indirect sort see [`sort_by_cached_key`]
- stable, i.e. does not reorder equal elements
- uses `#![no_std]`, but needs an allocator

This sort can be several times faster than `slice::sort` and
`slice::sort_unstable`, typically on large slices (hundreds of elements or
more). It performs worse on short slices and when using wide keys
(16 bytes). See [benchmarks] to get a better picture of the performance
characteristics.

`radsort` is an implementation of LSB radix sort, using counting sort to
sort the slice by each digit (byte) of the key. As an optimization, the
slice is sorted only by digits which differ between the keys. See the
[`unopt`] module for more details and functions which don't use this
optimization.

This implementation is based on radix sort by Pierre Terdiman,
published at
[http://codercorner.com/RadixSortRevisited.htm](http://codercorner.com/RadixSortRevisited.htm),
with select optimizations published by Michael Herf at
[http://stereopsis.com/radix.html](http://stereopsis.com/radix.html).

## Floating-point numbers

Floating-point number keys are effectively sorted according to their partial
order (see [`PartialOrd`]), with `NaN` values at the beginning (before the
negative infinity) and at the end (after the positive infinity), depending
on the sign bit of each `NaN`.

## Examples

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

To sort by two or more keys, put them in a tuple, starting with the most
significant key:
```rust
struct Height { feet: u8, inches: u8, }

let mut heights = [
    Height { feet: 6, inches: 1 },
    Height { feet: 5, inches: 9 },
    Height { feet: 6, inches: 0 },
];

// sort by feet, if feet are equal, sort by inches
radsort::sort_by_key(&mut heights, |h| (h.feet, h.inches));

assert_eq!(heights, [
    Height { feet: 5, inches: 9 },
    Height { feet: 6, inches: 0 },
    Height { feet: 6, inches: 1 },
]);
```

[`Key`]: https://docs.rs/radsort/latest/radsort/trait.Key.html
[`unopt`]: https://docs.rs/radsort/latest/radsort/unopt/index.html
[benchmarks]: https://github.com/JakubValtar/radsort/wiki/Benchmarks
[`sort_by_cached_key`]: https://docs.rs/radsort/latest/radsort/fn.sort_by_cached_key.html
[`PartialOrd`]: https://doc.rust-lang.org/std/cmp/trait.PartialOrd.html
