# Bitmask backed array of slots
This library provides a bitmask backed array where the mask is used
to track which slots in the array are filled. This library also supports `serde`
serialisation using the `serde` feature flag.

This is very similar to an array of `Option`s, but the discriminant bits
are crammed together in a bitmask to save space and be a little bit performant.

This library is quite similar to https://github.com/BastiDood/option-block.
Here are a few differences:
-   This library has an `UnsafeCell` for each entry, so you can access each one
    independently when using `unsafe` to build data structures.
-   This library has a `MaskTrackedArray` trait which allows you to write
    generic data structures for different sizes.
-   This library does not have const functions due to traits not supporting them.
    `option-block` has support for const functions.
-   This library provides support for `serde` using the `serde` feature flag.
-   `option-block` provides some more methods for ergonomics compared to this
    library
-   This library uses the same `MaskTrackedArrayBase` type for all variants.
    This could be useful for doing generics over different sizes.

See the docs.rs page for more details.

# Example
```rust
let mut mask_tracked_array = MaskTrackedArrayU8::new();
mask_tracked_array.insert(0, 2);
mask_tracked_array.insert(1, 3);
assert_eq!(2, mask_tracked_array.remove(0));
assert_eq!(3, *mask_tracked_array.get_ref(1))
```