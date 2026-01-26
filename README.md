# MaskTrackedArray
This library provides a bitmask backed array where the mask is used
to track which slots in the array are filled. This library also supports `serde`
serialisation using the `serde` feature flag.

See the docs.rs page for more details.

# Example
```rust
let mut mask_tracked_array = MaskTrackedArrayU8::new();
mask_tracked_array.insert(0, 2);
mask_tracked_array.insert(1, 3);
assert_eq!(2, mask_tracked_array.remove(0));
assert_eq!(3, *mask_tracked_array.get_ref(1))
```