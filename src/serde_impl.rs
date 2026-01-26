//! [`serde::Serialize`] and [`serde::Deserialize`] implementations.
use super::*;
use core::marker::PhantomData;
use serde::Deserializer;
use serde::de::*;
use serde::ser::*;
/// Generates implementations of [`serde::Serialize`] and [`serde::Deserialize`].
macro_rules! mask_tracked_array_serde_impl {
    () => {};
    (($ty:ty, $alias_ident:ident), $($rest:tt)*) => {
        mask_tracked_array_serde_impl!(($ty, $alias_ident));
        mask_tracked_array_serde_impl!($($rest)*);
    };
    (($ty:ty, $alias_ident:ident)) => {
        impl<T: serde::Serialize> serde::Serialize for $alias_ident<T> {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                let mut state = serializer.serialize_map(Some(self.len() as usize + 1usize))?;
                state.serialize_entry(&"mask", &self.mask)?;
                for (index, value) in self.iter_filled_indices().zip(self.iter()) {
                    state.serialize_entry(&index, &value)?;
                }
                state.end()
            }
        }
        paste::paste! {
            struct [<$alias_ident Visitor>]<T>(PhantomData<T>);
            impl<'de, T: serde::Deserialize<'de>> Visitor<'de> for [<$alias_ident Visitor>]<T> {
                type Value = $alias_ident<T>;
                fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                    formatter.write_str(stringify!($alias_ident))
                }
                fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error>
                where
                    M: MapAccess<'de>,
                {
                    let array = $alias_ident::new();
                    let ("mask", expected_mask): (&str, $ty) = access.next_entry()?.ok_or_else(|| serde::de::Error::invalid_length(0, &"Mask"))?
                    else {
                        return Err(serde::de::Error::invalid_value(Unexpected::Other("Wrong first key"), &"mask key"));
                    };
                    while let Some((key, value)) = access.next_entry()? {
                        if let Some(_) = array.insert(key, value) {
                            // if no_insert exists there must have been something
                            // wrong
                            return Err(serde::de::Error::invalid_value(Unexpected::Other("uninsertable key"), &"Correct key"));
                        }
                    }
                    if expected_mask != array.mask.get() {
                        return Err(serde::de::Error::invalid_value(Unexpected::Other("Invalid mask"), &"Valid mask"));
                    }
                    Ok(array)
                }
            }
            impl<'de, T: serde::Deserialize<'de>> serde::Deserialize<'de> for $alias_ident<T> {
                fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
                where
                    D: Deserializer<'de>,
                {
                    deserializer.deserialize_map([<$alias_ident Visitor>](PhantomData))
                }
            }
            #[cfg(test)]
            mod [<$ty _serde_tests>] {
                use super::*;
                #[test]
                fn empty() {
                    let empty: $alias_ident<u8> = $alias_ident::new();
                    let serialised = postcard::to_vec::<_, 1000>(&empty).unwrap();
                    let deserialised: $alias_ident<u8> = postcard::from_bytes(&serialised).unwrap();
                    assert_eq!(empty, deserialised);
                }
                #[test]
                fn order() {
                    let original: $alias_ident<u8> = $alias_ident::new();
                    assert!(original.insert(1, 1).is_none());
                    assert!(original.insert(3, 3).is_none());
                    assert!(original.insert(2, 2).is_none());
                    let serialised = postcard::to_vec::<_, 1000>(&original).unwrap();
                    let deserialised: $alias_ident<u8> = postcard::from_bytes(&serialised).unwrap();
                    assert_eq!(original, deserialised);
                }
                #[test]
                fn bad_serialisation_input() {
                    let bad = [0, 1, 2, 3, 4, 5, 6, 8];
                    let deserialisation_attempt: Result<$alias_ident<u8>, _> = postcard::from_bytes(&bad);
                    assert!(deserialisation_attempt.is_err());
                }
            }
        }
    };
}
mask_tracked_array_serde_impl!(
    (u8, MaskTrackedArrayU8),
    (u16, MaskTrackedArrayU16),
    (u32, MaskTrackedArrayU32),
    (u64, MaskTrackedArrayU64),
    (u128, MaskTrackedArrayU128)
);
