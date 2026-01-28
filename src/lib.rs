#![no_std]
#![warn(missing_docs)]
//! A no std and no alloc abstraction for some data structures on
//! microcontrollers. A [`MaskTrackedArray`] is a
//! [`UnsafeCell<MaybeUninit<T>>`] with a number mask for tracking which slots
//! are filled and which aren't. The arrays are allocated at compile time using
//! generics and as such come in different sizes based on the number types.
//!
//! You can think of a [`MaskTrackedArray`] as an array of numbered slots which
//! can be accessed independently (unsafe code may be required).
//!
//! The current implementations supplied by this crate are
//! - [`MaskTrackedArrayU8`]
//! - [`MaskTrackedArrayU16`]
//! - [`MaskTrackedArrayU32`]
//! - [`MaskTrackedArrayU64`]
//! - [`MaskTrackedArrayU128`]
//!
//! See the documentation on [`MaskTrackedArray`] to see what methods are
//! available.
use core::{cell::UnsafeCell, mem::MaybeUninit};

use bit_iter::BitIter;

#[cfg(feature = "serde")]
#[doc(hidden)]
pub mod serde_impl;

/// Implemented by every variant of the mask tracked array. The
/// [`MaskTrackedArray::MaskType`] is the number type used for the mask with
/// [`MaskTrackedArray::MAX_COUNT`] being the size of the slots array.
pub trait MaskTrackedArray<T>: Default {
    /// The number type used as the mask.
    #[cfg(not(feature = "num_traits"))]
    type MaskType;
    /// The number type used as the mask.
    #[cfg(feature = "num_traits")]
    type MaskType: num_traits::PrimInt;
    /// The maximum number of elements in the array. Note that this is based
    /// on the number of bits in [`MaskTrackedArray::MaskType`].
    const MAX_COUNT: usize;
    /// Check if there is an item at a slot. This function will also return
    /// false if the index is out of range.
    fn contains_item_at(&self, index: usize) -> bool;
    /// Check how many slots are occupied.
    fn len(&self) -> u32;
    /// Returns true if this array is completely empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Construct a new empty instance of this array.
    #[must_use]
    fn new() -> Self {
        Self::default()
    }
    /// Clear out all items in this array, returning to its empty state. Drop
    /// is called if needed.
    fn clear(&mut self);
    /// Get a reference to an item inside a slot if available.
    fn get_ref(&self, index: usize) -> Option<&T> {
        if self.contains_item_at(index) {
            Some(unsafe { self.get_unchecked_ref(index) })
        } else {
            None
        }
    }
    /// Get a mutable reference to an item inside a slot if available.
    fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if self.contains_item_at(index) {
            Some(unsafe { self.get_unchecked_mut(index) })
        } else {
            None
        }
    }
    /// Get an immutable reference to slot without bounds or validity checking.
    /// # Safety
    /// The given index must be valid.
    unsafe fn get_unchecked_ref(&self, index: usize) -> &T;
    /// Get a mutable reference to a slot without bounds, validity or borrow
    /// checking.
    /// # Safety
    /// The given index must be valid and there must be no other references
    /// to the same slot.
    #[allow(clippy::mut_from_ref)]
    unsafe fn get_unchecked_mut(&self, index: usize) -> &mut T;
    /// Insert an item at a given index without bounds, validity or borrow
    /// checking.
    /// # Safety
    /// The given index must be valid to avoid undefined behaviour. If a value
    /// was already present, that value will be forgotten without running its
    /// drop implementation.
    unsafe fn insert_unchecked(&self, index: usize, value: T);
    /// Try to insert an item at a given index. If insertion fails, return
    /// the value in an option. If the option is none then the insertion
    /// succeeded.
    #[must_use]
    fn insert(&self, index: usize, value: T) -> Option<T> {
        if self.contains_item_at(index) || index >= Self::MAX_COUNT {
            Some(value)
        } else {
            unsafe { self.insert_unchecked(index, value) };
            None
        }
    }
    /// Remove a value from a slot without checking the index or if the item is
    /// there.
    /// # Safety
    /// Calling this function on currently referenced or nonexistent slots will
    /// result in undefined behaviour.
    unsafe fn remove_unchecked(&self, index: usize) -> T;
    /// Remove a value at a specific index and return it if available.
    fn remove(&mut self, index: usize) -> Option<T> {
        if self.contains_item_at(index) {
            Some(unsafe { self.remove_unchecked(index) })
        } else {
            None
        }
    }
    /// Get an iterator over all filled slot indices.
    fn iter_filled_indices(&self) -> impl Iterator<Item = usize>;
    /// Get an iterator over all filled slot indices also present in the given
    /// mask.
    fn iter_filled_indices_mask(&self, mask: Self::MaskType) -> impl Iterator<Item = usize>;
    /// Get an iterator over all unfilled slot indices.
    fn iter_empty_indices(&self) -> impl Iterator<Item = usize>;
    /// Iterate over references to every filled slot.
    fn iter<'a>(&'a self) -> impl Iterator<Item = &'a T>
    where
        T: 'a {
            self.iter_filled_indices().map(|index| unsafe { self.get_unchecked_ref(index)})
        }
    /// Iterate over mutable references to every filled slot.
    fn iter_mut<'a>(&'a mut self) -> impl Iterator<Item = &'a mut T>
    where
        T: 'a {
            self.iter_filled_indices().map(|index| unsafe { self.get_unchecked_mut(index)})
        }
    /// Iterate over references which are only present in the given mask.
    fn iter_mask<'a>(&'a self, mask: Self::MaskType) -> impl Iterator<Item = &'a T>
    where
        T: 'a {
            self.iter_filled_indices_mask(mask).map(|index| unsafe { self.get_unchecked_ref(index)})
        }
    /// Iterate over mutable references which are only present in the given
    /// mask.
    fn iter_mut_mask<'a>(&'a mut self, mask: Self::MaskType) -> impl Iterator<Item = &'a mut T>
    where
        T: 'a {
            self.iter_filled_indices_mask(mask).map(|index| unsafe { self.get_unchecked_mut(index)})
        }
    /// Get the internal mask used.
    fn mask(&self) -> Self::MaskType;
}

/// An array with slots for values backed by a mask for tracking which slots
/// are under use. Each slot has their own [`UnsafeCell`].
pub struct MaskTrackedArrayBase<T, M, const N: usize>
where
    Self: MaskTrackedArray<T, MaskType = M>,
{
    /// Mask used for tracking which slots in the array are filled.
    mask: core::cell::Cell<M>,
    /// An array of fillable slots.
    array: [UnsafeCell<MaybeUninit<T>>; N],
}

/// An iterator for [`MaskTrackedArray`] variants.
pub struct MaskTrackedArrayIter<T, M, const N: usize>
where
    MaskTrackedArrayBase<T, M, N>: MaskTrackedArray<T, MaskType = M>,
{
    bit_iterator: BitIter<M>,
    source: MaskTrackedArrayBase<T, M, N>,
}

impl<T, M, const N: usize> Drop for MaskTrackedArrayBase<T, M, N>
where
    Self: MaskTrackedArray<T, MaskType = M>,
{
    fn drop(&mut self) {
        self.clear();
    }
}
macro_rules! mask_tracked_array_impl {
    () => {};
    (($num_ty:ty, $bits:expr, $alias_ident:ident), $($rest:tt)*) => {
        mask_tracked_array_impl!(($num_ty, $bits, $alias_ident));
        mask_tracked_array_impl!($($rest)*);
    };
    (($num_ty:ty, $bits:expr, $alias_ident:ident)) => {
        #[doc = stringify!(A $num_ty tracked array which can hold $bits items) ]
        pub type $alias_ident<T> = MaskTrackedArrayBase<T, $num_ty, $bits>;
        impl<T> MaskTrackedArray<T> for MaskTrackedArrayBase<T, $num_ty, $bits> {
            type MaskType = $num_ty;
            const MAX_COUNT: usize = $bits;
            fn contains_item_at(&self, index: usize) -> bool {
                if index >= $bits {
                    return false;
                }
                self.mask.get() & (1 << index) != 0
            }
            fn mask(&self) -> Self::MaskType {
                self.mask.get()
            }
            fn len(&self) -> u32 {
                self.mask.get().count_ones()
            }
            unsafe fn get_unchecked_ref(&self, index: usize) -> &T {
                unsafe { (&*self.array.get_unchecked(index).get()).assume_init_ref() }
            }
            unsafe fn get_unchecked_mut(&self, index: usize) -> &mut T {
                unsafe { (&mut *self.array.get_unchecked(index).get()).assume_init_mut() }
            }
            fn clear(&mut self) {
                if core::mem::needs_drop::<T>() {
                    for index in bit_iter::BitIter::from(self.mask.get()) {
                        unsafe {
                            self.array
                                .get_unchecked_mut(index)
                                .get_mut()
                                .assume_init_drop()
                        };
                    }
                }
                self.mask.set(0);
            }
            unsafe fn insert_unchecked(&self, index: usize, value: T) {
                unsafe { (&mut *self.array.get_unchecked(index).get()).write(value)};
                self.mask.update(|v| v | (1 << index));
            }
            unsafe fn remove_unchecked(&self, index: usize) -> T {
                self.mask.update(|v| v & !(1 << index));
                let mut empty = core::mem::MaybeUninit::uninit();
                unsafe {
                    let mut_ref = (&mut *self.array.get_unchecked(index).get());
                    core::mem::swap(&mut empty, mut_ref);
                    empty.assume_init()
                }
            }
            #[inline]
            fn iter_filled_indices(&self) -> impl Iterator<Item = usize> {
                BitIter::from(self.mask.get())
            }
            #[inline]
            fn iter_filled_indices_mask(&self, mask: Self::MaskType) -> impl Iterator<Item = usize> {
                BitIter::from(self.mask.get() & mask)
            }
            #[inline]
            fn iter_empty_indices(&self) -> impl Iterator<Item = usize> {
                BitIter::from(!self.mask.get())
            }
        }
        impl<T> Default for MaskTrackedArrayBase<T, $num_ty, $bits> {
            fn default() -> Self {
                Self {
                    mask: core::cell::Cell::new(0),
                    array: [const {core::cell::UnsafeCell::new(core::mem::MaybeUninit::uninit())}; $bits]
                }
            }
        }
        impl<T> core::iter::Iterator for MaskTrackedArrayIter<T, $num_ty, $bits> {
            type Item = T;
            fn next(&mut self) -> Option<Self::Item> {
                let next_index = self.bit_iterator.next()?;
                Some( unsafe { self.source.remove_unchecked(next_index) } )
            }
        }
        impl<T> core::iter::IntoIterator for MaskTrackedArrayBase<T, $num_ty, $bits>
        {
            type Item = T;
            type IntoIter = MaskTrackedArrayIter<T, $num_ty, $bits>;
            fn into_iter(self) -> Self::IntoIter {
                let bit_iterator = BitIter::from(self.mask.get());
                MaskTrackedArrayIter {
                    source: self,
                    bit_iterator
                }
            }
        }
        impl<T> core::iter::FromIterator<T> for MaskTrackedArrayBase<T, $num_ty, $bits> {
            fn from_iter<I>(iter: I) -> Self
                where I: IntoIterator<Item = T>
            {
                let empty = Self::new();
                for (index, value) in iter.into_iter().enumerate() {
                    if index >= $bits {
                        break;
                    }
                    unsafe { empty.insert_unchecked(index, value) };
                }
                empty
            }
        }
        impl<T> core::iter::FromIterator<(usize, T)> for MaskTrackedArrayBase<T, $num_ty, $bits> {
            fn from_iter<I>(iter: I) -> Self
                where I: IntoIterator<Item = (usize, T)>
            {
                let empty = Self::new();
                for (index, value) in iter.into_iter() {
                    let _ = empty.insert(index, value);
                }
                empty
            }
        }
        impl<T: PartialEq> PartialEq for MaskTrackedArrayBase<T, $num_ty, $bits> {
            fn eq(&self, other: &Self) -> bool {
                if self.mask != other.mask {
                    return false;
                }
                self.iter().zip(other.iter()).all(|(left, right)| left.eq(right))
            }
        }
        impl<T: Eq> Eq for MaskTrackedArrayBase<T, $num_ty, $bits> {}
        impl<T: core::hash::Hash> core::hash::Hash for MaskTrackedArrayBase<T, $num_ty, $bits> {
            fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
                self.mask.get().hash(state);
                self.iter().for_each(|v| v.hash(state));
            }
        }
        impl<T: core::fmt::Debug> core::fmt::Debug for MaskTrackedArrayBase<T, $num_ty, $bits> {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                f.debug_list().entries(self.iter()).finish()?;
                Ok(())
            }
        }
        paste::paste! {
            #[cfg(test)]
            mod [<$num_ty _tests>] {
                use super::*;
                extern crate std;
                #[test]
                fn from_iterator_and_back() {
                    let mask = $alias_ident::from_iter(0..$bits);
                    for (index, number) in mask.into_iter().enumerate() {
                        assert_eq!(index, number);
                    }
                }
                #[test]
                fn from_too_big_iterator() {
                    let numbers = [0; $bits + 1];
                    let mask = $alias_ident::from_iter(numbers);
                    assert_eq!(mask.len(), $bits);
                }
                #[test]
                fn from_empty_iterator() {
                    let numbers: [u8; 0] = [];
                    let mask = $alias_ident::from_iter(numbers);
                    assert_eq!(mask.len(), 0);
                }
                #[test]
                fn hash_equality() {
                    let mask = $alias_ident::new();
                    assert!(mask.insert(0, 0).is_none());
                    assert!(mask.insert(1, 1).is_none());
                    let mask_2 = $alias_ident::new();
                    assert!(mask_2.insert(1, 1).is_none());
                    assert!(mask_2.insert(0, 0).is_none());
                    assert_eq!(mask, mask_2);
                    use std::hash::{ Hash, DefaultHasher, Hasher };
                    let mut hasher = DefaultHasher::new();
                    mask.hash(&mut hasher);
                    let first_hash = hasher.finish();
                    let mut hasher = DefaultHasher::new();
                    mask_2.hash(&mut hasher);
                    let second_hash = hasher.finish();
                    assert_eq!(first_hash, second_hash);
                }
                #[test]
                fn equality() {
                    let first = $alias_ident::from_iter([1, 2]);
                    let second = $alias_ident::from_iter([1]);
                    assert_ne!(first, second);
                }
                #[test]
                fn removal() {
                    let mut array = $alias_ident::from_iter([1, 2, 3]);
                    assert_eq!(Some(1), array.remove(0));
                    assert_eq!(Some(2), array.remove(1));
                    assert_eq!(Some(3), array.remove(2));
                    assert_eq!(None, array.remove(0))
                }
                #[test]
                fn failing_getters() {
                    let mut array = $alias_ident::from_iter([1, 2, 3, 4]);
                    assert_eq!(None, array.get_ref(5));
                    assert_eq!(None, array.get_ref(1000));
                    assert_eq!(None, array.get_mut(5));
                    assert_eq!(None, array.get_mut(1000));
                }
                #[test]
                fn succeeding_getters() {
                    let mut array = $alias_ident::from_iter([1, 2, 3, 4]);
                    assert_eq!(Some(&1), array.get_ref(0));
                    assert_eq!(Some(&mut 2), array.get_mut(1));
                }
                #[test]
                fn clearing() {
                    let mut array = $alias_ident::from_iter([1, 2, 3, 4]);
                    array.clear();
                    assert_eq!(array, $alias_ident::new());
                    assert_eq!(array.len(), 0);
                }
                #[test]
                fn clearing_with_drop() {
                    use std::rc::Rc;
                    let rc1 = Rc::new(1);
                    let rc2 = Rc::new(2);
                    let mut array = $alias_ident::from_iter([rc1.clone(), rc2.clone()]);
                    assert_eq!(Rc::strong_count(&rc1), 2);
                    assert_eq!(Rc::strong_count(&rc2), 2);
                    array.clear();
                    assert_eq!(Rc::strong_count(&rc1), 1);
                    assert_eq!(Rc::strong_count(&rc2), 1);
                }
                #[test]
                fn empty_indices_iterator() {
                    let array = $alias_ident::from_iter([0, 1]);
                    assert!(array.iter_empty_indices().all(|v| v != 0 && v != 1))
                }
                #[test]
                fn mutable_ref_iterator() {
                    let mut array = $alias_ident::from_iter([0, 1]);
                    array.iter_mut().for_each(|v| *v += 1);
                    let new_version = $alias_ident::from_iter([1, 2]);
                    assert_eq!(array, new_version);
                }
                #[test]
                fn insertion() {
                    let array = $alias_ident::from_iter([0, 1]);
                    assert_eq!(None, array.insert(2, 2));
                    let new_array = $alias_ident::from_iter([0, 1, 2]);
                    assert_eq!(array, new_array);
                }
                #[test]
                fn debug_print_no_ub() {
                    let array = $alias_ident::from_iter([0, 1]);
                    let formatted_string = std::format!("{:?}", array);
                    assert!(formatted_string.is_ascii());
                }
                #[test]
                fn emptiness() {
                    let array: $alias_ident<u8> = $alias_ident::new();
                    assert!(array.is_empty());
                    assert_eq!(0, array.len());
                }
            }
        }
    };
}

mask_tracked_array_impl!(
    (u8, 8, MaskTrackedArrayU8),
    (u16, 16, MaskTrackedArrayU16),
    (u32, 32, MaskTrackedArrayU32),
    (u64, 64, MaskTrackedArrayU64),
    (u128, 128, MaskTrackedArrayU128)
);
