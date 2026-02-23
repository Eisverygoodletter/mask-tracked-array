use bit_iter::BitIter;
/// An integer mask trait
pub trait Mask:
    num_traits::PrimInt
    + num_traits::ConstZero
    + num_traits::ConstOne
    + num_traits::Bounded
    + num_traits::Euclid
{
    /// An instance of the mask with all indices selected.
    const ALL_SELECTED: Self;
    /// An instance of the mask with no indices selected.
    const NONE_SELECTED: Self;
    /// An instance of the mask with the lowest index (1) selected.
    const ONE_SELECTED: Self;
    /// The number of bits in the mask
    const MAX_SELECTIONS: u32;
    /// Convert an index into an instance of this mask.
    #[inline]
    fn index_to_mask(index: usize) -> Self {
        Self::ONE_SELECTED << index
    }
    /// Convert this mask into an iterator of indices.
    fn mask_to_indices(self) -> impl Iterator<Item = usize>;
}
macro_rules! impl_mask_trait {
    ($t:ty) => {
        impl Mask for $t {
            const ALL_SELECTED: Self = Self::MAX;
            const NONE_SELECTED: Self = 0;
            const ONE_SELECTED: Self = 1;
            const MAX_SELECTIONS: u32 = Self::BITS;
            #[inline]
            fn mask_to_indices(self) -> impl Iterator<Item = usize> {
                BitIter::from(self)
            }
        }
        paste::paste! {
            #[test]
            fn [< correct_inverse_ $t >]() {
                let mask = $t::index_to_mask(2);
                let mut iter = mask.mask_to_indices();
                assert_eq!(iter.next().unwrap(), 2);
                assert_eq!(iter.next(), None);
            }
        }
    };
    ($($t:ty),*) => {
        $(
            impl_mask_trait!($t);
        )*
    };
}
impl_mask_trait!(u8, u16, u32, u64, u128);
