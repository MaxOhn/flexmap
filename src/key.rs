/// Trait to help [`FlexMap`](crate::FlexMap) figure out in which internal
/// hashmap a given entry should be stored.
pub trait FlexMapKey {
    /// Given a reference to a key, return the index of the hashmap in which the entry should be
    /// stored. The index must be between `0` and `N` (excluded).
    ///
    /// The more evenly the indices are spread between keys contained in the map, the more
    /// performant the map becomes and the lower the likelyhood of deadlocking yourself.
    fn index<const N: usize>(&self) -> usize;
}

macro_rules! impl_separator {
    ($($ty:ty),*) => {
        $(
            impl FlexMapKey for $ty {
                #[inline]
                fn index<const N: usize>(&self) -> usize {
                    *self as usize % N
                }
            }
        )*
    };
}

impl_separator!(u8, u16, u32, u64, usize, i8, i16, i32, i64, isize);
