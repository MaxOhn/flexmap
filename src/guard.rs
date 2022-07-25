use ::std::marker::PhantomData;

/// A guard that is generic over the lock type.
///
/// Be sure to hold these as briefly as possible to avoid deadlocking yourself.
#[derive(Debug)]
pub struct Guard<G, K, V> {
    guard: G,
    key: K,
    value: PhantomData<V>,
}

impl<G, K, V> Guard<G, K, V> {
    pub(super) fn new(guard: G, key: K) -> Self {
        Self {
            guard,
            key,
            value: PhantomData,
        }
    }
}

macro_rules! read_guard_methods {
    ($($ty:ident),*) => {
        $(
            impl<K, V> crate::Guard<$ty<'_, hashbrown::HashMap<K, V>>, K, V>
            where
                K: Eq + ::std::hash::Hash,
            {
                /// Returns a reference to the value corresponding to the key.
                pub fn get(&self) -> Option<&V> {
                    self.guard.get(&self.key)
                }
            }
        )*
    }
}

macro_rules! write_guard_methods {
    ($($ty:ident),*) => {
        $(
            impl<K, V> crate::Guard<$ty<'_, hashbrown::HashMap<K, V>>, K, V>
            where
                K: Eq + ::std::hash::Hash,
            {
                /// Returns a reference to the value corresponding to the key.
                pub fn get(&self) -> Option<&V> {
                    self.guard.get(&self.key)
                }

                /// Returns a mutable reference to the value corresponding to the key.
                pub fn get_mut(&mut self) -> Option<&mut V> {
                    self.guard.get_mut(&self.key)
                }

                /// Inserts a value into the map.
                ///
                /// If the map did not have the key present, [`None`] is returned.
                ///
                /// If the map did have the key present, the value is updated, and the old value is
                /// returned. The key is not updated, though; this matters for types that can be
                /// `==` without being identical.
                pub fn insert(mut self, value: V) -> Option<V> {
                    self.guard.insert(self.key, value)
                }

                /// Removes the key from the map, returning the value at the key if the key was
                /// previously in the map. Keeps the allocated memory for reuse.
                pub fn remove(&mut self) -> Option<V> {
                    self.guard.remove(&self.key)
                }
            }

            impl<K, V, S> crate::Guard<$ty<'_, hashbrown::HashMap<K, V, S>>, K, V>
            where
                K: Copy + Eq + ::std::hash::Hash,
                S: ::std::hash::BuildHasher
            {
                /// Gets the key's corresponding entry in the map for in-place manipulation.
                pub fn entry(&mut self) -> hashbrown::hash_map::Entry<'_, K, V, S> {
                    self.guard.entry(self.key)
                }
            }
        )*
    }
}

#[cfg(feature = "std")]
mod std {
    use std::sync::{MutexGuard, RwLockReadGuard, RwLockWriteGuard};

    read_guard_methods!(RwLockReadGuard);
    write_guard_methods!(RwLockWriteGuard, MutexGuard);
}

#[cfg(feature = "tokio")]
mod tokio {
    use tokio::sync::{MutexGuard, RwLockReadGuard, RwLockWriteGuard};

    read_guard_methods!(RwLockReadGuard);
    write_guard_methods!(RwLockWriteGuard, MutexGuard);
}
