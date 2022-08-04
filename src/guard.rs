use ::std::marker::PhantomData;

/// A guard that is generic over the lock type.
///
/// Be sure to hold these as briefly as possible to avoid deadlocking yourself.
#[derive(Debug)]
pub struct Guard<'key, G, K, V, Q> {
    guard: G,
    key: &'key Q,
    value: PhantomData<(K, V)>,
}

impl<'key, G, K, V, Q> Guard<'key, G, K, V, Q> {
    pub(super) fn new(guard: G, key: &'key Q) -> Self {
        Self {
            guard,
            key,
            value: PhantomData,
        }
    }
}

/// A guard that is generic over the lock and contains ownership of a key.
///
/// Be sure to hold these as briefly as possible to avoid deadlocking yourself.
#[derive(Debug)]
pub struct OwnGuard<G, K, V> {
    guard: G,
    key: Option<K>,
    value: PhantomData<V>,
}

impl<G, K, V> OwnGuard<G, K, V> {
    pub(super) fn new(guard: G, key: K) -> Self {
        Self {
            guard,
            key: Some(key),
            value: PhantomData,
        }
    }
}

macro_rules! read_guard_methods {
    ($($ty:ident),*) => {
        $(
            impl<'key, K, V, S, Q> crate::Guard<'key, $ty<'_, hashbrown::HashMap<K, V, S>>, K, V, Q>
            where
                K: ::std::borrow::Borrow<Q> + Eq + ::std::hash::Hash,
                Q: Eq + ::std::hash::Hash,
                S: ::std::hash::BuildHasher,
            {
                read_guard_methods!(@INNER);
            }
        )*
    };

    (@INNER $(.$handle:ident ())*) => {
        /// Returns a reference to the value corresponding to the key.
        pub fn get(&self) -> Option<&V> {
            self.guard.get(self.key $(. $handle ())*)
        }
    }
}

macro_rules! write_guard_methods {
    ($($ty:ident),*) => {
        $(
            impl<'key, K, V, S, Q> crate::Guard<'key, $ty<'_, hashbrown::HashMap<K, V, S>>, K, V, Q>
            where
                K: ::std::borrow::Borrow<Q> + Eq + ::std::hash::Hash,
                Q: Eq + ::std::hash::Hash,
                S: ::std::hash::BuildHasher,
            {
                write_guard_methods!(@INNER);
            }
        )*
    };

    (@INNER $(. $handle:ident ())*) => {
        read_guard_methods!(@INNER $(. $handle ())*);

        /// Returns a mutable reference to the value corresponding to the key.
        pub fn get_mut(&mut self) -> Option<&mut V> {
            self.guard.get_mut(self.key $(. $handle ())*)
        }

        /// Removes the key from the map, returning the value at the key if the key was
        /// previously in the map. Keeps the allocated memory for reuse.
        pub fn remove(&mut self) -> Option<V> {
            self.guard.remove(self.key $(. $handle ())*)
        }
    }
}

macro_rules! own_guard_methods {
    ($($ty:ident),*) => {
        $(
            impl<K, V, S> crate::OwnGuard<$ty<'_, hashbrown::HashMap<K, V, S>>, K, V>
            where
                K: Eq + ::std::hash::Hash,
                S: ::std::hash::BuildHasher,
            {
                write_guard_methods!(@INNER .as_ref().unwrap());
            }

            impl<'map, K, V, S> crate::OwnGuard<$ty<'map, hashbrown::HashMap<K, V, S>>, K, V>
            where
                K: Eq + ::std::hash::Hash,
                S: ::std::hash::BuildHasher,
            {
                /// Inserts a value into the map.
                ///
                /// If the map did not have the key present, [`None`] is returned.
                ///
                /// If the map did have the key present, the value is updated, and the old value is
                /// returned. The key is not updated, though; this matters for types that can be
                /// `==` without being identical.
                pub fn insert(mut self, value: V) -> Option<V> {
                    let key = self.key.take().unwrap();

                    self.guard.insert(key, value)
                }

                /// Gets the key's corresponding entry in the map for in-place manipulation.
                ///
                /// After calling this method, `self`'s only purpose is to keep the inner lock
                /// in scope. Do *not* call any other method on it.
                pub fn entry(&mut self) -> hashbrown::hash_map::Entry<'_, K, V, S> {
                    let key = self.key.take().unwrap();

                    self.guard.entry(key)
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
    own_guard_methods!(RwLockWriteGuard, MutexGuard);
}

#[cfg(feature = "tokio")]
mod tokio {
    use tokio::sync::{MutexGuard, RwLockReadGuard, RwLockWriteGuard};

    read_guard_methods!(RwLockReadGuard);
    write_guard_methods!(RwLockWriteGuard, MutexGuard);
    own_guard_methods!(RwLockWriteGuard, MutexGuard);
}
