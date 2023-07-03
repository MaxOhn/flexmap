use ::std::hash::{BuildHasher, Hash, Hasher};

use hashbrown::{hash_map::DefaultHashBuilder, HashMap};

use crate::MapLock;

#[cfg(feature = "std")]
pub use self::std::{StdMutexMap, StdMutexMarker, StdRwLockMap, StdRwLockMarker};

#[cfg(feature = "tokio")]
pub use self::tokio::{TokioMutexMap, TokioMutexMarker, TokioRwLockMap, TokioRwLockMarker};

/// Concurrent map with a similar internal structure to `DashMap`.
///
/// However, this map can get locked through any kind of locks like a `std::sync::RwLock` or a
/// `tokio::sync::Mutex`.
///
/// Access to the map is generally abstracted through a [`Guard`](crate::Guard).
///
/// # DEADLOCKS
///
/// Note that the map can still deadlock when you hold a write-guard and want to
/// get another guard while both happen to fall into the same shard.
/// So don't do that :)
pub struct FlexMap<K, V, S, L>
where
    L: MapLock<HashMap<K, V, S>>,
{
    pub(super) inner: Box<[L::Lock]>,
    shift: usize,
    hasher: S,
}

impl<K, V, S, L> FlexMap<K, V, S, L>
where
    L: MapLock<HashMap<K, V, S>>,
    S: BuildHasher,
{
    // https://github.com/xacrimon/dashmap/blob/459db7ac6f3d0b46f507cb724dd9bb0ce389f4ae/src/lib.rs#L366
    fn determine_shard<Q: Hash>(&self, key: &Q) -> usize {
        let mut hasher = self.hasher.build_hasher();
        key.hash(&mut hasher);
        let hash = hasher.finish() as usize;

        (hash << 7) >> self.shift
    }
}

// https://github.com/xacrimon/dashmap/blob/459db7ac6f3d0b46f507cb724dd9bb0ce389f4ae/src/lib.rs#L54
fn default_shard_amount() -> usize {
    (::std::thread::available_parallelism().map_or(1, usize::from) * 4).next_power_of_two()
}

macro_rules! impl_flex {
    ($($ty:ident: $orig:ident $lock:ident,)*) => {
        $(
            impl<K, V> FlexMap<K, V, DefaultHashBuilder, $ty> {
                /// Creates an empty map.
                pub fn new() -> Self {
                    Self::with_hasher(DefaultHashBuilder::default())
                }

                /// Creates an empty map with `shard_amount` many internal locked maps.
                ///
                /// # Panics
                ///
                /// `shard_amount` needs to be greater than 0 and be a power of two or this
                /// function panics.
                pub fn with_shard_amount(shard_amount: usize) -> Self {
                    Self::with_shard_amount_and_hasher(shard_amount, DefaultHashBuilder::default())
                }
            }

            impl<K, V, S: Clone> FlexMap<K, V, S, $ty> {
                /// Creates an empty map which will use the given hash builder to hash keys.
                pub fn with_hasher(hasher: S) -> Self {
                    Self::with_shard_amount_and_hasher(default_shard_amount(), hasher)
                }

                /// Creates an empty map with `shard_amount` many internal locked maps, each one
                /// using the given hash builder to hash keys.
                ///
                /// # Panics
                ///
                /// `shard_amount` needs to be greater than 0 and be a power of two or this
                /// function panics.
                pub fn with_shard_amount_and_hasher(shard_amount: usize, hasher: S) -> Self {
                    assert!(shard_amount > 0);
                    assert!(shard_amount.is_power_of_two());

                    let rev_shift = shard_amount.trailing_zeros() as usize;
                    let bits_in_usize = ::std::mem::size_of::<usize>() * 8;

                    let shift = bits_in_usize - rev_shift;

                    let inner = (0..shard_amount)
                        .map(|_| :: $orig ::sync:: $lock ::new(HashMap::with_hasher(hasher.clone())))
                        .collect::<Vec<_>>()
                        .into_boxed_slice();

                    Self {
                        inner,
                        shift,
                        hasher,
                    }
                }
            }
        )*
    }
}

impl_flex! {
    StdRwLockMarker:   std   RwLock,
    StdMutexMarker:    std   Mutex,
    TokioRwLockMarker: tokio RwLock,
    TokioMutexMarker:  tokio Mutex,
}

macro_rules! impl_traits {
    ($($map:ident: $lock:ident $own:ident $($unwrap:ident)?,)*) => {
        $(
            impl<K, V, S: Clone + Default> Default for $map<K, V, S> {
                fn default() -> Self {
                    let hasher = <S as Default>::default();

                    Self::with_shard_amount_and_hasher(super::default_shard_amount(), hasher)
                }
            }

            impl<K, V, S> Extend<(K, V)> for $map<K, V, S>
            where
                K: Eq + ::std::hash::Hash,
                S: ::std::hash::BuildHasher,
            {
                fn extend<I>(&mut self, iter: I)
                where
                    I: IntoIterator<Item = (K, V)>
                {
                    for (k, v) in iter {
                        self.$own(k)$(.$unwrap())?.insert(v);
                    }
                }
            }

            impl<K, V, S> FromIterator<(K, V)> for $map<K, V, S>
            where
                K: Eq + ::std::hash::Hash,
                S: ::std::hash::BuildHasher + Clone + Default
            {
                fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
                    let mut map = Self::default();
                    map.extend(iter);

                    map
                }
            }
        )*
    }
}

#[cfg(feature = "std")]
mod std {
    use std::{
        borrow::Borrow,
        fmt::{Debug, Formatter, Result as FmtResult},
        hash::{BuildHasher, Hash},
        sync::{Mutex, MutexGuard, RwLock, RwLockReadGuard, RwLockWriteGuard},
    };

    use hashbrown::{hash_map::DefaultHashBuilder, HashMap};

    use crate::{
        std::{StdMutexIter, StdRwLockIter, StdRwLockIterMut},
        FlexMap, Guard, MapLock, OwnGuard,
    };

    #[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
    /// Marker struct to mark a [`FlexMap`] as [`StdRwLockMap`].
    pub struct StdRwLockMarker;

    #[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
    /// Marker struct to mark a [`FlexMap`] as [`StdMutexMap`].
    pub struct StdMutexMarker;

    impl<M> MapLock<M> for StdRwLockMarker {
        type Lock = RwLock<M>;
    }

    impl<M> MapLock<M> for StdMutexMarker {
        type Lock = Mutex<M>;
    }

    /// [`FlexMap`] that operates on [`std::sync::RwLock`].
    pub type StdRwLockMap<K, V, S = DefaultHashBuilder> = FlexMap<K, V, S, StdRwLockMarker>;

    /// [`FlexMap`] that operates on [`std::sync::Mutex`].
    pub type StdMutexMap<K, V, S = DefaultHashBuilder> = FlexMap<K, V, S, StdMutexMarker>;

    type ReadGuard<'map, 'key, K, V, S, Q> =
        Guard<'key, RwLockReadGuard<'map, HashMap<K, V, S>>, K, V, Q>;
    type WriteGuard<'map, 'key, K, V, S, Q> =
        Guard<'key, RwLockWriteGuard<'map, HashMap<K, V, S>>, K, V, Q>;
    type OwnWriteGuard<'map, K, V, S> = OwnGuard<RwLockWriteGuard<'map, HashMap<K, V, S>>, K, V>;
    type LockGuard<'map, 'key, K, V, S, Q> =
        Guard<'key, MutexGuard<'map, HashMap<K, V, S>>, K, V, Q>;
    type OwnLockGuard<'map, K, V, S> = OwnGuard<MutexGuard<'map, HashMap<K, V, S>>, K, V>;

    impl<K, V, S> StdRwLockMap<K, V, S>
    where
        S: BuildHasher,
    {
        /// Acquire read access to a shard.
        ///
        /// # DEADLOCKS
        ///
        /// While not as bad as write access, you should still try to hold this guard
        /// as briefly as possible. If a write guard is being acquired while this guard
        /// is being held we got ourselves a potential deadlock.
        pub fn read<'map, 'key, Q>(&'map self, key: &'key Q) -> ReadGuard<'map, 'key, K, V, S, Q>
        where
            K: Borrow<Q>,
            Q: Eq + Hash,
        {
            let idx = self.determine_shard(key);
            let guard = self.inner[idx].read().expect("RwLock poisoned");

            Guard::new(guard, key)
        }

        /// Acquire write access to a shard.
        ///
        /// # DEADLOCKS
        ///
        /// Be sure you hold the guard as briefly as possible so that nothing deadlocks.
        /// If any guard for the same shard is being acquired while this guard is being held, that's no bueno.
        pub fn write<'map, 'key, Q>(&'map self, key: &'key Q) -> WriteGuard<'map, 'key, K, V, S, Q>
        where
            K: Borrow<Q>,
            Q: Eq + Hash,
        {
            let idx = self.determine_shard(key);
            let guard = self.inner[idx].write().expect("RwLock poisoned");

            Guard::new(guard, key)
        }

        /// Acquire write access to a shard by providing ownership to a key.
        ///
        /// # DEADLOCKS
        ///
        /// Be sure you hold the guard as briefly as possible so that nothing deadlocks.
        /// If any guard for the same shard is being acquired while this guard is being held, that's no bueno.
        pub fn own(&self, key: K) -> OwnWriteGuard<'_, K, V, S>
        where
            K: Eq + Hash,
        {
            let idx = self.determine_shard(&key);
            let guard = self.inner[idx].write().expect("RwLock poisoned");

            OwnGuard::new(guard, key)
        }
    }

    impl<K, V, S> StdRwLockMap<K, V, S> {
        /// Check if all shards are empty.
        ///
        /// # DEADLOCKS
        ///
        /// This method will acquire read access to the shards so be sure you don't
        /// have a write-guard lying around unless you intend to deadlock yourself.
        pub fn is_empty(&self) -> bool {
            self.inner
                .iter()
                .all(|map| map.read().expect("RwLock poisoned").is_empty())
        }

        /// Returns the total number of elements in the map.
        ///
        /// # DEADLOCKS
        ///
        /// This method will acquire read access to the shards so be sure you don't
        /// have a write-guard lying around unless you intent to deadlock yourself.
        #[allow(clippy::len_without_is_empty)] // why is that necessary...
        pub fn len(&self) -> usize {
            self.inner.iter().fold(0, |len, map| {
                map.read().expect("RwLock poisoned").len() + len
            })
        }

        /// Clear the map i.e. remove all entries.
        ///
        /// # DEADLOCKS
        ///
        /// This method will acquire write access to the shards so be sure you don't
        /// have a guard lying around unless you intent to deadlock yourself.
        pub async fn clear(&self) {
            for map in self.inner.iter() {
                map.write().expect("RwLock poisoned").clear();
            }
        }

        /// Returns an iterator to iterate over immutable references to all elements of all shards.
        ///
        /// # DEADLOCKS
        ///
        /// While iterating, be sure there is no write-guard around or it will deadlock.
        pub fn iter(&self) -> StdRwLockIter<'_, K, V, S> {
            StdRwLockIter::new(self)
        }

        /// Returns an iterator to iterate over mutable references to all elements of all shards.
        ///
        /// # DEADLOCKS
        ///
        /// While iterating, be sure there is no read- or write-guard around or it will deadlock.
        pub fn iter_mut(&self) -> StdRwLockIterMut<'_, K, V, S> {
            StdRwLockIterMut::new(self)
        }
    }

    impl<K, V, S> StdMutexMap<K, V, S>
    where
        S: BuildHasher,
    {
        /// Acquire sole access to a shard.
        ///
        /// # DEADLOCKS
        ///
        /// Hold the guard as briefly as possible since all other acquisations of this lock
        /// on the same shard will block until the guard is dropped.
        pub fn lock<'map, 'key, Q>(&'map self, key: &'key Q) -> LockGuard<'map, 'key, K, V, S, Q>
        where
            K: Borrow<Q>,
            Q: Eq + Hash,
        {
            let idx = self.determine_shard(key);
            let guard = self.inner[idx].lock().expect("Mutex poisoned");

            Guard::new(guard, key)
        }

        /// Acquire sole access to a shard by providing ownership to a key.
        ///
        /// # DEADLOCKS
        ///
        /// Hold the guard as briefly as possible since all other acquisations of this lock
        /// on the same shard will block until the guard is dropped.
        pub fn own(&self, key: K) -> OwnLockGuard<'_, K, V, S>
        where
            K: Eq + Hash,
        {
            let idx = self.determine_shard(&key);
            let guard = self.inner[idx].lock().expect("Mutex poisoned");

            OwnGuard::new(guard, key)
        }
    }

    impl<K, V, S> StdMutexMap<K, V, S> {
        /// Check if all shards are empty.
        ///
        /// # DEADLOCKS
        ///
        /// This method will acquire a lock to the shards so be sure you don't
        /// have a guard lying around unless you intend to deadlock yourself.
        pub fn is_empty(&self) -> bool {
            self.inner
                .iter()
                .all(|map| map.lock().expect("Mutex poisoned").is_empty())
        }

        /// Returns the total number of elements in the map.
        ///
        /// # DEADLOCKS
        ///
        /// This method will acquire a lock to the shards so be sure you don't
        /// have a guard lying around unless you intent to deadlock yourself.
        #[allow(clippy::len_without_is_empty)] // why is that necessary...
        pub fn len(&self) -> usize {
            self.inner.iter().fold(0, |len, map| {
                map.lock().expect("Mutex poisoned").len() + len
            })
        }

        /// Clear the map i.e. remove all entries.
        ///
        /// # DEADLOCKS
        ///
        /// This method will acquire a lock to the shards so be sure you don't
        /// have a write-guard lying around unless you intent to deadlock yourself.
        pub async fn clear(&self) {
            for map in self.inner.iter() {
                map.lock().expect("Mutex poisoned").clear();
            }
        }

        /// Returns an iterator to iterate over mutable references to all elements of all shards,
        /// same as `.iter_mut()`.
        ///
        /// # DEADLOCKS
        ///
        /// While iterating, be sure there is no guard around or it will deadlock.
        pub fn iter(&self) -> StdMutexIter<'_, K, V, S> {
            self.iter_mut()
        }

        /// Returns an iterator to iterate over mutable references to all elements of all shards.
        ///
        /// # DEADLOCKS
        ///
        /// While iterating, be sure there is no guard around or it will deadlock.
        pub fn iter_mut(&self) -> StdMutexIter<'_, K, V, S> {
            StdMutexIter::new(self)
        }
    }

    impl<K, V, S> Debug for StdRwLockMap<K, V, S>
    where
        K: Debug,
        V: Debug,
    {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            if f.alternate() {
                let mut iter = self.inner.iter();

                if let Some(inner) = iter.next() {
                    let locked = inner.read().expect("RwLock poisoned");
                    writeln!(f, "{locked:?}")?;

                    for inner in iter {
                        let locked = inner.read().expect("RwLock poisoned");
                        writeln!(f, "{locked:?}")?;
                    }
                }

                Ok(())
            } else {
                let mut f = f.debug_map();

                for inner in self.inner.iter() {
                    let locked = inner.read().expect("RwLock poisoned");
                    f.entries(locked.iter());
                }

                f.finish()
            }
        }
    }

    impl<K, V, S> Debug for StdMutexMap<K, V, S>
    where
        K: Debug,
        V: Debug,
    {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            if f.alternate() {
                let mut iter = self.inner.iter();

                if let Some(inner) = iter.next() {
                    let locked = inner.lock().expect("Mutex poisoned");
                    writeln!(f, "{locked:?}")?;

                    for inner in iter {
                        let locked = inner.lock().expect("Mutex poisoned");
                        writeln!(f, "{locked:?}")?;
                    }
                }

                Ok(())
            } else {
                let mut f = f.debug_map();

                for inner in self.inner.iter() {
                    let locked = inner.lock().expect("Mutex poisoned");
                    f.entries(locked.iter());
                }

                f.finish()
            }
        }
    }

    impl_traits! {
        StdRwLockMap: write own,
        StdMutexMap: lock own,
    }
}

#[cfg(feature = "tokio")]
mod tokio {
    use std::{
        borrow::Borrow,
        fmt::{Debug, Formatter, Result as FmtResult},
        hash::{BuildHasher, Hash},
    };

    use hashbrown::{hash_map::DefaultHashBuilder, HashMap};
    use tokio::sync::{Mutex, MutexGuard, RwLock, RwLockReadGuard, RwLockWriteGuard, TryLockError};

    use crate::{
        tokio::{TokioMutexStream, TokioRwLockStream, TokioRwLockStreamMut},
        FlexMap, Guard, MapLock, OwnGuard,
    };

    #[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
    /// Marker struct to mark a [`FlexMap`] as [`TokioRwLockMap`].
    pub struct TokioRwLockMarker;

    #[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
    /// Marker struct to mark a [`FlexMap`] as [`TokioMutexMap`].
    pub struct TokioMutexMarker;

    impl<M> MapLock<M> for TokioRwLockMarker {
        type Lock = RwLock<M>;
    }

    impl<M> MapLock<M> for TokioMutexMarker {
        type Lock = Mutex<M>;
    }

    /// [`FlexMap`] that operates on [tokio](https://docs.rs/tokio/latest/tokio/)'s `RwLock`.
    pub type TokioRwLockMap<K, V, S = DefaultHashBuilder> = FlexMap<K, V, S, TokioRwLockMarker>;

    /// [`FlexMap`] that operates on [tokio](https://docs.rs/tokio/latest/tokio/)'s `Mutex`.
    pub type TokioMutexMap<K, V, S = DefaultHashBuilder> = FlexMap<K, V, S, TokioMutexMarker>;

    type ReadGuard<'map, 'key, K, V, S, Q> =
        Guard<'key, RwLockReadGuard<'map, HashMap<K, V, S>>, K, V, Q>;
    type WriteGuard<'map, 'key, K, V, S, Q> =
        Guard<'key, RwLockWriteGuard<'map, HashMap<K, V, S>>, K, V, Q>;
    type OwnWriteGuard<'map, K, V, S> = OwnGuard<RwLockWriteGuard<'map, HashMap<K, V, S>>, K, V>;
    type LockGuard<'map, 'key, K, V, S, Q> =
        Guard<'key, MutexGuard<'map, HashMap<K, V, S>>, K, V, Q>;
    type OwnLockGuard<'map, K, V, S> = OwnGuard<MutexGuard<'map, HashMap<K, V, S>>, K, V>;

    impl<K, V, S> TokioRwLockMap<K, V, S>
    where
        S: BuildHasher,
    {
        /// Acquire read access to a shard.
        ///
        /// # DEADLOCKS
        ///
        /// While not as bad as write access, you should still try to hold this guard
        /// as briefly as possible. If a write guard is being acquired while this guard
        /// is being held we got ourselves a potential deadlock.
        pub async fn read<'map, 'key, Q>(
            &'map self,
            key: &'key Q,
        ) -> ReadGuard<'map, 'key, K, V, S, Q>
        where
            K: Borrow<Q>,
            Q: Eq + Hash,
        {
            let idx = self.determine_shard(key);

            Guard::new(self.inner[idx].read().await, key)
        }

        /// Try to acquire read access to a shard. Fails if there is already is a write-guard in use.
        ///
        /// # DEADLOCKS
        ///
        /// While not as bad as write access, you should still try to hold this guard
        /// as briefly as possible. If a write guard is being acquired while this guard
        /// is being held we got ourselves a potential deadlock.
        pub fn try_read<'map, 'key, Q>(
            &'map self,
            key: &'key Q,
        ) -> Result<ReadGuard<'map, 'key, K, V, S, Q>, TryLockError>
        where
            K: Borrow<Q>,
            Q: Eq + Hash,
        {
            let idx = self.determine_shard(key);

            Ok(Guard::new(self.inner[idx].try_read()?, key))
        }

        /// Acquire write access to a shard.
        ///
        /// # DEADLOCKS
        ///
        /// Be sure you hold the guard as briefly as possible so that nothing deadlocks.
        /// If any guard for the same shard is being acquired while this guard is being held, that's no bueno.
        pub async fn write<'map, 'key, Q>(
            &'map self,
            key: &'key Q,
        ) -> WriteGuard<'map, 'key, K, V, S, Q>
        where
            K: Borrow<Q>,
            Q: Eq + Hash,
        {
            let idx = self.determine_shard(key);

            Guard::new(self.inner[idx].write().await, key)
        }

        /// Try to acquire write access to a shard. Fails if there already is a write-guard in use.
        ///
        /// # DEADLOCKS
        ///
        /// Be sure you hold the guard as briefly as possible so that nothing deadlocks.
        /// If any guard for the same shard is being acquired while this guard is being held, that's no bueno.
        pub fn try_write<'map, 'key, Q>(
            &'map self,
            key: &'key Q,
        ) -> Result<WriteGuard<'map, 'key, K, V, S, Q>, TryLockError>
        where
            K: Borrow<Q>,
            Q: Eq + Hash,
        {
            let idx = self.determine_shard(key);

            Ok(Guard::new(self.inner[idx].try_write()?, key))
        }

        /// Acquire write access to a shard by providing ownership to a key.
        ///
        /// # DEADLOCKS
        ///
        /// Be sure you hold the guard as briefly as possible so that nothing deadlocks.
        /// If any guard for the same shard is being acquired while this guard is being held, that's no bueno.
        pub async fn own(&self, key: K) -> OwnWriteGuard<'_, K, V, S>
        where
            K: Eq + Hash,
        {
            let idx = self.determine_shard(&key);

            OwnGuard::new(self.inner[idx].write().await, key)
        }

        /// Try to acquire write access to a shard by providing ownership to a key.
        /// Fails if there already is a write-guard in use.
        ///
        /// # DEADLOCKS
        ///
        /// Be sure you hold the guard as briefly as possible so that nothing deadlocks.
        /// If any guard for the same shard is being acquired while this guard is being held, that's no bueno.
        pub fn try_own(&self, key: K) -> Result<OwnWriteGuard<'_, K, V, S>, TryLockError>
        where
            K: Eq + Hash,
        {
            let idx = self.determine_shard(&key);

            Ok(OwnGuard::new(self.inner[idx].try_write()?, key))
        }
    }

    impl<K, V, S> TokioRwLockMap<K, V, S> {
        /// Check if all shards are empty.
        ///
        /// # DEADLOCKS
        ///
        /// This method will acquire read access to the shards so be sure you don't
        /// have a write-guard lying around unless you intend to deadlock yourself.
        pub async fn is_empty(&self) -> bool {
            for map in self.inner.iter() {
                if !map.read().await.is_empty() {
                    return false;
                }
            }

            true
        }

        /// Returns the total number of elements in the map.
        ///
        /// # DEADLOCKS
        ///
        /// This method will acquire read access to the shards so be sure you don't
        /// have a write-guard lying around unless you intent to deadlock yourself.
        pub async fn len(&self) -> usize {
            let mut len = 0;

            for map in self.inner.iter() {
                len += map.read().await.len();
            }

            len
        }

        /// Clear the map i.e. remove all entries.
        ///
        /// # DEADLOCKS
        ///
        /// This method will acquire write access to the shards so be sure you don't
        /// have a guard lying around unless you intent to deadlock yourself.
        pub async fn clear(&self) {
            for map in self.inner.iter() {
                map.write().await.clear();
            }
        }

        /// Returns a stream to iterate over immutable references to all elements of all shards.
        ///
        /// # DEADLOCKS
        ///
        /// While iterating, be sure there is no write-guard around or it will deadlock.
        pub fn iter(&self) -> TokioRwLockStream<'_, K, V, S> {
            TokioRwLockStream::new(self)
        }

        /// Returns a stream to iterate over mutable references to all elements of all shards.
        ///
        /// # DEADLOCKS
        ///
        /// While iterating, be sure there is no read- or write-guard around or it will deadlock.
        pub fn iter_mut(&self) -> TokioRwLockStreamMut<'_, K, V, S> {
            TokioRwLockStreamMut::new(self)
        }
    }

    impl<K, V, S> TokioMutexMap<K, V, S>
    where
        S: BuildHasher,
    {
        /// Acquire sole access to a shard.
        ///
        /// # DEADLOCKS
        ///
        /// Hold the guard as briefly as possible since all other acquisations of this lock
        /// on the same shard will block until the guard is dropped.
        pub async fn lock<'map, 'key, Q>(
            &'map self,
            key: &'key Q,
        ) -> LockGuard<'map, 'key, K, V, S, Q>
        where
            K: Borrow<Q>,
            Q: Eq + Hash,
        {
            let idx = self.determine_shard(key);

            Guard::new(self.inner[idx].lock().await, key)
        }

        /// Try to acquire sole access to a shard. Fails if there already is a guard around.
        ///
        /// # DEADLOCKS
        ///
        /// Hold the guard as briefly as possible since all other acquisations of this lock
        /// on the same shard will block until the guard is dropped.
        pub fn try_lock<'map, 'key, Q>(
            &'map self,
            key: &'key Q,
        ) -> Result<LockGuard<'map, 'key, K, V, S, Q>, TryLockError>
        where
            K: Borrow<Q>,
            Q: Eq + Hash,
        {
            let idx = self.determine_shard(key);

            Ok(Guard::new(self.inner[idx].try_lock()?, key))
        }

        /// Acquire sole access to a shard by providing ownership to a key.
        ///
        /// # DEADLOCKS
        ///
        /// Hold the guard as briefly as possible since all other acquisations of this lock
        /// on the same shard will block until the guard is dropped.
        pub async fn own(&self, key: K) -> OwnLockGuard<'_, K, V, S>
        where
            K: Eq + Hash,
        {
            let idx = self.determine_shard(&key);

            OwnGuard::new(self.inner[idx].lock().await, key)
        }

        /// Try to acquire sole access to a shard by providing ownership to a key.
        /// Fails if there already is a guard around.
        ///
        /// # DEADLOCKS
        ///
        /// Hold the guard as briefly as possible since all other acquisations of this lock
        /// on the same shard will block until the guard is dropped.
        pub fn try_own(&self, key: K) -> Result<OwnLockGuard<'_, K, V, S>, TryLockError>
        where
            K: Eq + Hash,
        {
            let idx = self.determine_shard(&key);

            Ok(OwnGuard::new(self.inner[idx].try_lock()?, key))
        }
    }

    impl<K, V, S> TokioMutexMap<K, V, S> {
        /// Check if all shards are empty.
        ///
        /// # DEADLOCKS
        ///
        /// This method will acquire read access to the shards so be sure you don't
        /// have a guard lying around unless you intend to deadlock yourself.
        pub async fn is_empty(&self) -> bool {
            for map in self.inner.iter() {
                if !map.lock().await.is_empty() {
                    return false;
                }
            }

            true
        }

        /// Returns the total number of elements in the map.
        ///
        /// # DEADLOCKS
        ///
        /// This method will acquire a lock to the shards so be sure you don't
        /// have a write-guard lying around unless you intent to deadlock yourself.
        pub async fn len(&self) -> usize {
            let mut len = 0;

            for map in self.inner.iter() {
                len += map.lock().await.len();
            }

            len
        }

        /// Clear the map i.e. remove all entries.
        ///
        /// # DEADLOCKS
        ///
        /// This method will acquire a lock to the shards so be sure you don't
        /// have a write-guard lying around unless you intent to deadlock yourself.
        pub async fn clear(&self) {
            for map in self.inner.iter() {
                map.lock().await.clear();
            }
        }

        /// Returns a stream to iterate over mutable references to all elements of all shards,
        /// same as `.iter_mut()`.
        ///
        /// # DEADLOCKS
        ///
        /// While iterating, be sure there is no guard around or it will deadlock.
        pub fn iter(&self) -> TokioMutexStream<'_, K, V, S> {
            self.iter_mut()
        }

        /// Returns a stream to iterate over mutable references to all elements of all shards.
        ///
        /// # DEADLOCKS
        ///
        /// While iterating, be sure there is no guard around or it will deadlock.
        pub fn iter_mut(&self) -> TokioMutexStream<'_, K, V, S> {
            TokioMutexStream::new(self)
        }
    }

    impl<K, V, S> Debug for TokioRwLockMap<K, V, S>
    where
        K: Debug,
        V: Debug,
    {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            if f.alternate() {
                let mut iter = self.inner.iter();

                if let Some(inner) = iter.next() {
                    match inner.try_read() {
                        Ok(locked) => write!(f, "{locked:?}")?,
                        Err(_) => write!(f, "<locked>")?,
                    }

                    for inner in iter {
                        match inner.try_read() {
                            Ok(locked) => write!(f, "\n{locked:?}")?,
                            Err(_) => write!(f, "\n<locked>")?,
                        }
                    }
                }

                Ok(())
            } else {
                let mut locked = 0;
                let mut f_map = f.debug_map();

                for inner in self.inner.iter() {
                    match inner.try_read() {
                        Ok(locked) => {
                            f_map.entries(locked.iter());
                        }
                        Err(_) => locked += 1,
                    }
                }

                f_map.finish()?;

                if locked > 0 {
                    write!(f, "{locked} inner maps were locked")?;
                }

                Ok(())
            }
        }
    }

    impl<K, V, S> Debug for TokioMutexMap<K, V, S>
    where
        K: Debug,
        V: Debug,
    {
        fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
            if f.alternate() {
                let mut iter = self.inner.iter();

                if let Some(inner) = iter.next() {
                    match inner.try_lock() {
                        Ok(locked) => write!(f, "{locked:?}")?,
                        Err(_) => write!(f, "<locked>")?,
                    }

                    for inner in iter {
                        match inner.try_lock() {
                            Ok(locked) => write!(f, "\n{locked:?}")?,
                            Err(_) => write!(f, "\n<locked>")?,
                        }
                    }
                }

                Ok(())
            } else {
                let mut locked = 0;
                let mut f_map = f.debug_map();

                for inner in self.inner.iter() {
                    match inner.try_lock() {
                        Ok(locked) => {
                            f_map.entries(locked.iter());
                        }
                        Err(_) => locked += 1,
                    }
                }

                f_map.finish()?;

                if locked > 0 {
                    write!(f, "{locked} inner maps were locked")?;
                }

                Ok(())
            }
        }
    }

    impl_traits! {
        TokioRwLockMap: try_write try_own unwrap,
        TokioMutexMap: try_lock try_own unwrap,
    }
}
