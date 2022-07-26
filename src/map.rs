use ::std::{iter, marker::PhantomData};

use hashbrown::HashMap;

use crate::MapLock;

#[cfg(feature = "std")]
pub use self::std::{StdMutexMap, StdMutexMarker, StdRwLockMap, StdRwLockMarker};

#[cfg(feature = "tokio")]
pub use self::tokio::{TokioMutexMap, TokioMutexMarker, TokioRwLockMap, TokioRwLockMarker};

/// Concurrent map with a similar internal structure to `DashMap`.
///
/// However, the amount of shards for this map can be set manually
/// and can also be locked through any kind of locks like a `std::sync::RwLock` or a `tokio::sync::Mutex`.
///
/// Access to the map is generally abstracted through a [`Guard`](crate::Guard) which you get
/// from either `FlexMap::read` or `FlexMap::write`.
///
/// # DEADLOCKS
///
/// Note that the map can still deadlock when you hold a write-guard and want to
/// get another guard while both happen to fall into the same shard.
/// So don't do that :)
pub struct FlexMap<K, V, L, const N: usize>
where
    L: MapLock<HashMap<K, V>>,
{
    pub(super) inner: Box<[L::Lock]>,
    inner_count: PhantomData<[(); N]>,
}

impl<K, V, L, const N: usize> Default for FlexMap<K, V, L, N>
where
    L: MapLock<HashMap<K, V>>,
    L::Lock: Default,
{
    #[inline]
    fn default() -> Self {
        let inner = iter::repeat_with(<L::Lock as Default>::default)
            .collect::<Vec<_>>()
            .into_boxed_slice();

        Self {
            inner,
            inner_count: PhantomData,
        }
    }
}

macro_rules! impl_from_iter {
    ($($map:ident: $lock:ident $($unwrap:ident)?,)*) => {
        $(
            impl<K, V, const N: usize> FromIterator<(K, V)> for $map<K, V, N>
            where
                K: crate::FlexMapKey + Eq + ::std::hash::Hash,
            {
                fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
                    let map = Self::default();

                    let iter = iter.into_iter();
                    let (len, _) = iter.size_hint();

                    if len > N {
                        let mut guards: Vec<_> = map.inner.iter().map(|lock| lock.$lock().unwrap()).collect();

                        for (key, value) in iter {
                            guards[key.index::<N>()].insert(key, value);
                        }
                    } else {
                        for (key, value) in iter {
                            map.$lock(key)$(.$unwrap())?.insert(value);
                        }
                    }

                    map
                }
            }
        )*
    }
}

#[cfg(feature = "std")]
mod std {
    use std::{
        fmt::{Debug, Formatter, Result as FmtResult},
        sync::{Mutex, MutexGuard, RwLock, RwLockReadGuard, RwLockWriteGuard},
    };

    use hashbrown::HashMap;

    use crate::{
        std::{StdMutexIter, StdRwLockIter, StdRwLockIterMut},
        FlexMap, FlexMapKey, Guard, MapLock,
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
    pub type StdRwLockMap<K, V, const N: usize = 10> = FlexMap<K, V, StdRwLockMarker, N>;

    /// [`FlexMap`] that operates on [`std::sync::Mutex`].
    pub type StdMutexMap<K, V, const N: usize = 10> = FlexMap<K, V, StdMutexMarker, N>;

    type ReadGuard<'map, K, V> = Guard<RwLockReadGuard<'map, HashMap<K, V>>, K, V>;
    type WriteGuard<'map, K, V> = Guard<RwLockWriteGuard<'map, HashMap<K, V>>, K, V>;
    type LockGuard<'map, K, V> = Guard<MutexGuard<'map, HashMap<K, V>>, K, V>;

    impl<K: FlexMapKey, V, const N: usize> StdRwLockMap<K, V, N> {
        /// Acquire read access to a shard.
        ///
        /// # DEADLOCKS
        ///
        /// While not as bad as write access, you should still try to hold this guard
        /// as briefly as possible. If a write guard is being acquired while this guard
        /// is being held we got ourselves a potential deadlock.
        pub fn read(&self, key: K) -> ReadGuard<'_, K, V> {
            let guard = self.inner[key.index::<N>()]
                .read()
                .expect("RwLock poisoned");

            Guard::new(guard, key)
        }

        /// Acquire write access to a shard.
        ///
        /// # DEADLOCKS
        ///
        /// Be sure you hold the guard as briefly as possible so that nothing deadlocks.
        /// If any guard for the same shard is being acquired while this guard is being held, that's no bueno.
        pub fn write(&self, key: K) -> WriteGuard<'_, K, V> {
            let guard = self.inner[key.index::<N>()]
                .write()
                .expect("RwLock poisoned");

            Guard::new(guard, key)
        }

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

        /// Returns an iterator to iterate over immutable references to all elements of all shards.
        ///
        /// # DEADLOCKS
        ///
        /// While iterating, be sure there is no write-guard around or it will deadlock.
        pub fn iter(&self) -> StdRwLockIter<'_, K, V, N> {
            StdRwLockIter::new(self)
        }

        /// Returns an iterator to iterate over mutable references to all elements of all shards.
        ///
        /// # DEADLOCKS
        ///
        /// While iterating, be sure there is no read- or write-guard around or it will deadlock.
        pub fn iter_mut(&self) -> StdRwLockIterMut<'_, K, V, N> {
            StdRwLockIterMut::new(self)
        }
    }

    impl<K: FlexMapKey, V, const N: usize> StdMutexMap<K, V, N> {
        /// Acquire sole access to a shard.
        ///
        /// # DEADLOCKS
        ///
        /// Hold the guard as briefly as possible since all other acquisations of this lock
        /// on the same shard will block until the guard is dropped.
        pub fn lock(&self, key: K) -> LockGuard<'_, K, V> {
            let guard = self.inner[key.index::<N>()].lock().expect("Mutex poisoned");

            Guard::new(guard, key)
        }

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

        /// Returns an iterator to iterate over mutable references to all elements of all shards,
        /// same as `.iter_mut()`.
        ///
        /// # DEADLOCKS
        ///
        /// While iterating, be sure there is no guard around or it will deadlock.
        pub fn iter(&self) -> StdMutexIter<'_, K, V, N> {
            self.iter_mut()
        }

        /// Returns an iterator to iterate over mutable references to all elements of all shards.
        ///
        /// # DEADLOCKS
        ///
        /// While iterating, be sure there is no guard around or it will deadlock.
        pub fn iter_mut(&self) -> StdMutexIter<'_, K, V, N> {
            StdMutexIter::new(self)
        }
    }

    impl<K, V, const N: usize> Debug for StdRwLockMap<K, V, N>
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

    impl<K, V, const N: usize> Debug for StdMutexMap<K, V, N>
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

    impl_from_iter! {
        StdRwLockMap: write,
        StdMutexMap: lock,
    }
}

#[cfg(feature = "tokio")]
mod tokio {
    use std::fmt::{Debug, Formatter, Result as FmtResult};

    use hashbrown::HashMap;
    use tokio::sync::{Mutex, MutexGuard, RwLock, RwLockReadGuard, RwLockWriteGuard, TryLockError};

    use crate::{
        tokio::{TokioMutexStream, TokioRwLockStream, TokioRwLockStreamMut},
        FlexMap, FlexMapKey, Guard, MapLock,
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
    pub type TokioRwLockMap<K, V, const N: usize = 10> = FlexMap<K, V, TokioRwLockMarker, N>;

    /// [`FlexMap`] that operates on [tokio](https://docs.rs/tokio/latest/tokio/)'s `Mutex`.
    pub type TokioMutexMap<K, V, const N: usize = 10> = FlexMap<K, V, TokioMutexMarker, N>;

    type ReadGuard<'map, K, V> = Guard<RwLockReadGuard<'map, HashMap<K, V>>, K, V>;
    type WriteGuard<'map, K, V> = Guard<RwLockWriteGuard<'map, HashMap<K, V>>, K, V>;
    type LockGuard<'map, K, V> = Guard<MutexGuard<'map, HashMap<K, V>>, K, V>;

    impl<K: FlexMapKey, V, const N: usize> TokioRwLockMap<K, V, N> {
        /// Acquire read access to a shard.
        ///
        /// # DEADLOCKS
        ///
        /// While not as bad as write access, you should still try to hold this guard
        /// as briefly as possible. If a write guard is being acquired while this guard
        /// is being held we got ourselves a potential deadlock.
        pub async fn read(&self, key: K) -> ReadGuard<'_, K, V> {
            Guard::new(self.inner[key.index::<N>()].read().await, key)
        }

        /// Try to acquire read access to a shard. Fails if there is already is a write-guard in use.
        ///
        /// # DEADLOCKS
        ///
        /// While not as bad as write access, you should still try to hold this guard
        /// as briefly as possible. If a write guard is being acquired while this guard
        /// is being held we got ourselves a potential deadlock.
        pub fn try_read(&self, key: K) -> Result<ReadGuard<'_, K, V>, TryLockError> {
            Ok(Guard::new(self.inner[key.index::<N>()].try_read()?, key))
        }

        /// Acquire write access to a shard.
        ///
        /// # DEADLOCKS
        ///
        /// Be sure you hold the guard as briefly as possible so that nothing deadlocks.
        /// If any guard for the same shard is being acquired while this guard is being held, that's no bueno.
        pub async fn write(&self, key: K) -> WriteGuard<'_, K, V> {
            Guard::new(self.inner[key.index::<N>()].write().await, key)
        }

        /// Try to acquire write access to a shard. Fails if there already is a write-guard in use.
        ///
        /// # DEADLOCKS
        ///
        /// Be sure you hold the guard as briefly as possible so that nothing deadlocks.
        /// If any guard for the same shard is being acquired while this guard is being held, that's no bueno.
        pub fn try_write(&self, key: K) -> Result<WriteGuard<'_, K, V>, TryLockError> {
            Ok(Guard::new(self.inner[key.index::<N>()].try_write()?, key))
        }

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

        /// Returns a stream to iterate over immutable references to all elements of all shards.
        ///
        /// # DEADLOCKS
        ///
        /// While iterating, be sure there is no write-guard around or it will deadlock.
        pub fn iter(&self) -> TokioRwLockStream<'_, K, V, N> {
            TokioRwLockStream::new(self)
        }

        /// Returns a stream to iterate over mutable references to all elements of all shards.
        ///
        /// # DEADLOCKS
        ///
        /// While iterating, be sure there is no read- or write-guard around or it will deadlock.
        pub fn iter_mut(&self) -> TokioRwLockStreamMut<'_, K, V, N> {
            TokioRwLockStreamMut::new(self)
        }
    }

    impl<K: FlexMapKey, V, const N: usize> TokioMutexMap<K, V, N> {
        /// Acquire sole access to a shard.
        ///
        /// # DEADLOCKS
        ///
        /// Hold the guard as briefly as possible since all other acquisations of this lock
        /// on the same shard will block until the guard is dropped.
        pub async fn lock(&self, key: K) -> LockGuard<'_, K, V> {
            Guard::new(self.inner[key.index::<N>()].lock().await, key)
        }

        /// Try to acquire sole access to a shard. Fails if there already is a guard around.
        ///
        /// # DEADLOCKS
        ///
        /// Hold the guard as briefly as possible since all other acquisations of this lock
        /// on the same shard will block until the guard is dropped.
        pub fn try_lock(&self, key: K) -> Result<LockGuard<'_, K, V>, TryLockError> {
            Ok(Guard::new(self.inner[key.index::<N>()].try_lock()?, key))
        }

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

        /// Returns a stream to iterate over mutable references to all elements of all shards,
        /// same as `.iter_mut()`.
        ///
        /// # DEADLOCKS
        ///
        /// While iterating, be sure there is no guard around or it will deadlock.
        pub fn iter(&self) -> TokioMutexStream<'_, K, V, N> {
            self.iter_mut()
        }

        /// Returns a stream to iterate over mutable references to all elements of all shards.
        ///
        /// # DEADLOCKS
        ///
        /// While iterating, be sure there is no guard around or it will deadlock.
        pub fn iter_mut(&self) -> TokioMutexStream<'_, K, V, N> {
            TokioMutexStream::new(self)
        }
    }

    impl<K, V, const N: usize> Debug for TokioRwLockMap<K, V, N>
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

    impl<K, V, const N: usize> Debug for TokioMutexMap<K, V, N>
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

    impl_from_iter! {
        TokioRwLockMap: try_write unwrap,
        TokioMutexMap: try_lock unwrap,
    }
}
