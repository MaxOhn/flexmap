use ::std::{
    ops::{Deref, DerefMut},
    sync::Arc,
};

use hashbrown::hash_map::{Iter, IterMut};

#[cfg(feature = "std")]
pub use self::std::{StdMutexIter, StdRwLockIter, StdRwLockIterMut};

#[cfg(feature = "tokio")]
pub use self::tokio::{TokioMutexStream, TokioRwLockStream, TokioRwLockStreamMut};

unsafe fn change_lifetime<'a, 'b, T>(v: &'a T) -> &'b T {
    ::std::mem::transmute(v)
}

unsafe fn change_lifetime_mut<'a, 'b, T>(v: &'a mut T) -> &'b mut T {
    ::std::mem::transmute(v)
}

#[derive(Debug)]
struct GuardIter<'map, G, K, V> {
    guard: Arc<G>,
    iter: Iter<'map, K, V>,
}

impl<'map, G, K, V> GuardIter<'map, G, K, V> {
    fn new(guard: G, iter: Iter<'map, K, V>) -> Self {
        Self {
            guard: Arc::new(guard),
            iter,
        }
    }
}

#[derive(Debug)]
struct GuardIterMut<'map, G, K, V> {
    guard: Arc<G>,
    iter: IterMut<'map, K, V>,
}

impl<'map, G, K, V> GuardIterMut<'map, G, K, V> {
    fn new(guard: G, iter: IterMut<'map, K, V>) -> Self {
        Self {
            guard: Arc::new(guard),
            iter,
        }
    }
}

/// A guard over an iterator item that is generic over the lock type.
///
/// Be sure to hold these as briefly as possible to avoid deadlocking yourself.
#[derive(Debug)]
pub struct Ref<G, K, V> {
    _guard: Arc<G>,
    key: *const K,
    value: *const V,
}

impl<G, K, V> Ref<G, K, V> {
    fn new(_guard: Arc<G>, key: *const K, value: *const V) -> Self {
        Self { _guard, key, value }
    }

    /// Returns the key of the entry.
    #[inline]
    pub fn key(&self) -> &K {
        unsafe { &*self.key }
    }

    /// Returns the value of the entry.
    #[inline]
    pub fn value(&self) -> &V {
        unsafe { &*self.value }
    }
}

impl<G, K, V> Deref for Ref<G, K, V> {
    type Target = V;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.value()
    }
}

/// A write-guard over an iterator item that is generic over the lock type.
///
/// Be sure to hold these as briefly as possible to avoid deadlocking yourself.
#[derive(Debug)]
pub struct RefMut<G, K, V> {
    _guard: Arc<G>,
    key: *const K,
    value: *mut V,
}

impl<G, K, V> RefMut<G, K, V> {
    fn new(_guard: Arc<G>, key: *const K, value: *mut V) -> Self {
        Self { _guard, key, value }
    }

    /// Returns the key of the entry.
    #[inline]
    pub fn key(&self) -> &K {
        unsafe { &*self.key }
    }

    /// Returns the value of the entry.
    #[inline]
    pub fn value(&self) -> &V {
        unsafe { &*self.value }
    }

    /// Returns a mutable reference to the value of the entry.
    #[inline]
    pub fn value_mut(&mut self) -> &mut V {
        unsafe { &mut *self.value }
    }
}

impl<G, K, V> Deref for RefMut<G, K, V> {
    type Target = V;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.value()
    }
}

impl<G, K, V> DerefMut for RefMut<G, K, V> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.value_mut()
    }
}

#[cfg(feature = "std")]
mod std {
    use std::sync::{Arc, MutexGuard, RwLockReadGuard, RwLockWriteGuard};

    use hashbrown::HashMap;

    use crate::std::{StdMutexMap, StdRwLockMap};

    use super::{GuardIter, GuardIterMut, Ref, RefMut};

    type ReadGuardIter<'map, K, V, S> =
        GuardIter<'map, RwLockReadGuard<'map, HashMap<K, V, S>>, K, V>;

    #[derive(Debug)]
    /// An iterator over references of entries of a [`StdRwLockMap`].
    pub struct StdRwLockIter<'map, K, V, S> {
        map: &'map StdRwLockMap<K, V, S>,
        curr_idx: usize,
        curr: Option<ReadGuardIter<'map, K, V, S>>,
    }

    impl<'map, K, V, S> StdRwLockIter<'map, K, V, S> {
        pub(crate) fn new(map: &'map StdRwLockMap<K, V, S>) -> Self {
            Self {
                map,
                curr_idx: 0,
                curr: None,
            }
        }
    }

    impl<'map, K, V, S> Iterator for StdRwLockIter<'map, K, V, S> {
        type Item = Ref<RwLockReadGuard<'map, HashMap<K, V, S>>, K, V>;

        fn next(&mut self) -> Option<Self::Item> {
            loop {
                if let Some(curr) = self.curr.as_mut() {
                    if let Some((key, value)) = curr.iter.next() {
                        let guard = Arc::clone(&curr.guard);

                        return Some(Ref::new(guard, key, value));
                    }
                }

                let guard = match self.map.inner.get(self.curr_idx) {
                    Some(lock) => lock.read().expect("RwLock poisoned"),
                    None => {
                        self.curr.take();

                        return None;
                    }
                };

                let iter = unsafe { super::change_lifetime(&guard) }.iter();

                self.curr = Some(GuardIter::new(guard, iter));
                self.curr_idx += 1;
            }
        }

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            self.curr
                .as_ref()
                .map(|guard| guard.iter.size_hint())
                .map(|(min, _)| (min, (self.curr_idx == self.map.inner.len()).then_some(min)))
                .unwrap_or((0, None))
        }
    }

    type WriteGuardIter<'map, K, V, S> =
        GuardIterMut<'map, RwLockWriteGuard<'map, HashMap<K, V, S>>, K, V>;

    #[derive(Debug)]
    /// An iterator over mutable references of entries of a [`StdRwLockMap`].
    pub struct StdRwLockIterMut<'map, K, V, S> {
        map: &'map StdRwLockMap<K, V, S>,
        curr_idx: usize,
        curr: Option<WriteGuardIter<'map, K, V, S>>,
    }

    impl<'map, K, V, S> StdRwLockIterMut<'map, K, V, S> {
        pub(crate) fn new(map: &'map StdRwLockMap<K, V, S>) -> Self {
            Self {
                map,
                curr_idx: 0,
                curr: None,
            }
        }
    }

    impl<'map, K, V, S> Iterator for StdRwLockIterMut<'map, K, V, S> {
        type Item = RefMut<RwLockWriteGuard<'map, HashMap<K, V, S>>, K, V>;

        fn next(&mut self) -> Option<Self::Item> {
            loop {
                if let Some(curr) = self.curr.as_mut() {
                    if let Some((key, value)) = curr.iter.next() {
                        let guard = Arc::clone(&curr.guard);

                        return Some(RefMut::new(guard, key, value));
                    }
                }

                let mut guard = match self.map.inner.get(self.curr_idx) {
                    Some(lock) => lock.write().expect("RwLock poisoned"),
                    None => {
                        self.curr.take();

                        return None;
                    }
                };

                let iter = unsafe { super::change_lifetime_mut(&mut guard) }.iter_mut();

                self.curr = Some(GuardIterMut::new(guard, iter));
                self.curr_idx += 1;
            }
        }

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            self.curr
                .as_ref()
                .map(|guard| guard.iter.size_hint())
                .map(|(min, _)| (min, (self.curr_idx == self.map.inner.len()).then_some(min)))
                .unwrap_or((0, None))
        }
    }

    type MutexGuardIter<'map, K, V, S> =
        GuardIterMut<'map, MutexGuard<'map, HashMap<K, V, S>>, K, V>;

    #[derive(Debug)]
    /// An iterator over references of entries of a [`StdMutexMap`].
    pub struct StdMutexIter<'map, K, V, S> {
        map: &'map StdMutexMap<K, V, S>,
        curr_idx: usize,
        curr: Option<MutexGuardIter<'map, K, V, S>>,
    }

    impl<'map, K, V, S> StdMutexIter<'map, K, V, S> {
        pub(crate) fn new(map: &'map StdMutexMap<K, V, S>) -> Self {
            Self {
                map,
                curr_idx: 0,
                curr: None,
            }
        }
    }

    impl<'map, K, V, S> Iterator for StdMutexIter<'map, K, V, S> {
        type Item = RefMut<MutexGuard<'map, HashMap<K, V, S>>, K, V>;

        fn next(&mut self) -> Option<Self::Item> {
            loop {
                if let Some(curr) = self.curr.as_mut() {
                    if let Some((key, value)) = curr.iter.next() {
                        let guard = Arc::clone(&curr.guard);

                        return Some(RefMut::new(guard, key, value));
                    }
                }

                let mut guard = match self.map.inner.get(self.curr_idx) {
                    Some(lock) => lock.lock().expect("Mutex poisoned"),
                    None => {
                        self.curr.take();

                        return None;
                    }
                };

                let iter = unsafe { super::change_lifetime_mut(&mut guard) }.iter_mut();

                self.curr = Some(GuardIterMut::new(guard, iter));
                self.curr_idx += 1;
            }
        }

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            self.curr
                .as_ref()
                .map(|guard| guard.iter.size_hint())
                .map(|(min, _)| (min, (self.curr_idx == self.map.inner.len()).then_some(min)))
                .unwrap_or((0, None))
        }
    }
}

#[cfg(feature = "tokio")]
mod tokio {
    use std::{
        pin::Pin,
        sync::Arc,
        task::{Context, Poll},
    };

    use futures::Stream;
    use hashbrown::HashMap;
    use tokio::sync::{MutexGuard, RwLockReadGuard, RwLockWriteGuard};

    use crate::tokio::{TokioMutexMap, TokioRwLockMap};

    use super::{GuardIter, GuardIterMut, Ref, RefMut};

    type ReadGuardIter<'map, K, V, S> =
        GuardIter<'map, RwLockReadGuard<'map, HashMap<K, V, S>>, K, V>;

    #[derive(Debug)]
    /// A stream  over references of entries of a [`TokioRwLockMap`].
    pub struct TokioRwLockStream<'map, K, V, S> {
        map: &'map TokioRwLockMap<K, V, S>,
        curr_idx: usize,
        curr: Option<ReadGuardIter<'map, K, V, S>>,
    }

    impl<'map, K, V, S> TokioRwLockStream<'map, K, V, S> {
        pub(crate) fn new(map: &'map TokioRwLockMap<K, V, S>) -> Self {
            Self {
                map,
                curr_idx: 0,
                curr: None,
            }
        }
    }

    impl<'map, K, V, S> Stream for TokioRwLockStream<'map, K, V, S> {
        type Item = Ref<RwLockReadGuard<'map, HashMap<K, V, S>>, K, V>;

        fn poll_next(mut self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<Option<Self::Item>> {
            loop {
                if let Some(curr) = self.curr.as_mut() {
                    if let Some((key, value)) = curr.iter.next() {
                        let guard = Arc::clone(&curr.guard);

                        return Poll::Ready(Some(Ref::new(guard, key, value)));
                    }
                }

                let guard = match self.map.inner.get(self.curr_idx) {
                    Some(lock) => match lock.try_read() {
                        Ok(guard) => guard,
                        Err(_) => return Poll::Pending,
                    },
                    None => {
                        self.curr.take();

                        return Poll::Ready(None);
                    }
                };

                let iter = unsafe { super::change_lifetime(&guard) }.iter();

                self.curr = Some(GuardIter::new(guard, iter));
                self.curr_idx += 1;
            }
        }
    }

    type WriteGuardIter<'map, K, V, S> =
        GuardIterMut<'map, RwLockWriteGuard<'map, HashMap<K, V, S>>, K, V>;

    #[derive(Debug)]
    /// A stream  over mutable references of entries of a [`TokioRwLockMap`].
    pub struct TokioRwLockStreamMut<'map, K, V, S> {
        map: &'map TokioRwLockMap<K, V, S>,
        curr_idx: usize,
        curr: Option<WriteGuardIter<'map, K, V, S>>,
    }

    impl<'map, K, V, S> TokioRwLockStreamMut<'map, K, V, S> {
        pub(crate) fn new(map: &'map TokioRwLockMap<K, V, S>) -> Self {
            Self {
                map,
                curr_idx: 0,
                curr: None,
            }
        }
    }

    impl<'map, K, V, S> Stream for TokioRwLockStreamMut<'map, K, V, S> {
        type Item = RefMut<RwLockWriteGuard<'map, HashMap<K, V, S>>, K, V>;

        fn poll_next(mut self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<Option<Self::Item>> {
            loop {
                if let Some(curr) = self.curr.as_mut() {
                    if let Some((key, value)) = curr.iter.next() {
                        let guard = Arc::clone(&curr.guard);

                        return Poll::Ready(Some(RefMut::new(guard, key, value)));
                    }
                }

                let mut guard = match self.map.inner.get(self.curr_idx) {
                    Some(lock) => match lock.try_write() {
                        Ok(guard) => guard,
                        Err(_) => return Poll::Pending,
                    },
                    None => {
                        self.curr.take();

                        return Poll::Ready(None);
                    }
                };

                let iter = unsafe { super::change_lifetime_mut(&mut guard) }.iter_mut();

                self.curr = Some(GuardIterMut::new(guard, iter));
                self.curr_idx += 1;
            }
        }

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            self.curr
                .as_ref()
                .map(|guard| guard.iter.size_hint())
                .map(|(min, _)| (min, (self.curr_idx == self.map.inner.len()).then_some(min)))
                .unwrap_or((0, None))
        }
    }

    type MutexGuardIter<'map, K, V, S> =
        GuardIterMut<'map, MutexGuard<'map, HashMap<K, V, S>>, K, V>;

    #[derive(Debug)]
    /// A stream  over mutable references of entries of a [`TokioMutexMap`].
    pub struct TokioMutexStream<'map, K, V, S> {
        map: &'map TokioMutexMap<K, V, S>,
        curr_idx: usize,
        curr: Option<MutexGuardIter<'map, K, V, S>>,
    }

    impl<'map, K, V, S> TokioMutexStream<'map, K, V, S> {
        pub(crate) fn new(map: &'map TokioMutexMap<K, V, S>) -> Self {
            Self {
                map,
                curr_idx: 0,
                curr: None,
            }
        }
    }

    impl<'map, K, V, S> Stream for TokioMutexStream<'map, K, V, S> {
        type Item = RefMut<MutexGuard<'map, HashMap<K, V, S>>, K, V>;

        fn poll_next(mut self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<Option<Self::Item>> {
            loop {
                if let Some(curr) = self.curr.as_mut() {
                    if let Some((key, value)) = curr.iter.next() {
                        let guard = Arc::clone(&curr.guard);

                        return Poll::Ready(Some(RefMut::new(guard, key, value)));
                    }
                }

                let mut guard = match self.map.inner.get(self.curr_idx) {
                    Some(lock) => match lock.try_lock() {
                        Ok(guard) => guard,
                        Err(_) => return Poll::Pending,
                    },
                    None => {
                        self.curr.take();

                        return Poll::Ready(None);
                    }
                };

                let iter = unsafe { super::change_lifetime_mut(&mut guard) }.iter_mut();

                self.curr = Some(GuardIterMut::new(guard, iter));
                self.curr_idx += 1;
            }
        }

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            self.curr
                .as_ref()
                .map(|guard| guard.iter.size_hint())
                .map(|(min, _)| (min, (self.curr_idx == self.map.inner.len()).then_some(min)))
                .unwrap_or((0, None))
        }
    }
}
