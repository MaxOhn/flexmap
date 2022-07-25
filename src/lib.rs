//! # FlexMap
//!
//! A highly flexible concurrent map with a similar approach as [DashMap](https://github.com/xacrimon/dashmap).
//!
//! ## Comparison
//!
//! The _ of FlexMap compared to DashMap:
//!   - Disadvantage:
//!     - Interface is very different than the one from the standard library's HashMap.
//!     - The index for the internal hashmap is determined by the keys instead of threads,
//!     hence the key type needs to implement a specific trait, namely `FlexMapKey`. By
//!     default, this trait is only implemented for integers by simple taking a modulo but it
//!     can easily be implemented for any other type.
//!     - Instead of allowing types that borrow into the key type, methods on FlexMap really do
//!     need the key type itself.
//!     - Most definitely not faster than DashMap, likely a little slower even. I did not
//!     benchmark yet.
//!   - Advantages:
//!     - Instead of always using a synchronous mutex, the internal locks are **flex**ible so
//!     that any lock can be added. By default, provided locks are both RwLock and Mutex from
//!     both the standard library and [tokio](https://docs.rs/tokio/latest/tokio/).
//!     - Instead of basing the amount of internal hashmaps on the amount of CPU cores, the
//!     amount is **flex**ible and can be chosen as a const generic. The more maps, the lower the
//!     likelyhood of deadlocking. Defaults to 10 on the provided default locks.
//!     - Due to the different interface, the user has full control over locks and their
//!     guards, thus shifting the responsibility to not deadlock on the user instead of
//!     internal machinery.
//!
//! ## Why
//!
//! Despite all my efforts to be as mindful as possible about tight scopes and DashMap accesses, I
//! still managed to deadlock myself a lot more than I deemed acceptable.
//! With FlexMap, there is no more internal shenanigans to blame, only me and my improper usage of
//! the map.
//!
//! Alternatively to DashMap, there is also [flurry](https://github.com/jonhoo/flurry)'s hashmap
//! which is amazing in its own domain but falls a little short when it comes to write-heavy usages
//! and even impossible to use in highly asynchronous applications. Since FlexMap uses a similar
//! principle as DashMap and DashMap performs very well on both read- and write-heavy usages,
//! FlexMap is expected to hold up in that department too. And since FlexMap is generic over the
//! lock type, using tokio's Mutex or RwLock integrates nicely into otherwise asynchronous code.
//!
//! ## Which map to use
//!
//! By default, there are four kinds of FlexMaps provided: `StdRwLockMap`, `StdMutexMap`,
//! `TokioRwLockMap`, and `TokioMutexMap`, each using either a Mutex or RwLock from either the
//! standard library or tokio. But which one should you use?
//!
//! Bad news: you'll have to figure out which one fits your situation the best.
//!
//! Good news: you get to pick the one that performs the best in your situation.
//!
//! It's generally not that hard to decide though:
//!   - Do you use a lot of async? Specifically, would you hold guards into the map across
//!   `.await` points? If yes, pick a tokio map.
//!   - Is the amount of times you read from the map significantly higher than the amount of
//!   times you write to it / modify entries? If yes, pick an RwLock map.
//!   - Are reads and writes happening roughly equally, are you unsure about it, or are there
//!   definitely more writes? Pick a Mutex map.
//!
//! ## Notes
//!
//! My main focus was to give me and only me an alternative to DashMap.
//! Hence, I've only put the bare minimum of effort into documentation and anything other that
//! people could expect. Examples are missing, it hasn't been benchmarked, and worst of all, I
//! haven't added any internal tests. As such, I'm not even comfortable enough to publish yet.
//!
//! I'm just using this in other projects of mine and haven't encountered any issues yet. I'll
//! likely polish FlexMap once I have time.
//!
//! ## Features
//!
//! |Feature   | Description                                   | Dependencies|
//! |----------|-----------------------------------------------|-------------|
//! |`default` | Enables the `std` and `tokio` feature         | [tokio](https://github.com/tokio-rs/tokio), [futures](https://github.com/rust-lang/futures-rs)|
//! |`std`     | Provides `StdRwLockMap` and `StdMutexMap`     | None|
//! |`tokio`   | Provides `TokioRwLockMap` and `TokioMutexMap` | [tokio](https://github.com/tokio-rs/tokio), [futures](https://github.com/rust-lang/futures-rs)|

#![deny(
    clippy::all,
    nonstandard_style,
    rust_2018_idioms,
    unused,
    warnings,
    missing_debug_implementations,
    missing_docs
)]

pub use self::{
    guard::Guard,
    iter::{Ref, RefMut},
    key::FlexMapKey,
    map::FlexMap,
};

mod guard;
mod iter;
mod key;
mod map;

/// Trait to help [`FlexMap`] determine the type of the inner locks.
pub trait MapLock<M> {
    /// The actual lock type that wraps [`FlexMap`]'s internal hashmaps.
    type Lock;
}

#[cfg(feature = "std")]
/// All types around the standard library's Mutex and RwLock.
pub mod std {
    pub use super::{
        iter::{StdMutexIter, StdRwLockIter, StdRwLockIterMut},
        map::{StdMutexMap, StdMutexMarker, StdRwLockMap, StdRwLockMarker},
    };
}

#[cfg(feature = "tokio")]
/// All types around tokio's Mutex and RwLock.
pub mod tokio {
    pub use super::{
        iter::{TokioMutexStream, TokioRwLockStream, TokioRwLockStreamMut},
        map::{TokioMutexMap, TokioMutexMarker, TokioRwLockMap, TokioRwLockMarker},
    };
}
