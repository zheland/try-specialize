//! This module contains a set of functions, traits and macros which depend on
//! undocumented stdlib behavior and should therefore be used with caution.
//!
//! Library tests ensure that the `impls_trait` checks are fully optimized and
//! become zero-cost with `opt-level >= 1`. Note that release profile uses
//! `opt-level = 3` by default.
//!
//! # Reliability
//!
//! While it is unlikely, there is still a possibility that functions of this
//! module future will returning false negatives in the future Rust versions.
//!
//! The correctness of the returned result of the functions depends on
//! the following:
//! - Documented behavior that if `T` implements `Eq`, two `Rc`s that
//!   point to the same allocation are always equal:
//!   <https://doc.rust-lang.org/1.81.0/std/rc/struct.Rc.html#method.eq>.
//! - Undocumented behavior that the `Rc::partial_eq` implementation for `T: Eq`
//!   will not use `PartialEq::eq` if both `Rc`s point to the same memory
//!   location.
//! - Assumption that the undocumented short-circuit behavior described above
//!   will be retained for optimization purposes.
//!
//! There is no formal guarantee that the undocumented behavior
//! described above will be retained. If the implementation is changed
//! in a future Rust version, the function may return a false negative,
//! that is, return `false`, even though `T` implements the trait.
//! However, the implementation guarantees that a false positive result
//! is impossible, i.e., the function will never return true if `T` does
//! not implement the trait in any future Rust version.
//!
//! Details:
//! - <https://internals.rust-lang.org/t/rc-uses-visibly-behavior-changing-specialization-is-that-okay/16173/6>,
//! - <https://users.rust-lang.org/t/hack-to-specialize-w-write-for-vec-u8/100366>,
//! - <https://doc.rust-lang.org/1.81.0/std/rc/struct.Rc.html#method.eq>,
//! - <https://github.com/rust-lang/rust/issues/42655>.

mod impls_trait;
mod try_specialize_weak;
mod weak_specialization;

pub use impls_trait::*;
pub use try_specialize_weak::*;
pub use weak_specialization::*;