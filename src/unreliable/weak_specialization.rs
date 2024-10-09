use crate::unreliable::impls_lifetime_free_weak;
use crate::{type_eq_ignore_lifetimes, Specialization};

/// A extension trait for [`Specialization`] type for specializing one
/// completely unconstrained type to another completely unconstrained type.
///
/// # Reliability
///
/// While it is unlikely, there is still a possibility that functions of this
/// module future will returning false negatives in the future Rust versions.
///
/// The correctness of the returned result of the function depends on
/// the following:
/// - Documented behavior that if `T` implements `Eq`, two `Rc`s that
///   point to the same allocation are always equal:
///   <https://doc.rust-lang.org/1.81.0/std/rc/struct.Rc.html#method.eq>.
/// - Undocumented behavior that the implementation of `Rc::partial_eq` for `T:
///   Eq` will not `PartialEq::eq` if both `Rc`s point to the same allocation.
/// - Assumption that the undocumented short-circuit behavior described above
///   will be retained for optimization purposes.
///
/// There is no formal guarantee that the undocumented behavior
/// described above will be retained. If the implementation is changed
/// in a future Rust version, the function may return a false negative,
/// that is, return `false`, even though `T` implements the trait.
/// However, the implementation guarantees that a false positive result
/// is impossible, i.e., the function will never return true if `T` does
/// not implement the trait in any future Rust version.
///
/// Details:
/// - <https://internals.rust-lang.org/t/rc-uses-visibly-behavior-changing-specialization-is-that-okay/16173/6>,
/// - <https://users.rust-lang.org/t/hack-to-specialize-w-write-for-vec-u8/100366>,
/// - <https://doc.rust-lang.org/1.81.0/std/rc/struct.Rc.html#method.eq>,
/// - <https://github.com/rust-lang/rust/issues/42655>.
pub trait WeakSpecialization: Sized {
    /// Checks the types `T1` and `T2` for equality and returns the
    /// specialization provider if types implement `LifetimeFree` and the types
    /// are equal.
    ///
    /// Note that `LifetimeFree` is not automatically derived and implemented
    /// only for a set of types without lifetimes. This function uses
    /// `impls_lifetime_free` to check wherever the unconstrained type
    /// implements `LifetimeFree` trait or not.
    #[must_use]
    fn try_new_if_lifetime_free_weak() -> Option<Self>;
}

#[cfg(feature = "alloc")]
impl<T1, T2> WeakSpecialization for Specialization<T1, T2>
where
    T1: ?Sized,
    T2: ?Sized,
{
    #[inline]
    fn try_new_if_lifetime_free_weak() -> Option<Self> {
        (impls_lifetime_free_weak::<T1>() && type_eq_ignore_lifetimes::<T1, T2>())
            // SAFETY: `T1` can be specialized to `T2` if the types are equal with
            // erased lifetime and any of it implements `NoLifetime` trait.
            .then_some(unsafe { Self::new_unchecked() })
    }
}
