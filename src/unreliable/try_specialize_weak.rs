use crate::unreliable::WeakSpecialization;
use crate::Specialization;

/// A extension trait for [`TrySpecialize`] trait for specializing one
/// completely unconstrained type to another completely unconstrained type.
///
/// This trait uses [`Specialization`] helper struct and [`WeakSpecialization`]
/// helper trait to perform all conversions. You can use [`Specialization`] and
/// [`WeakSpecialization`] directly if you need to perform more complex
/// specialization cases or to cache the specializable ability.
///
/// # Reliability
///
/// While it is unlikely, there is still a possibility that the methods of this
/// trait may return false negatives in future Rust versions.
///
/// The correctness of the results returned by the methods depends on the
/// following:
/// - Documented behavior that if `T` implements `Eq`, two `Rc`s that point to
///   the same allocation are always equal:
///   <https://doc.rust-lang.org/1.81.0/std/rc/struct.Rc.html#method.eq>.
/// - Undocumented behavior that the `Rc::partial_eq` implementation for `T: Eq`
///   will not use `PartialEq::eq` if both `Rc`s point to the same memory
///   location.
/// - The assumption that the undocumented short-circuit behavior described
///   above will be retained for optimization purposes.
///
/// There is no formal guarantee that the undocumented behavior described above
/// will be retained. If the implementation changes in a future Rust version,
/// the function may return a false negative, that is, it may return `false`,
/// even though `T` implements the trait. However, the implementation guarantees
/// that a false positive result is impossible, i.e., the function will never
/// return true if `T` does not implement the trait in any future Rust version.
///
/// Details:
/// - <https://internals.rust-lang.org/t/rc-uses-visibly-behavior-changing-specialization-is-that-okay/16173/6>,
/// - <https://users.rust-lang.org/t/hack-to-specialize-w-write-for-vec-u8/100366>,
/// - <https://doc.rust-lang.org/1.81.0/std/rc/struct.Rc.html#method.eq>,
/// - <https://github.com/rust-lang/rust/issues/42655>.
///
/// [`TrySpecialize`]: crate::TrySpecialize
pub trait TrySpecializeWeak {
    /// Attempts to specialize `Self` as `T` checking that underlying `Self`
    /// type implements [`LifetimeFree`].
    ///
    /// Returns `T` as `Self` wrapped in `Ok` if `Self` and `T` types are
    /// identical and [`impls_lifetime_free_weak::<Self>()`] check succeed.
    /// Otherwise, it returns `T` wrapped in `Err`.
    ///
    /// The [`LifetimeFree`] trait is **not** automatically derived for all
    /// lifetime-free types. The library only implements it for standard library
    /// types that do not have any lifetime parameters. Prefer to specialize to
    /// specific [`LifetimeFree`] type if possible with
    /// [`TrySpecialize::try_specialize`].
    ///
    /// [`LifetimeFree`]: crate::LifetimeFree
    /// [`TrySpecialize::try_specialize`]: crate::TrySpecialize::try_specialize
    /// [`impls_lifetime_free_weak::<Self>()`]: crate::unreliable::impls_lifetime_free_weak
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(all(feature = "alloc", feature = "unreliable"))] {
    /// use core::ops::Add;
    ///
    /// use try_specialize::unreliable::TrySpecializeWeak;
    ///
    /// fn add_if_same_ty_weak<T1, T2>(left: T1, right: T2) -> Result<T1, (T1, T2)>
    /// where
    ///     T1: Add<Output = T1>,
    /// {
    ///     match right.try_specialize_if_lifetime_free_weak() {
    ///         Ok(right) => Ok(left + right),
    ///         Err(right) => Err((left, right)),
    ///     }
    /// }
    ///
    /// assert_eq!(add_if_same_ty_weak(42_u32, 123_u32), Ok(165));
    /// assert_eq!(
    ///     add_if_same_ty_weak(123.456_f64, 123_u32),
    ///     Err((123.456_f64, 123_u32))
    /// );
    /// assert_eq!(
    ///     add_if_same_ty_weak(123.456_f64, 1000.111_f64),
    ///     Ok(1123.567_f64)
    /// );
    /// # }
    #[expect(clippy::missing_errors_doc, reason = "already described")]
    #[inline]
    fn try_specialize_if_lifetime_free_weak<T>(self) -> Result<T, Self>
    where
        Self: Sized,
    {
        if let Some(spec) = Specialization::try_new_if_lifetime_free_weak() {
            Ok(spec.specialize(self))
        } else {
            Err(self)
        }
    }

    /// Attempts to specialize `&Self` as `&T` checking that underlying `Self`
    /// type implements [`LifetimeFree`].
    ///
    /// The [`LifetimeFree`] trait is **not** automatically derived for all
    /// lifetime-free types. The library only implements it for standard library
    /// types that do not have any lifetime parameters. Prefer to specialize to
    /// specific [`LifetimeFree`] type if possible with
    /// [`TrySpecialize::try_specialize_ref`].
    ///
    /// [`LifetimeFree`]: crate::LifetimeFree
    /// [`TrySpecialize::try_specialize_ref`]: crate::TrySpecialize::try_specialize_ref
    /// [`impls_lifetime_free_weak::<Self>()`]: crate::unreliable::impls_lifetime_free_weak
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(all(feature = "alloc", feature = "unreliable"))] {
    /// use try_specialize::unreliable::TrySpecializeWeak;
    ///
    /// fn eq_if_same_ty_weak<T1, T2>(left: &T1, right: &T2) -> Option<bool>
    /// where
    ///     T1: PartialEq,
    /// {
    ///     right.
    ///         try_specialize_ref_if_lifetime_free_weak().
    ///         map(|right| left == right)
    /// }
    ///
    /// assert_eq!(eq_if_same_ty_weak(&42_u32, &42_u32), Some(true));
    /// assert_eq!(eq_if_same_ty_weak(&42_u32, &123_u32), Some(false));
    /// assert_eq!(eq_if_same_ty_weak(&123.456_f64, &123_u32), None);
    /// # }
    #[inline]
    fn try_specialize_ref_if_lifetime_free_weak<T>(&self) -> Option<&T>
    where
        T: ?Sized,
    {
        Specialization::try_new_if_lifetime_free_weak().map(|spec| spec.specialize_ref(self))
    }

    /// Attempts to specialize `&mut Self` as `&mut T` checking that underlying
    /// `Self` type implements [`LifetimeFree`].
    ///
    /// The [`LifetimeFree`] trait is **not** automatically derived for all
    /// lifetime-free types. The library only implements it for standard library
    /// types that do not have any lifetime parameters. Prefer to specialize to
    /// specific [`LifetimeFree`] type if possible with
    /// [`TrySpecialize::try_specialize_mut`].
    ///
    /// [`LifetimeFree`]: crate::LifetimeFree
    /// [`TrySpecialize::try_specialize_mut`]: crate::TrySpecialize::try_specialize_mut
    /// [`impls_lifetime_free_weak::<Self>()`]: crate::unreliable::impls_lifetime_free_weak
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(all(feature = "alloc", feature = "unreliable"))] {
    /// use core::ops::AddAssign;
    ///
    /// use try_specialize::unreliable::TrySpecializeWeak;
    ///
    /// fn transfer_if_same_ty_weak<T1, T2>(left: &mut T1, right: &mut T2) -> bool
    /// where
    ///     T1: AddAssign + Default,
    /// {
    ///     match right.try_specialize_mut_if_lifetime_free_weak() {
    ///         Some(right) => {
    ///             *left += core::mem::take(right);
    ///             true
    ///         },
    ///         None => false,
    ///     }
    /// }
    ///
    /// let mut v1: u32 = 10;
    /// let mut v2: f64 = 20.0;
    /// let mut v3: u32 = 40;
    /// let mut v4: f64 = 80.0;
    ///
    /// assert_eq!(transfer_if_same_ty_weak(&mut v1, &mut v2), false);
    /// assert_eq!((v1, v2, v3, v4), (10, 20.0, 40, 80.0));
    /// assert_eq!(transfer_if_same_ty_weak(&mut v1, &mut v3), true);
    /// assert_eq!((v1, v2, v3, v4), (50, 20.0, 0, 80.0));
    /// assert_eq!(transfer_if_same_ty_weak(&mut v1, &mut v4), false);
    /// assert_eq!((v1, v2, v3, v4), (50, 20.0, 0, 80.0));
    /// assert_eq!(transfer_if_same_ty_weak(&mut v2, &mut v3), false);
    /// assert_eq!((v1, v2, v3, v4), (50, 20.0, 0, 80.0));
    /// assert_eq!(transfer_if_same_ty_weak(&mut v2, &mut v4), true);
    /// assert_eq!((v1, v2, v3, v4), (50, 100.0, 0, 0.0));
    /// # }
    #[inline]
    fn try_specialize_mut_if_lifetime_free_weak<T>(&mut self) -> Option<&mut T>
    where
        T: ?Sized,
    {
        Specialization::try_new_if_lifetime_free_weak().map(|spec| spec.specialize_mut(self))
    }
}

impl<T> TrySpecializeWeak for T where T: ?Sized {}

#[cfg(test)]
mod tests {
    #[cfg(feature = "alloc")]
    use crate::unreliable::TrySpecializeWeak;

    #[cfg(feature = "alloc")]
    #[test]
    fn test_try_specialize_if_lifetime_free() {
        fn try_spec_erased<T1, T2>(value: T1) -> Result<T2, T1> {
            value.try_specialize_if_lifetime_free_weak()
        }

        assert_eq!(try_spec_erased::<_, u32>(123_u32), Ok(123_u32));
        assert_eq!(try_spec_erased::<_, i32>(123_u32), Err(123_u32));

        assert_eq!(try_spec_erased::<_, u32>("abc"), Err("abc"));
        // '&'static str' is not [`LifetimeFree`] so the specialization failed
        // as expected even if the types are equal.
        assert_eq!(try_spec_erased::<_, &'static str>("abc"), Err("abc"));
    }
}
