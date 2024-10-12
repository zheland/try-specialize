use core::any::TypeId;
use core::marker::PhantomData;

use crate::LifetimeFree;

/// Returns `true` if the `T1` and `T2` types are equal.
///
/// This method requires only `T2` to implement [`LifetimeFree`] trait.
///
/// Library tests ensure that type comparisons are performed at compile time and
/// are fully optimized with no runtime cost at `opt-level >= 1`. Note that the
/// release profile uses `opt-level = 3` by default.
///
/// [`LifetimeFree`]: crate::LifetimeFree
///
/// # Examples
///
/// ```rust
/// use try_specialize::type_eq;
///
/// assert!(type_eq::<(), ()>());
/// assert!(!type_eq::<(), u8>());
///
/// assert!(type_eq::<u8, u8>());
/// assert!(!type_eq::<u8, u32>());
///
/// assert!(type_eq::<[u8], [u8]>());
/// assert!(type_eq::<[u8; 8], [u8; 8]>());
/// assert!(!type_eq::<[u8; 8], [u8]>());
/// assert!(!type_eq::<[u8], [u8; 8]>());
/// assert!(!type_eq::<[u8; 8], [u8; 16]>());
///
/// assert!(type_eq::<str, str>());
/// assert!(type_eq::<[u8], [u8]>());
/// assert!(!type_eq::<str, [u8]>());
/// assert!(!type_eq::<[u8], [u8; 4]>());
///
/// # #[cfg(feature = "alloc")]
/// assert!(type_eq::<String, String>());
/// ```
#[inline]
#[must_use]
pub fn type_eq<T1, T2>() -> bool
where
    T1: ?Sized,
    T2: ?Sized + LifetimeFree,
{
    type_eq_ignore_lifetimes::<T1, T2>()
}

/// Returns `true` if the `T1` and `T2` static types are equal.
///
/// This method requires both `T1` and `T2` to be `'static`.
///
/// Library tests ensure that type comparisons are performed at compile time and
/// are fully optimized with no runtime cost at `opt-level >= 1`. Note that the
/// release profile uses `opt-level = 3` by default.
///
/// # Examples
///
/// ```rust
/// use try_specialize::static_type_eq;
///
/// fn static_type_eq_of_vals<T1: 'static, T2: 'static>(_: T1, _: T2) -> bool {
///     static_type_eq::<T1, T2>()
/// }
///
/// assert!(static_type_eq::<(), ()>());
/// assert!(!static_type_eq::<(), u8>());
///
/// assert!(static_type_eq::<u8, u8>());
/// assert!(!static_type_eq::<u8, u32>());
///
/// assert!(static_type_eq::<[u8], [u8]>());
/// assert!(static_type_eq::<[u8; 8], [u8; 8]>());
/// assert!(!static_type_eq::<[u8; 8], [u8]>());
/// assert!(!static_type_eq::<[u8], [u8; 8]>());
/// assert!(!static_type_eq::<[u8; 8], [u8; 16]>());
///
/// assert!(static_type_eq::<&'static str, &'static str>());
/// assert!(static_type_eq_of_vals("foo", "bar"));
///
/// assert!(static_type_eq::<str, str>());
/// assert!(static_type_eq::<[u8], [u8]>());
/// assert!(!static_type_eq::<str, [u8]>());
/// assert!(!static_type_eq::<[u8], [u8; 4]>());
///
/// # #[cfg(feature = "alloc")]
/// assert!(static_type_eq::<String, String>());
/// ```
#[inline]
#[must_use]
pub fn static_type_eq<T1, T2>() -> bool
where
    T1: ?Sized + 'static,
    T2: ?Sized + 'static,
{
    TypeId::of::<T1>() == TypeId::of::<T2>()
}

/// Returns `true` if the `Self` and `T` types are equal ignoring their
/// lifetimes.
///
/// Note that all the lifetimes are erased and not accounted for.
///
/// Library tests ensure that type comparisons are performed at compile time and
/// are fully optimized with no runtime cost at `opt-level >= 1`. Note that the
/// release profile uses `opt-level = 3` by default.
///
/// # Examples
///
/// ```rust
/// use core::hint::black_box;
///
/// use try_specialize::type_eq_ignore_lifetimes;
///
/// const STATIC_STR: &'static str = "foo";
///
/// assert!(type_eq_ignore_lifetimes::<(), ()>());
/// assert!(!type_eq_ignore_lifetimes::<(), u8>());
///
/// assert!(type_eq_ignore_lifetimes::<u8, u8>());
/// assert!(!type_eq_ignore_lifetimes::<u8, u32>());
///
/// assert!(type_eq_ignore_lifetimes::<[u8], [u8]>());
/// assert!(type_eq_ignore_lifetimes::<[u8; 8], [u8; 8]>());
/// assert!(!type_eq_ignore_lifetimes::<[u8; 8], [u8]>());
/// assert!(!type_eq_ignore_lifetimes::<[u8], [u8; 8]>());
/// assert!(!type_eq_ignore_lifetimes::<[u8; 8], [u8; 16]>());
///
/// assert!(type_eq_ignore_lifetimes::<str, str>());
/// assert!(type_eq_ignore_lifetimes::<[u8], [u8]>());
/// assert!(!type_eq_ignore_lifetimes::<str, [u8]>());
/// assert!(!type_eq_ignore_lifetimes::<[u8], [u8; 4]>());
///
/// assert!(type_eq_ignore_lifetimes::<&'static str, &'static str>());
/// assert!(type_eq_ignore_lifetimes_of_vals("foo", "bar"));
/// assert!(type_eq_ignore_lifetimes_of_vals(
///     STATIC_STR,
///     format!("bar").as_str()
/// ));
///
/// # #[cfg(feature = "alloc")]
/// scoped_test();
///
/// # #[cfg(feature = "alloc")]
/// fn scoped_test() {
///     let local_str = format!("{}{}", black_box("foo"), black_box("bar"));
///     let local_str = local_str.as_str(); // Non-static str.
///     assert!(type_eq_ignore_lifetimes_of_vals(STATIC_STR, local_str));
/// }
///
/// fn type_eq_ignore_lifetimes_of_vals<T1, T2>(_: T1, _: T2) -> bool {
///     type_eq_ignore_lifetimes::<T1, T2>()
/// }
/// ```
#[inline]
#[must_use]
pub fn type_eq_ignore_lifetimes<T1, T2>() -> bool
where
    T1: ?Sized,
    T2: ?Sized,
{
    non_static_type_id::<T1>() == non_static_type_id::<T2>()
}

/// Returns the `TypeId` of the type this generic function has been instantiated
/// with ignoring lifetimes.
///
/// Based on original implementation written by @dtolnay:
/// <https://github.com/rust-lang/rust/issues/41875#issuecomment-317292888>
///
/// # Safety
///
/// This function doesn't validate type lifetimes. Lifetimes must be validated
/// separately.
#[inline]
#[must_use]
fn non_static_type_id<T>() -> TypeId
where
    T: ?Sized,
{
    trait NonStaticAny {
        fn get_type_id(&self) -> TypeId
        where
            Self: 'static;
    }

    impl<T> NonStaticAny for PhantomData<T>
    where
        T: ?Sized,
    {
        #[inline]
        fn get_type_id(&self) -> TypeId
        where
            Self: 'static,
        {
            TypeId::of::<T>()
        }
    }

    // SAFETY: Types differs only by lifetimes. Lifetimes are the compile-time
    // feature and are completely erased before the code generation stage.
    // The transmuted type is only used to get its id and does not outlive the
    // `get_type_id` function.
    NonStaticAny::get_type_id(unsafe {
        core::mem::transmute::<&dyn NonStaticAny, &(dyn NonStaticAny + 'static)>(&PhantomData::<T>)
    })
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "alloc")]
    use alloc::string::String;
    use core::cell::Ref;
    use core::hint::black_box;

    use crate::type_eq_ignore_lifetimes;

    fn type_eq_ignore_lifetimes_of_vals<T1, T2>(_: T1, _: T2) -> bool {
        type_eq_ignore_lifetimes::<T1, T2>()
    }

    #[cfg(feature = "alloc")]
    #[inline(never)]
    fn make_dummy_string() -> String {
        #[expect(
            clippy::arithmetic_side_effects,
            reason = "false positive for string type"
        )]
        black_box(String::from("foo") + "bar")
    }

    #[test]
    fn test_type_eq_ignore_lifetimes_with_local() {
        test_type_eq_ignore_lifetimes_with_local_impl(&black_box(123));
    }

    #[expect(
        clippy::trivially_copy_pass_by_ref,
        reason = "ref is necessary for the test"
    )]
    fn test_type_eq_ignore_lifetimes_with_local_impl<'a>(local1: &'a u32) {
        assert!(type_eq_ignore_lifetimes::<&'static str, &'a str>());
        assert!(type_eq_ignore_lifetimes::<&'a str, &'static str>());
        assert!(type_eq_ignore_lifetimes::<&'a str, &'a str>());
        assert!(!type_eq_ignore_lifetimes::<&'a str, &'a u32>());

        assert!(type_eq_ignore_lifetimes::<Ref<'static, u32>, Ref<'a, u32>>());
        assert!(type_eq_ignore_lifetimes::<Ref<'a, u32>, Ref<'static, u32>>());
        assert!(type_eq_ignore_lifetimes::<Ref<'a, u32>, Ref<'a, u32>>());
        assert!(!type_eq_ignore_lifetimes::<Ref<'a, u32>, Ref<'a, u64>>());

        let local2: &u32 = &black_box(234);
        let local3: &i32 = &black_box(234);
        assert!(type_eq_ignore_lifetimes_of_vals(local1, local2));
        assert!(!type_eq_ignore_lifetimes_of_vals(local2, local3));
        assert!(!type_eq_ignore_lifetimes_of_vals(local1, local3));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_type_eq_ignore_lifetimes_alloc() {
        let string = make_dummy_string();
        let non_static_str: &str = string.as_str();
        assert!(type_eq_ignore_lifetimes_of_vals("foo", non_static_str));
    }
}
