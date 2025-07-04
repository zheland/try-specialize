use core::fmt::{Debug, Display, Write as FmtWrite};
use core::future::{Future, IntoFuture};
use core::hash::Hash;
use core::ops::Deref;
use core::panic::{RefUnwindSafe, UnwindSafe};
use core::str::FromStr;
#[cfg(feature = "std")]
use std::io::{Read as IoRead, Write as IoWrite};

use crate::LifetimeFree;

/// Generates a function which returns `true` if the given type implements
/// specified trait. Note that all the lifetimes are erased and not accounted
/// for.
///
/// Library tests ensure that the `impls_trait` checks are performed at compile
/// time and are fully optimized with no runtime cost at `opt-level >= 1`. Note
/// that the release profile uses `opt-level = 3` by default.
///
/// Custom attributes:
/// - `#[auto_doc]` attribute enables automatic documentation generation for the
///   generated function including the `Reliability` documentation section.
/// - `#[+reliability_doc]` attribute enables automatic generation of
///   `Reliability` documentation section for the generated function.
///
/// # Reliability
///
/// While it is unlikely, there is still a possibility that the functions
/// generated by this macro may return false negatives in future Rust versions.
///
/// The correctness of the results returned by the functions depends on
/// the following:
/// - Documented behavior that if `T` implements `Eq`, two `Rc`s that point to
///   the same allocation are always equal:
///   <https://doc.rust-lang.org/1.82.0/std/rc/struct.Rc.html#method.eq>.
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
/// - <https://doc.rust-lang.org/1.82.0/std/rc/struct.Rc.html#method.eq>,
/// - <https://github.com/rust-lang/rust/issues/42655>.
///
/// # Examples
///
/// ```rust
/// # #[cfg(all(feature = "alloc", feature = "unreliable"))] {
/// use try_specialize::define_impls_trait_ignore_lt_fn;
///
/// define_impls_trait_ignore_lt_fn!(
///     #[auto_doc] pub impls_into_iterator_u32: IntoIterator<Item = u32>
/// );
/// assert!(impls_into_iterator_u32::<[u32; 4]>());
/// assert!(impls_into_iterator_u32::<Vec<u32>>());
/// assert!(!impls_into_iterator_u32::<Vec<i32>>());
/// # }
/// ```
///
/// ```rust
/// # #[cfg(all(feature = "alloc", feature = "unreliable"))] {
/// use try_specialize::define_impls_trait_ignore_lt_fn;
///
/// define_impls_trait_ignore_lt_fn!(
///     pub impls_copy_eq_ord: Copy + Eq + Ord
/// );
/// assert!(impls_copy_eq_ord::<u32>());
/// assert!(impls_copy_eq_ord::<[u32; 4]>());
/// assert!(!impls_copy_eq_ord::<Vec<u32>>());
/// # }
/// ```
///
/// ```rust
/// # #[cfg(all(feature = "alloc", feature = "unreliable"))] {
/// use try_specialize::define_impls_trait_ignore_lt_fn;
///
/// pub trait IsRef {}
/// impl<T> IsRef for &T where T: ?Sized {}
///
/// pub trait IsMutRef {}
/// impl<T> IsMutRef for &mut T where T: ?Sized {}
///
/// pub trait IsBox {}
/// impl<T> IsBox for Box<T> where T: ?Sized {}
///
/// define_impls_trait_ignore_lt_fn!(
///     #[+reliability_doc]
///     /// Returns `true` if the given type is a const reference like `&T`.
///     pub is_ref: IsRef
/// );
///
/// define_impls_trait_ignore_lt_fn!(
///     #[+reliability_doc]
///     /// Returns `true` if the given type is a mutable reference like
///     /// `&mut T`.
///     pub is_mut_ref: IsMutRef
/// );
///
/// define_impls_trait_ignore_lt_fn!(
///     #[+reliability_doc]
///     /// Returns `true` if the given type is a `Box<T>`-type.
///     pub is_box: IsBox
/// );
///
/// assert!(!is_ref::<u32>());
/// assert!(!is_ref::<[u32; 4]>());
/// assert!(!is_ref::<Vec<u32>>());
/// assert!(is_ref::<&u32>());
/// assert!(is_ref::<&[u32]>());
/// assert!(!is_ref::<&mut u32>());
///
/// assert!(!is_mut_ref::<u32>());
/// assert!(!is_mut_ref::<&u32>());
/// assert!(is_mut_ref::<&mut u32>());
///
/// assert!(!is_box::<u32>());
/// assert!(!is_box::<&u32>());
/// assert!(!is_box::<&mut u32>());
/// assert!(is_box::<Box<u32>>());
/// assert!(is_box::<Box<(char, u32, i128)>>());
/// # }
/// ```
#[macro_export]
macro_rules! define_impls_trait_ignore_lt_fn {
    ( #[auto_doc] $( #[$meta:meta] )* $vis:vis $fn_name:ident: $( $bounds:tt )+ ) => {
        define_impls_trait_ignore_lt_fn! {
            #[doc = "Returns `true` if the given type implements `"]
            #[doc = stringify!( $( $bounds )+ )]
            #[doc = "`."]
            ///
            /// Use [`define_impls_trait_ignore_lt_fn`] macro to generate other
            /// trait implementation check functions.
            ///
            /// Library tests ensure that the `impls_trait` checks are performed
            /// at compile time and fully optimized with no runtime cost at
            /// `opt-level >= 1`. Note that the release profile uses
            /// `opt-level = 3` by default.
            ///
            /// [`define_impls_trait_ignore_lt_fn`]: https://docs.rs/try-specialize/latest/try_specialize/macro.define_impls_trait_ignore_lt_fn.html
            ///
            #[+reliability_doc]
            $( #[$meta] )*
            $vis $fn_name: $( $bounds )+
        }
    };
    (
        $( #[$meta1:meta] )* #[+reliability_doc] $( #[$meta2:meta] )*
        $vis:vis $fn_name:ident: $( $bounds:tt )+
    ) => {
        define_impls_trait_ignore_lt_fn! {
            $( #[$meta1] )*
            ///
            /// # Reliability
            ///
            /// While it is unlikely, there is still a possibility that this
            /// function may return false negatives in future Rust versions.
            ///
            /// The correctness of the results returned by the functions depends
            /// on the following:
            /// - Documented behavior that if `T` implements `Eq`, two `Rc`s
            ///   that point to the same allocation are always equal:
            ///   <https://doc.rust-lang.org/1.82.0/std/rc/struct.Rc.html#method.eq>.
            /// - Undocumented behavior that the `Rc::partial_eq` implementation
            ///   for `T: Eq` will not use `PartialEq::eq` if both `Rc`s point
            ///   to the same memory location.
            /// - The assumption that the undocumented short-circuit behavior
            ///   described above will be retained for optimization purposes.
            ///
            /// There is no formal guarantee that the undocumented behavior
            /// described above will be retained. If the implementation changes
            /// in a future Rust version, the function may return a false
            /// negative, that is, it may return `false`, even though `T`
            /// implements the trait. However, the implementation guarantees
            /// that a false positive result is impossible, i.e., the function
            /// will never return true if `T` does not implement the trait in
            /// any future Rust version.
            ///
            /// Details:
            /// - <https://internals.rust-lang.org/t/rc-uses-visibly-behavior-changing-specialization-is-that-okay/16173/6>,
            /// - <https://users.rust-lang.org/t/hack-to-specialize-w-write-for-vec-u8/100366>,
            /// - <https://doc.rust-lang.org/1.82.0/std/rc/struct.Rc.html#method.eq>,
            /// - <https://github.com/rust-lang/rust/issues/42655>.
            ///
            $( #[$meta2] )*
            $vis $fn_name: $( $bounds )+
        }
    };
    ( $( #[$meta:meta] )* $vis:vis $fn_name:ident: $( $bounds:tt )+ ) => {
        $( #[$meta] )*
        #[inline]
        #[must_use]
        $vis fn $fn_name<T>() -> bool
        where
            T: ?Sized
        {
            struct Impl<'a, T>(&'a ::core::cell::Cell<bool>, ::core::marker::PhantomData<T>)
            where
                T: ?Sized;

            impl<T> PartialEq for Impl<'_, T>
            where
                T: ?Sized,
            {
                fn eq(&self, _other: &Self) -> bool {
                    let _ = self.0.set(true);
                    true
                }
            }

            impl<T> Eq for Impl<'_, T> where T: ?Sized + $( $bounds )+ {}

            let not_impls_trait = ::core::cell::Cell::new(false);
            let rc = $crate::macro_deps::Rc::new(Impl(
                &not_impls_trait,
                ::core::marker::PhantomData::<T>
            ));
            let _ = rc == rc;
            !not_impls_trait.get()
        }
    };
}

define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_sized_weak: Sized);
define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_send_weak: Send);
define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_sync_weak: Sync);
define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_unpin_weak: Unpin);
define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_unwind_safe_weak: UnwindSafe);
define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_ref_unwind_safe_weak: RefUnwindSafe);

define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_deref_weak: Deref);
define_impls_trait_ignore_lt_fn!(
    #[auto_doc]
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(all(feature = "alloc", feature = "unreliable"))] {
    /// use core::sync::atomic::{AtomicU32, Ordering as AtomicOrdering};
    ///
    /// use try_specialize::unreliable::impls_copy_weak;
    ///
    /// #[derive(Eq, PartialEq, Debug)]
    /// pub struct ArrayLike<T, const N: usize> {
    /// #   inner: [T; N]
    /// }
    ///
    /// impl<T, const N: usize> From<[T; N]> for ArrayLike<T, N> {
    ///     #[inline]
    ///     fn from(value: [T; N]) -> Self {
    ///         // ...
    ///         # Self { inner: value }
    ///     }
    /// }
    ///
    /// impl<T, const N: usize> AsRef<[T; N]> for ArrayLike<T, N> {
    ///     #[inline]
    ///     fn as_ref(&self) -> &[T; N] {
    ///         // ...
    ///         # &self.inner
    ///     }
    /// }
    ///
    /// static DEBUG: AtomicU32 = AtomicU32::new(0);
    ///
    /// impl<T, const N: usize> Clone for ArrayLike<T, N>
    /// where
    ///     T: Clone
    /// {
    ///     #[inline]
    ///     fn clone(&self) -> Self {
    ///         if impls_copy_weak::<T>() {
    ///             DEBUG.store(101, AtomicOrdering::Relaxed);
    ///             // Fast path for `T: Copy`.
    ///             unsafe { std::mem::transmute_copy(self) }
    ///         } else {
    ///             DEBUG.store(202, AtomicOrdering::Relaxed);
    ///             Self::from(self.as_ref().clone())
    ///         }
    ///     }
    /// }
    ///
    /// #[derive(Clone, Eq, PartialEq, Debug)]
    /// struct NonCopiable<T>(pub T);
    ///
    /// assert_eq!(
    ///     ArrayLike::from([1, 2, 3]).clone(),
    ///     ArrayLike::from([1, 2, 3])
    /// );
    /// assert_eq!(DEBUG.load(AtomicOrdering::Relaxed), 101);
    ///
    /// assert_eq!(
    ///     ArrayLike::from([NonCopiable(1), NonCopiable(2)]).clone(),
    ///     ArrayLike::from([NonCopiable(1), NonCopiable(2)])
    /// );
    /// assert_eq!(DEBUG.load(AtomicOrdering::Relaxed), 202);
    /// # }
    /// ```
    pub impls_copy_weak: Copy
);
define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_clone_weak: Clone);
define_impls_trait_ignore_lt_fn!(
    #[auto_doc]
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(all(feature = "alloc", feature = "unreliable"))] {
    ///
    /// use core::sync::atomic::{AtomicU32, Ordering as AtomicOrdering};
    /// # use std::sync::Arc;
    ///
    /// use try_specialize::unreliable::impls_eq_weak;
    ///
    /// #[derive(Clone, Debug)]
    /// pub struct ArcLike<T> {
    ///     // ...
    /// #   inner: Arc<T>,
    /// }
    ///
    /// impl<T> ArcLike<T> {
    ///     #[inline]
    ///     fn new(value: T) -> Self {
    ///         // ...
    /// #       Self {
    /// #           inner: Arc::new(value),
    /// #       }
    ///     }
    ///
    ///     #[inline]
    ///     fn as_ptr(&self) -> *const T {
    ///         // ...
    /// #       Arc::as_ptr(&self.inner)
    ///     }
    /// }
    ///
    /// impl<T> AsRef<T> for ArcLike<T> {
    ///     #[inline]
    ///     fn as_ref(&self) -> &T {
    ///         // ...
    /// #       &*self.inner
    ///     }
    /// }
    ///
    /// impl<T> PartialEq for ArcLike<T>
    /// where
    ///     T: PartialEq,
    /// {
    ///     #[inline]
    ///     fn eq(&self, other: &Self) -> bool {
    ///         // Fast path for `T: Eq`.
    ///         if impls_eq_weak::<T>() && self.as_ptr() == other.as_ptr() {
    ///             // Fast path for `T: Eq` if pointers are equal.
    ///             return true;
    ///         }
    ///         self.as_ref() == other.as_ref()
    ///     }
    /// }
    ///
    /// #[derive(Copy, Clone, Eq, Debug)]
    /// struct Wrapper<T>(pub T);
    ///
    /// static COUNTER: AtomicU32 = AtomicU32::new(0);
    ///
    /// impl<T> PartialEq for Wrapper<T>
    /// where
    ///     T: PartialEq,
    /// {
    ///     #[inline]
    ///     fn eq(&self, other: &Self) -> bool {
    ///         let _ = COUNTER.fetch_add(1, AtomicOrdering::Relaxed);
    ///         self.0 == other.0
    ///     }
    /// }
    ///
    /// let arc_like1 = ArcLike::new(Wrapper(42_u32));
    /// let arc_like2 = arc_like1.clone();
    /// assert_eq!(arc_like1, arc_like2);
    /// // `u32` implements Eq. Fast path used. Counter not incremented.
    /// assert_eq!(COUNTER.load(AtomicOrdering::Relaxed), 0);
    ///
    /// let arc_like1 = ArcLike::new(Wrapper(123.456_f64));
    /// let arc_like2 = arc_like1.clone();
    /// assert_eq!(arc_like1, arc_like2);
    /// // `f64` doesn't implement Eq. Fast path is not used.
    /// // Counter incremented.
    /// assert_eq!(COUNTER.load(AtomicOrdering::Relaxed), 1);
    /// # }
    /// ```
    pub impls_eq_weak: Eq
);
define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_partial_eq_weak: PartialEq);
define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_ord_weak: Ord);
define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_partial_ord_weak: PartialOrd);
define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_hash_weak: Hash);
define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_default_weak: Default);
define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_debug_weak: Debug);
define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_display_weak: Display);
define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_from_str_weak: FromStr);
define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_iterator_weak: Iterator);
define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_into_iterator_weak: IntoIterator);
define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_future_weak: Future);
define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_into_future_weak: IntoFuture);
define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_fmt_write_weak: FmtWrite);
#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_io_read_weak: IoRead);
#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_io_write_weak: IoWrite);

define_impls_trait_ignore_lt_fn!(#[auto_doc] pub impls_lifetime_free_weak: LifetimeFree);

#[cfg(test)]
mod tests {
    #[cfg(feature = "alloc")]
    use alloc::string::String;
    #[cfg(feature = "alloc")]
    use alloc::vec::Vec;

    use crate::unreliable::{
        impls_clone_weak, impls_copy_weak, impls_eq_weak, impls_lifetime_free_weak,
        impls_partial_eq_weak,
    };

    #[test]
    fn test_impls_copy() {
        #[derive(Copy, Clone)]
        struct Copiable;
        #[derive(Clone)]
        struct Cloneable;
        struct NonCloneable;

        assert!(impls_copy_weak::<()>());
        assert!(impls_copy_weak::<u32>());
        assert!(impls_copy_weak::<f64>());

        assert!(impls_copy_weak::<Copiable>());
        assert!(!impls_copy_weak::<Cloneable>());
        assert!(!impls_copy_weak::<NonCloneable>());
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_impls_copy_alloc() {
        assert!(impls_copy_weak::<&String>());
        assert!(impls_copy_weak::<&Vec<u8>>());
        assert!(!impls_copy_weak::<String>());
        assert!(!impls_copy_weak::<Vec<u8>>());
        assert!(!impls_copy_weak::<&mut String>());
        assert!(!impls_copy_weak::<&mut Vec<u8>>());
    }

    #[test]
    fn test_impls_clone() {
        #[derive(Copy, Clone)]
        struct Copiable;
        #[derive(Clone)]
        struct Cloneable;
        struct NonCloneable;

        assert!(impls_clone_weak::<()>());
        assert!(impls_clone_weak::<u32>());
        assert!(impls_clone_weak::<f64>());

        assert!(impls_clone_weak::<Copiable>());
        assert!(impls_clone_weak::<Cloneable>());
        assert!(!impls_clone_weak::<NonCloneable>());
    }

    #[test]
    fn test_impls_eq() {
        assert!(impls_eq_weak::<()>());
        assert!(impls_eq_weak::<u32>());
        assert!(!impls_eq_weak::<f64>());
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_impls_eq_alloc() {
        assert!(impls_eq_weak::<&String>());
        assert!(impls_eq_weak::<&Vec<u8>>());
        assert!(impls_eq_weak::<String>());
        assert!(impls_eq_weak::<Vec<u8>>());
        assert!(impls_eq_weak::<&mut String>());
        assert!(impls_eq_weak::<&mut Vec<u8>>());
    }

    #[test]
    fn test_impls_partial_eq() {
        assert!(impls_partial_eq_weak::<()>());
        assert!(impls_partial_eq_weak::<u32>());
        assert!(impls_partial_eq_weak::<f64>());
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_impls_partial_eq_alloc() {
        assert!(impls_partial_eq_weak::<&String>());
        assert!(impls_partial_eq_weak::<&Vec<u8>>());
        assert!(impls_partial_eq_weak::<String>());
        assert!(impls_partial_eq_weak::<Vec<u8>>());
        assert!(impls_partial_eq_weak::<&mut String>());
        assert!(impls_partial_eq_weak::<&mut Vec<u8>>());
    }

    #[test]
    fn test_lifetime_free() {
        assert!(impls_lifetime_free_weak::<()>());
        assert!(impls_lifetime_free_weak::<u32>());
        assert!(impls_lifetime_free_weak::<f64>());
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_lifetime_free_alloc() {
        assert!(!impls_lifetime_free_weak::<&String>());
        assert!(!impls_lifetime_free_weak::<&Vec<u8>>());
        assert!(impls_lifetime_free_weak::<String>());
        assert!(impls_lifetime_free_weak::<Vec<u8>>());
        assert!(!impls_lifetime_free_weak::<&mut String>());
        assert!(!impls_lifetime_free_weak::<&mut Vec<u8>>());
    }
}
