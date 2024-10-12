use crate::{LifetimeFree, Specialization};

/// A trait for specializing one type to another at runtime.
///
/// This trait uses [`Specialization`] helper struct to perform all
/// conversions. You can use [`Specialization`] directly if you need to perform
/// more complex specialization cases or to cache the specializable ability.
///
/// Library tests ensure that the specializations are performed at compile time
/// and are fully optimized with no runtime cost at `opt-level >= 1`. Note that
/// the release profile uses `opt-level = 3` by default.
///
/// Methods cheat sheet:
/// | Bounds\Operation | specialize `T1` to `T2` | specialize `&T1` to `&T2` | specialize `&mut T1` to `&mut T2` |
/// |:--:|:--:|:--:|:--:|
/// | `T1: 'static` <br /> `+ LifetimeFree` | [`try_specialize`] | [`try_specialize_ref`] | [`try_specialize_mut`] |
/// | `T2: 'static` <br /> `+ LifetimeFree` | [`try_specialize_from`] | [`try_specialize_from_ref`] | [`try_specialize_from_mut`] |
/// | `T1: 'static,` <br /> `T2: 'static,` | [`try_specialize_static`] | [`try_specialize_ref_static`] | [`try_specialize_mut_static`] |
/// | unconstrained <br /> underlying type <br /> maybe impls <br /> `LifetimeFree` | [`..._if_lifetime_free_weak`] | [`..._ref_if_lifetime_free_weak`] | [`..._mut_if_lifetime_free_weak`] |
/// | unconstrained <br /> `unsafe` without <br /> lifetimes check | [`..._ignore_lifetimes`] | [`..._ref_ignore_lifetimes`] | [`..._mut_ignore_lifetimes`] |
///
/// [`try_specialize`]: TrySpecialize::try_specialize
/// [`try_specialize_ref`]: TrySpecialize::try_specialize_ref
/// [`try_specialize_mut`]: TrySpecialize::try_specialize_mut
/// [`try_specialize_from`]: TrySpecialize::try_specialize_from
/// [`try_specialize_from_ref`]: TrySpecialize::try_specialize_from_ref
/// [`try_specialize_from_mut`]: TrySpecialize::try_specialize_from_mut
/// [`try_specialize_static`]: TrySpecialize::try_specialize_static
/// [`try_specialize_ref_static`]: TrySpecialize::try_specialize_ref_static
/// [`try_specialize_mut_static`]: TrySpecialize::try_specialize_mut_static
/// [`..._ignore_lifetimes`]: TrySpecialize::try_specialize_ignore_lifetimes
/// [`..._ref_ignore_lifetimes`]: TrySpecialize::try_specialize_ref_ignore_lifetimes
/// [`..._mut_ignore_lifetimes`]: TrySpecialize::try_specialize_mut_ignore_lifetimes
/// [`..._if_lifetime_free_weak`]: crate::unreliable::TrySpecializeWeak::try_specialize_if_lifetime_free_weak
/// [`..._ref_if_lifetime_free_weak`]: crate::unreliable::TrySpecializeWeak::try_specialize_ref_if_lifetime_free_weak
/// [`..._mut_if_lifetime_free_weak`]: crate::unreliable::TrySpecializeWeak::try_specialize_mut_if_lifetime_free_weak
pub trait TrySpecialize {
    /// Attempts to specialize `Self` as `T` for types without lifetimes.
    ///
    /// Returns `Self` as `T` wrapped in `Ok` if `Self` and `T` types are
    /// identical. Otherwise, it returns `Self` wrapped in `Err`.
    ///
    /// Note that this method requires target type to implement
    /// [`LifetimeFree`]. Use [`TrySpecialize::try_specialize_from`] if your
    /// target type doesn't have [`LifetimeFree`] bound but source type does.
    /// Use [`TrySpecialize::try_specialize_static`] if both source and target
    /// type have `'static` bounds.
    ///
    /// The [`LifetimeFree`] trait is **not** automatically derived for all
    /// lifetime-free types. The library only implements it for standard library
    /// types that do not have any lifetime parameters.
    ///
    /// [`LifetimeFree`]: crate::LifetimeFree
    ///
    /// # Examples
    ///
    /// Simple partial reimplementation of stdlib `ToString`:
    /// ```rust
    /// # #[cfg(feature = "std")] {
    /// use core::fmt::Display;
    ///
    /// use try_specialize::TrySpecialize;
    ///
    /// fn to_string<T>(value: T) -> String
    /// where
    ///     T: Display,
    /// {
    ///     match value.try_specialize() {
    ///         Ok(string) => string,
    ///         Err(value) => format!("{value}"),
    ///     }
    /// }
    ///
    /// assert_eq!(to_string("abc".to_owned()), "abc".to_owned()); // Specialized.
    /// assert_eq!(to_string(123), String::from("123")); // Default.
    /// # }
    /// ```
    ///
    /// Note that many standard library types and traits, including `ToString`,
    /// already use specialization for optimization purposes using
    /// `min_specialization` nightly feature.
    #[expect(clippy::missing_errors_doc, reason = "already described")]
    #[inline]
    fn try_specialize<T>(self) -> Result<T, Self>
    where
        Self: Sized,
        T: LifetimeFree,
    {
        if let Some(spec) = Specialization::try_new() {
            Ok(spec.specialize(self))
        } else {
            Err(self)
        }
    }

    /// Attempts to specialize `T` as `Self` for types without lifetimes.
    ///
    /// Returns `T` as `Self` wrapped in `Ok` if `Self` and `T` types are
    /// identical. Otherwise, it returns `T` wrapped in `Err`.
    ///
    /// Note that this method requires source type to implement
    /// [`LifetimeFree`]. Use [`TrySpecialize::try_specialize_from`] if your
    /// source type doesn't have [`LifetimeFree`] bound but target type does.
    /// Use [`TrySpecialize::try_specialize_static`] if both target and source
    /// type have `'static` bounds.
    /// The [`LifetimeFree`] trait is **not** automatically derived for all
    /// lifetime-free types. The library only implements it for standard library
    /// types that do not have any lifetime parameters.
    ///
    /// [`LifetimeFree`]: crate::LifetimeFree
    ///
    /// # Examples
    ///
    /// Generate a placeholder with non-default value for some types:
    /// ```rust
    /// # #[cfg(feature = "alloc")] {
    /// use try_specialize::{Specialization, TrySpecialize};
    ///
    /// fn placeholder<T>() -> T
    /// where
    ///     T: Default,
    /// {
    ///     None.or_else(|| T::try_specialize_from(12_u8).ok())
    ///         .or_else(|| T::try_specialize_from(234_u16).ok())
    ///         .or_else(|| T::try_specialize_from(3456_u32).ok())
    ///         .or_else(|| T::try_specialize_from(45678_u64).ok())
    ///         .or_else(|| T::try_specialize_from(567_890_u128).ok())
    ///         .or_else(|| T::try_specialize_from(123_456_789_usize).ok())
    ///         .or_else(|| T::try_specialize_from(123.456_f32).ok())
    ///         .or_else(|| T::try_specialize_from(123.456_f64).ok())
    ///         .or_else(|| {
    ///             // SAFETY: For any `'a` It is safe to specialize `&'static str`
    ///             // as `&'a str`.
    ///             unsafe { "dummy string".try_specialize_ignore_lifetimes() }.ok()
    ///         })
    ///         .or_else(|| {
    ///             let spec/*: Specialization<T, String>*/ = Specialization::try_new()?;
    ///             Some(spec.rev().specialize(String::from("foobar")))
    ///         })
    ///         .or_else(|| {
    ///             let spec/*: Specialization<T, Box<str>>*/ = Specialization::try_new()?;
    ///             Some(spec.rev().specialize(String::from("bazz").into_boxed_str()))
    ///         })
    ///         .unwrap_or_default()
    /// }
    ///
    /// assert_eq!(placeholder::<(u8, u8)>(), (0, 0));
    /// assert_eq!(placeholder::<u32>(), 3456);
    /// assert_eq!(placeholder::<f64>(), 123.456_f64);
    /// assert_eq!(placeholder::<u128>(), 567_890);
    /// assert_eq!(placeholder::<i128>(), 0);
    /// assert_eq!(placeholder::<&'static str>(), "dummy string");
    /// assert_eq!(placeholder::<String>(), String::from("foobar"));
    /// assert_eq!(placeholder::<Box<str>>(), Box::from("bazz"));
    /// # }
    /// ```
    #[expect(clippy::missing_errors_doc, reason = "already described")]
    #[inline]
    fn try_specialize_from<T>(other: T) -> Result<Self, T>
    where
        Self: Sized,
        T: LifetimeFree,
    {
        if let Some(spec) = Specialization::try_new() {
            Ok(spec.rev().specialize(other))
        } else {
            Err(other)
        }
    }

    /// Attempts to specialize `Self` as `T` for static types.
    ///
    /// Returns `Self` as `T` wrapped in `Ok` if `Self` and `T` types are
    /// identical. Otherwise, it returns `Self` wrapped in `Err`.
    ///
    /// Note that this method requires both types to have `'static` lifetime,
    /// but don't require any type to implement [`LifetimeFree`]. If one of your
    /// types does not have a 'static bounds but the other type implements
    /// [`LifetimeFree`] use [`TrySpecialize::try_specialize`] or
    /// [`TrySpecialize::try_specialize_from`] instead.
    ///
    /// # Note
    ///
    /// This function requires both the source and destination types to
    /// implement `'static`. Although most `'static` types in Rust can be
    /// subtypes to a non-`'static` alternatives this is not always the case.
    /// For example `fn(&'static str)` and `fn(&'a str)` have the same `TypeId`
    /// however you can't subtype the first to the second, because, unlike
    /// anything else in the language, functions are contravariant over their
    /// arguments. See <https://doc.rust-lang.org/reference/subtyping.html#variance>
    /// and <https://doc.rust-lang.org/nomicon/subtyping.html#variance> for
    /// more details.
    ///
    /// # Examples
    ///
    /// Function with specialized implementation for
    /// [`std::collections::HashMap`] and `hashbrown::HashMap`:
    /// ```rust
    /// use try_specialize::TrySpecialize;
    ///
    /// fn process_static<T>(value: T)
    /// where
    ///     T: 'static,
    /// {
    ///     match value.try_specialize_static::<std::collections::HashMap<u32, char>>() {
    ///         Ok(hash_map @ std::collections::HashMap { .. }) => {
    ///             drop(hash_map);
    ///             // specialized impl for `std::collections::HashMap`
    ///         }
    ///         Err(value) => {
    ///             match value.try_specialize_static::<hashbrown::HashMap<u32, char>>() {
    ///                 Ok(hash_map @ hashbrown::HashMap { .. }) => {
    ///                     drop(hash_map);
    ///                     // specialized impl for `hashbrown::HashMap`
    ///                 }
    ///                 Err(default) => {
    ///                     drop(default);
    ///                     // default impl ...
    ///                 }
    ///             }
    ///         }
    ///     }
    /// }
    /// # let input = [(123_u32, 'a'), (234_u32, 'b')];
    /// # process_static(input.into_iter().collect::<std::collections::HashMap::<_, _>>());
    /// # process_static(input.into_iter().collect::<hashbrown::HashMap::<_, _>>());
    /// # process_static(input.into_iter().collect::<Vec::<_>>());
    /// ```
    #[expect(clippy::missing_errors_doc, reason = "already described")]
    #[inline]
    fn try_specialize_static<T>(self) -> Result<T, Self>
    where
        Self: 'static + Sized,
        T: 'static,
    {
        if let Some(spec) = Specialization::try_new_static() {
            Ok(spec.specialize(self))
        } else {
            Err(self)
        }
    }

    /// Attempts to specialize `&Self` as `&T` for types without lifetimes.
    ///
    /// Note that this method requires target type to implement
    /// [`LifetimeFree`]. Use [`TrySpecialize::try_specialize_from_ref`] if your
    /// target type doesn't implement [`LifetimeFree`] but source type does.
    ///
    /// The [`LifetimeFree`] trait is **not** automatically derived for all
    /// lifetime-free types. The library only implements it for standard library
    /// types that do not have any lifetime parameters.
    ///
    /// [`LifetimeFree`]: crate::LifetimeFree
    ///
    /// # Examples
    ///
    /// Stringifiable type concatenation, that don't allocate memory if one of
    /// the arguments is empty `&str`:
    /// ```rust
    /// use core::fmt::Display;
    /// use std::borrow::Cow;
    /// use std::format;
    ///
    /// use try_specialize::TrySpecialize;
    ///
    /// fn concat<'a, T1, T2>(first: &'a T1, second: &'a T2) -> Cow<'a, str>
    /// where
    ///     T1: ?Sized + Display,
    ///     T2: ?Sized + Display,
    /// {
    ///     match (
    ///         first.try_specialize_ref(),
    ///         second.try_specialize_ref(),
    ///     ) {
    ///         (Some(first), Some("")) => Cow::Borrowed(first),
    ///         (Some(""), Some(second)) => Cow::Borrowed(second),
    ///         (_, _) => Cow::Owned(format!("{first}{second}")),
    ///     }
    /// }
    ///
    /// assert!(matches!(concat("foo", "bar"), Cow::Owned(v) if v == "foobar"));
    /// assert!(matches!(concat("foo", ""), Cow::Borrowed("foo")));
    /// assert!(matches!(concat("", "bar"), Cow::Borrowed("bar")));
    /// let foo = String::from("foo");
    /// let bar = String::from("bar");
    /// assert!(matches!(concat(&foo, &bar), Cow::Owned(v) if v == "foobar"));
    /// assert!(matches!(concat("foo", &456), Cow::Owned(v) if v == "foo456"));
    /// assert!(matches!(concat(&123, &456), Cow::Owned(v) if v == "123456"));
    /// ```
    #[inline]
    fn try_specialize_ref<T>(&self) -> Option<&T>
    where
        T: ?Sized + LifetimeFree,
    {
        Specialization::try_new().map(|spec| spec.specialize_ref(self))
    }

    /// Attempts to specialize `&T` as `&Self` for types without lifetimes.
    ///
    /// Note that this method requires source type to implement
    /// [`LifetimeFree`]. Use [`TrySpecialize::try_specialize_ref`] if your
    /// source type doesn't implement [`LifetimeFree`] but target type does.
    /// The [`LifetimeFree`] trait is **not** automatically derived for all
    /// lifetime-free types. The library only implements it for standard library
    /// types that do not have any lifetime parameters.
    ///
    /// [`LifetimeFree`]: crate::LifetimeFree
    #[inline]
    fn try_specialize_from_ref<T>(other: &T) -> Option<&Self>
    where
        T: ?Sized + LifetimeFree,
    {
        Specialization::try_new().map(|spec| spec.rev().specialize_ref(other))
    }

    /// Attempts to specialize `&Self` as `&T` for static types.
    ///
    /// Note that this method requires both types to have `'static` lifetime,
    /// but don't require any type to implement [`LifetimeFree`].
    #[inline]
    fn try_specialize_ref_static<T>(&self) -> Option<&T>
    where
        Self: 'static,
        T: ?Sized + 'static,
    {
        Specialization::try_new_static().map(|spec| spec.specialize_ref(self))
    }

    /// Attempts to specialize `&mut Self` as `&mut T` for types without
    /// lifetimes.
    ///
    /// Note that this method requires target type to implement
    /// [`LifetimeFree`]. Use [`TrySpecialize::try_specialize_from_mut`] if your
    /// target type doesn't implement [`LifetimeFree`] but source type does.
    ///
    /// The [`LifetimeFree`] trait is **not** automatically derived for all
    /// lifetime-free types. The library only implements it for standard library
    /// types that do not have any lifetime parameters.
    ///
    /// [`LifetimeFree`]: crate::LifetimeFree
    #[inline]
    fn try_specialize_mut<T>(&mut self) -> Option<&mut T>
    where
        T: ?Sized + LifetimeFree,
    {
        Specialization::try_new().map(|spec| spec.specialize_mut(self))
    }

    /// Attempts to specialize `&mut T` as `&mut Self` for types without
    /// lifetimes.
    ///
    /// Note that this method requires source type to implement
    /// [`LifetimeFree`]. Use [`TrySpecialize::try_specialize_mut`] if your
    /// source type doesn't implement [`LifetimeFree`] but target type does.
    /// The [`LifetimeFree`] trait is **not** automatically derived for all
    /// lifetime-free types. The library only implements it for standard library
    /// types that do not have any lifetime parameters.
    ///
    /// [`LifetimeFree`]: crate::LifetimeFree
    #[inline]
    fn try_specialize_from_mut<T>(other: &mut T) -> Option<&mut Self>
    where
        T: ?Sized + LifetimeFree,
    {
        Specialization::try_new().map(|spec| spec.rev().specialize_mut(other))
    }

    /// Attempts to specialize `&mut Self` as `&mut T` for static types.
    ///
    /// Note that this method requires both types to have `'static` lifetime,
    /// but don't require any type to implement [`LifetimeFree`].
    #[inline]
    fn try_specialize_mut_static<T>(&mut self) -> Option<&mut T>
    where
        Self: 'static,
        T: ?Sized + 'static,
    {
        Specialization::try_new_static().map(|spec| spec.specialize_mut(self))
    }

    /// Attempts to specialize `Self` as `T` ignoring lifetimes.
    ///
    /// Returns `T` as `Self` wrapped in `Ok` if `Self` and `T` types are
    /// identical. Otherwise, it returns `T` wrapped in `Err`.
    ///
    /// # Safety
    ///
    /// This method doesn't validate type lifetimes. Lifetimes equality should
    /// be validated separately.
    ///
    /// Calling this method for types with any differences in lifetimes between
    /// `Self` and `T` types is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    ///
    /// # Examples
    ///
    /// Generate a placeholder with non-default value for some types with
    /// several `&'static T` types:
    /// ```rust
    /// use try_specialize::{Specialization, TrySpecialize};
    ///
    /// fn placeholder<T>() -> T
    /// where
    ///     T: Default,
    /// {
    ///     None.or_else(|| T::try_specialize_from(12_u8).ok())
    ///         .or_else(|| T::try_specialize_from(234_u16).ok())
    ///         .or_else(|| T::try_specialize_from(3456_u32).ok())
    ///         .or_else(|| {
    ///             // SAFETY: For any `'a` It is safe to specialize `&'static str`
    ///             // as `&'a str`.
    ///             unsafe { "dummy string".try_specialize_ignore_lifetimes() }.ok()
    ///         })
    ///         .or_else(|| {
    ///             // Ensure that the slice is static.
    ///             const DEFAULT: &'static [u8] = &[1, 2, 3, 4, 5];
    ///             // SAFETY: For any `'a` It is safe to specialize `&'static [u8]`
    ///             // as `&'a [u8]`.
    ///             unsafe { DEFAULT.try_specialize_ignore_lifetimes() }.ok()
    ///         })
    ///         .unwrap_or_default()
    /// }
    ///
    /// assert_eq!(placeholder::<(u8, u8)>(), (0, 0));
    /// assert_eq!(placeholder::<u32>(), 3456);
    /// assert_eq!(placeholder::<f64>(), 0.0);
    /// assert_eq!(placeholder::<&'static str>(), "dummy string");
    /// assert_eq!(placeholder::<&'static [u8]>(), &[1, 2, 3, 4, 5]);
    /// ```
    #[expect(clippy::missing_errors_doc, reason = "already described")]
    #[inline]
    unsafe fn try_specialize_ignore_lifetimes<T>(self) -> Result<T, Self>
    where
        Self: Sized,
    {
        if let Some(spec) = Specialization::try_new_ignore_lifetimes() {
            Ok(spec.specialize(self))
        } else {
            Err(self)
        }
    }

    /// Attempts to specialize `&Self` as `&T` ignoring lifetimes.
    ///
    /// # Safety
    ///
    /// This method doesn't validate type lifetimes. Lifetimes equality should
    /// be validated separately.
    ///
    /// Calling this method for types with any differences in lifetimes between
    /// `Self` and `T` types is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    unsafe fn try_specialize_ref_ignore_lifetimes<T>(&self) -> Option<&T>
    where
        T: ?Sized,
    {
        Specialization::try_new_ignore_lifetimes().map(|spec| spec.specialize_ref(self))
    }

    /// Attempts to specialize `&mut Self` as `&mut T` ignoring lifetimes.
    ///
    /// # Safety
    ///
    /// This method doesn't validate type lifetimes. Lifetimes equality should
    /// be validated separately.
    ///
    /// Calling this method for types with any differences in lifetimes between
    /// `Self` and `T` types is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    unsafe fn try_specialize_mut_ignore_lifetimes<T>(&mut self) -> Option<&mut T>
    where
        T: ?Sized,
    {
        Specialization::try_new_ignore_lifetimes().map(|spec| spec.specialize_mut(self))
    }
}

impl<T> TrySpecialize for T where T: ?Sized {}

#[cfg(test)]
mod tests {
    #[cfg(feature = "alloc")]
    use alloc::borrow::{Cow, ToOwned};
    #[cfg(feature = "alloc")]
    use alloc::boxed::Box;
    #[cfg(feature = "alloc")]
    use alloc::format;
    #[cfg(feature = "alloc")]
    use alloc::string::String;
    #[cfg(feature = "alloc")]
    use core::fmt::Display;

    #[cfg(feature = "alloc")]
    use crate::LifetimeFree;
    use crate::{type_eq_ignore_lifetimes, TrySpecialize};

    #[cfg(feature = "alloc")]
    fn specialized_to_string<T>(value: T) -> String
    where
        T: LifetimeFree + Display,
    {
        match value.try_specialize::<i32>() {
            Ok(value) => format!("{value}: i32"),
            Err(value) => match value.try_specialize::<u32>() {
                Ok(value) => format!("{value}: u32"),
                Err(value) => format!("{value}: ???"),
            },
        }
    }

    #[test]
    fn test_try_specialize() {
        assert_eq!((123_i32).try_specialize::<i32>(), Ok(123_i32));
        assert_eq!((123_u32).try_specialize::<u32>(), Ok(123_u32));
        assert_eq!((123_i32).try_specialize::<u32>(), Err(123_i32));
        assert_eq!("123".try_specialize::<i32>(), Err("123"));

        assert_eq!(<u32>::try_specialize_from(123_u32), Ok(123_u32));
        assert_eq!(<&'static str>::try_specialize_from(123), Err(123));
    }

    #[test]
    fn test_try_specialize_ref() {
        let value = &[1_u32, 2, 3][..];
        assert_eq!(value.try_specialize_ref::<[u32]>(), Some(value));
        assert_eq!(value.try_specialize_ref::<[i32]>(), None);
        assert_eq!(value.try_specialize_ref::<str>(), None);
        assert_eq!(value.try_specialize_ref::<str>(), None);

        assert_eq!(<[u32]>::try_specialize_from_ref(value), Some(value));
        assert_eq!(<&'static str>::try_specialize_from_ref(value), None);
    }

    #[test]
    fn test_try_specialize_static() {
        let value: &'static [&'static u32] = &[&1, &2, &3];
        assert_eq!(value.try_specialize_static::<&[&u32]>(), Ok(value));
        assert_eq!(value.try_specialize_static::<&[&i32]>(), Err(value));

        let value: [&'static u32; 3] = [&1, &2, &3];
        let value: &[&'static u32] = &value; // Reference itself it not 'static.
        assert_eq!(value.try_specialize_ref_static::<[&u32]>(), Some(value));
        assert_eq!(value.try_specialize_ref_static::<[&i32]>(), None);

        let mut value: [&'static u32; 3] = [&1, &2, &3];
        let value: &mut [&'static u32] = &mut value; // Reference itself it not 'static.
        assert_eq!(
            value.try_specialize_mut_static::<[&u32]>(),
            Some(&mut [&1, &2, &3][..])
        );
        assert_eq!(value.try_specialize_mut_static::<[&i32]>(), None);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_try_specialize_ignore_lifetimes() {
        // SAFETY: In real code the developer should ensure that `T1` and `T2`
        // types have same lifetimes.
        unsafe fn try_spec_erased<T1, T2>(value: T1) -> Result<T2, T1> {
            value.try_specialize_ignore_lifetimes()
        }

        fn is_foobar_cow<'a, T>(value: Cow<'a, T>) -> bool
        where
            T: ?Sized + ToOwned,
        {
            // SAFETY: Specialization from `Cow<'a, T>` to `Cow<'a, str>`
            // will always have equal lifetimes because `str` is [`LifetimeFree`].
            unsafe {
                try_spec_erased::<_, Cow<'a, str>>(value).map_or(false, |value| value == "foobar")
            }
        }

        let value = String::from("foo") + "bar";
        let value = Cow::Borrowed(value.as_str());
        assert!(is_foobar_cow(value));
        assert!(!is_foobar_cow(Cow::Borrowed("foo")));
        assert!(!is_foobar_cow(Cow::Borrowed(&123)));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_try_specialize_ref_ignore_lifetimes() {
        #[expect(
            clippy::redundant_allocation,
            reason = "`Box` type is passed on purpose."
        )]
        fn with_non_static_box<'a>(mut value: Box<&'a u32>) {
            let mut expected = value.clone();
            assert_eq!(
                // SAFETY: Okay in test.
                unsafe {
                    value
                        .clone()
                        .try_specialize_ignore_lifetimes::<Box<&'a u32>>()
                },
                Ok(expected.clone())
            );

            assert_eq!(
                // SAFETY: Okay in test.
                unsafe { value.try_specialize_ref_ignore_lifetimes::<Box<&'a u32>>() },
                Some(&expected)
            );

            assert_eq!(
                // SAFETY: Okay in test.
                unsafe { value.try_specialize_mut_ignore_lifetimes::<Box<&'a u32>>() },
                Some(&mut expected)
            );
        }

        let mut value = 12;
        value += 23;
        let value: Box<&u32> = Box::new(&value);
        with_non_static_box(value);
    }

    #[test]
    fn test_try_specialize_mut() {
        let value1 = &mut [1_u32, 2, 3][..];
        let value2 = &mut [1_u32, 2, 3][..];
        assert_eq!(value1.try_specialize_mut::<[u32]>(), Some(value2));
        assert_eq!(value1.try_specialize_mut::<[i32]>(), None);
        assert_eq!(value1.try_specialize_mut::<str>(), None);
        assert_eq!(value1.try_specialize_mut::<str>(), None);

        let value2 = &mut [1_u32, 2, 3][..];
        assert_eq!(<[u32]>::try_specialize_from_mut(value1), Some(value2));
        assert_eq!(<&'static str>::try_specialize_from_mut(value1), None);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_alloc_try_specialize() {
        assert_eq!(specialized_to_string(123_i32), "123: i32");
        assert_eq!(specialized_to_string(234_u32), "234: u32");
        assert_eq!(specialized_to_string(345_i16), "345: ???");
        assert_eq!(specialized_to_string(456_u16), "456: ???");
    }

    #[test]
    fn test_should_not_impl_try_specialize_static_with_non_static_target() {
        #[expect(clippy::trivially_copy_pass_by_ref, reason = "intentionally")]
        fn scoped<'a>(_: &'a u32) {
            type LocalFn<'a> = fn(&'a str) -> u32;
            type StaticFn = LocalFn<'static>;

            // Types `TypeId` are equal.
            assert!(type_eq_ignore_lifetimes::<StaticFn, LocalFn<'a>>());

            // But you can convert non-`'static` fn to `'static` one.
            let func: Option<LocalFn<'a>> = None;
            #[expect(clippy::unwrap_used, reason = "okay in tests")]
            let _func: Option<StaticFn> = func.try_specialize_static().unwrap();

            // The reverse will fail to compile.
            // let func: Option<StaticFn> = None;
            // let func: Option<LocalFn<'a>> =
            //     func.try_specialize_static().unwrap();
        }

        let value = 123;
        scoped(&value);
    }
}
