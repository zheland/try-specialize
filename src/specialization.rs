use core::cmp::Ordering;
use core::fmt::{Debug, Formatter, Result as FmtResult};
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::mem::{transmute_copy, ManuallyDrop};

use crate::{static_type_eq, type_eq, type_eq_ignore_lifetimes, LifetimeFree, TypeFn};

/// A zero-sized marker struct that guarantees type equality between `T1` and
/// `T2`.
///
/// This struct provides a type-safe mechanism to specialize one type into
/// another, enforcing that `T1` and `T2` are identical concrete types. It can
/// only be instantiated when both types are the same.
///
/// `Specialization` trait refers to a lower-level API. Prefer to use
/// [`TrySpecialize`] trait methods if applicable.
///
/// Library tests ensure that the specializations are fully optimized and
/// become zero-cost with `opt-level >= 1`. Note that release profile uses
/// `opt-level = 3` by default.
///
/// Constructors cheat sheet:
/// | Type bounds | Constructor |
/// |:--:|:--:|
/// | `T1: 'static + LifetimeFree` | [`try_new`] |
/// | `T2: 'static + LifetimeFree` | [`try_new`] + [`rev`] |
/// | `T1: 'static, T2: 'static` | [`try_new_static`] |
/// | underlying type maybe impls `LifetimeFree` | [`try_new_if_lifetime_free_weak`] |
/// | `unsafe`, without lifetimes check | [`try_new_ignore_lifetimes`] |
///
/// Specialization methods cheat sheet:
/// | From | To | Method |
/// |:--:|:--:|:--:|
/// | `T1` | `T2` | [`specialize`] |
/// | `&T1` | `&T2` | [`specialize_ref`] |
/// | `&mut T1` | `&mut T2` | [`specialize_mut`] |
/// | `T2` | `T1` | [`rev`] + [`specialize`] |
/// | `Wrapper<T1>` | `Wrapper<T2>` | [`map`] + [`specialize`] |
/// | `T1::AssociatedType` | `T2::AssociatedType` | [`map`] + [`specialize`] |
///
/// [`TrySpecialize`]: crate::TrySpecialize
/// [`try_new`]: Specialization::try_new
/// [`rev`]: Specialization::rev
/// [`map`]: Specialization::map
/// [`try_new_static`]: Specialization::try_new_static
/// [`try_new_if_lifetime_free_weak`]: crate::unreliable::WeakSpecialization::try_new_if_lifetime_free_weak
/// [`try_new_ignore_lifetimes`]: Specialization::try_new_ignore_lifetimes
/// [`specialize`]: Specialization::specialize
/// [`specialize_ref`]: Specialization::specialize_ref
/// [`specialize_mut`]: Specialization::specialize_mut
pub struct Specialization<T1, T2>(PhantomData<T1>, PhantomData<T2>)
where
    T1: ?Sized,
    T2: ?Sized;

impl<T1, T2> Specialization<T1, T2>
where
    T1: ?Sized,
    T2: ?Sized,
{
    /// Checks the types `T1` and `T2` for equality and returns the
    /// specialization provider if types are equal.
    ///
    /// Note that this method requires source type to implement `LifetimeFree`.
    /// Use `Specialization::try_new().rev()` method to check the target
    /// type instead.
    /// `LifetimeFree` is not automatically derived and implemented only for a
    /// set of types without lifetimes.
    ///
    /// For simple cases consider using [`TrySpecialize`] methods like
    /// [`try_specialize`],
    /// [`try_specialize_ref`], and
    /// [`try_specialize_mut`] instead.
    ///
    /// You can use [`Specialization::try_new_static`] if both types are
    /// `'static`.
    ///
    /// # Examples
    ///
    /// Same-type stringifiable type concatenation, that don't allocate memory
    /// if one of the arguments is empty `&str`:
    /// ```rust
    /// use core::fmt::Display;
    /// use std::borrow::Cow;
    /// use std::format;
    ///
    /// use try_specialize::Specialization;
    ///
    /// fn concat_same<'a, T>(first: &'a T, second: &'a T) -> Cow<'a, str>
    /// where
    ///     T: ?Sized + Display,
    /// {
    ///     if let Some(spec) = Specialization::<T, str>::try_new() {
    ///         match (spec.specialize_ref(first), spec.specialize_ref(second)) {
    ///             (first, "") => Cow::Borrowed(first),
    ///             ("", second) => Cow::Borrowed(second),
    ///             (first, second) => Cow::Owned([first, second].concat()),
    ///         }
    ///     } else {
    ///         Cow::Owned(format!("{first}{second}"))
    ///     }
    /// }
    ///
    /// assert!(matches!(concat_same("foo", "bar"), Cow::Owned(v) if v == "foobar"));
    /// assert!(matches!(concat_same("foo", ""), Cow::Borrowed("foo")));
    /// assert!(matches!(concat_same("", "bar"), Cow::Borrowed("bar")));
    /// let foo = String::from("foo");
    /// let bar = String::from("bar");
    /// assert!(matches!(concat_same(&foo, &bar), Cow::Owned(v) if v == "foobar"));
    /// assert!(matches!(concat_same(&123, &456), Cow::Owned(v) if v == "123456"));
    /// ```
    ///
    /// Generate a placeholder with non-default value for some types:
    /// ```rust
    /// use try_specialize::Specialization;
    ///
    /// fn placeholder<T>() -> T
    /// where
    ///     T: Default,
    /// {
    ///     if let Some(spec) = Specialization::<T, u8>::try_new() {
    ///         spec.rev().specialize(12)
    ///     } else if let Some(spec) = Specialization::<T, u32>::try_new() {
    ///         spec.rev().specialize(42)
    ///     } else if let Some(spec) = Specialization::<T, f64>::try_new() {
    ///         spec.rev().specialize(123.456)
    ///     // ...
    ///     } else {
    ///         T::default()
    ///     }
    /// }
    ///
    /// assert_eq!(placeholder::<&'static str>(), "");
    /// assert_eq!(placeholder::<u8>(), 12);
    /// assert_eq!(placeholder::<(u8, u8)>(), (0, 0));
    /// assert_eq!(placeholder::<u32>(), 42);
    /// assert_eq!(placeholder::<f64>(), 123.456);
    /// assert_eq!(placeholder::<i128>(), 0);
    /// ```
    ///
    /// [`TrySpecialize`]: crate::TrySpecialize
    /// [`try_specialize`]: crate::TrySpecialize::try_specialize
    /// [`try_specialize_ref`]: crate::TrySpecialize::try_specialize_ref
    /// [`try_specialize_mut`]: crate::TrySpecialize::try_specialize_mut
    #[inline]
    #[must_use]
    pub fn try_new() -> Option<Self>
    where
        T2: LifetimeFree,
    {
        // SAFETY: `T1` can be specialized to `T2` if the types are equal.
        type_eq::<T1, T2>().then_some(unsafe { Self::new_unchecked() })
    }

    /// Checks the types `T1` and `T2` for equality and returns the
    /// specialization provider if types are equal.
    ///
    /// Note that this method requires both types to have `'static` lifetime,
    /// but don't require any type to implement `LifetimeFree`.
    ///
    /// For simple cases consider using [`TrySpecialize`] methods like
    /// [`try_specialize_static`],
    /// [`try_specialize_ref_static`], and
    /// [`try_specialize_mut_static`] instead.
    ///
    /// You can use [`Specialization::try_new`] if the target type
    /// implements [`LifetimeFree`] trait or
    /// `Specialization::try_new().rev()` if the source type implements
    /// [`LifetimeFree`] trait.
    ///
    /// # Examples
    ///
    /// Collection reverse function with optimized specializations for `Vec<T>`
    /// and `Box<[T]>`:
    /// ```rust
    /// use core::sync::atomic::{AtomicU32, Ordering as AtomicOrdering};
    /// use std::collections::VecDeque;
    ///
    /// use try_specialize::Specialization;
    ///
    /// static DEBUG_SPEC_USED: AtomicU32 = AtomicU32::new(0);
    ///
    /// fn reverse_collection<T>(value: T) -> T
    /// where
    ///     T: 'static + IntoIterator + FromIterator<T::Item>,
    ///     T::IntoIter: DoubleEndedIterator,
    /// {
    ///     let spec1 = Specialization::<T, Vec<T::Item>>::try_new_static();
    ///     let spec2 = Specialization::<T, Box<[T::Item]>>::try_new_static();
    ///
    ///     if let Some(spec1) = spec1 {
    ///         DEBUG_SPEC_USED.store(101, AtomicOrdering::Relaxed);
    ///         let mut vec = spec1.specialize(value);
    ///         vec.reverse();
    ///         spec1.rev().specialize(vec)
    ///     } else if let Some(spec2) = spec2 {
    ///         DEBUG_SPEC_USED.store(202, AtomicOrdering::Relaxed);
    ///         let mut boxed = spec2.specialize(value);
    ///         boxed.reverse();
    ///         spec2.rev().specialize(boxed)
    ///     } else {
    ///         DEBUG_SPEC_USED.store(303, AtomicOrdering::Relaxed);
    ///         value.into_iter().rev().collect()
    ///     }
    /// }
    ///
    /// assert_eq!(reverse_collection(vec![1, 2, 3]), vec![3, 2, 1]);
    /// assert_eq!(DEBUG_SPEC_USED.load(AtomicOrdering::Relaxed), 101);
    ///
    /// assert_eq!(
    ///     reverse_collection(vec![1, 2, 3].into_boxed_slice()),
    ///     vec![3, 2, 1].into_boxed_slice()
    /// );
    /// assert_eq!(DEBUG_SPEC_USED.load(AtomicOrdering::Relaxed), 202);
    ///
    /// assert_eq!(
    ///     reverse_collection(VecDeque::from([1, 2, 3])),
    ///     VecDeque::from([3, 2, 1])
    /// );
    /// assert_eq!(DEBUG_SPEC_USED.load(AtomicOrdering::Relaxed), 303);
    /// ```
    ///
    /// Same-type stringifiable type concatenation, that don't allocate memory
    /// if one of the arguments is empty `&'static str` and avoid reallocations
    /// if one of the arguments is empty `String`:
    /// ```rust
    /// use core::fmt::Display;
    /// use std::borrow::Cow;
    ///
    /// use try_specialize::Specialization;
    ///
    /// fn concat_same<T>(first: T, second: T) -> Cow<'static, str>
    /// where
    ///     T: 'static + Display,
    /// {
    ///     if let Some(spec) = Specialization::<T, &'static str>::try_new_static() {
    ///         match (spec.specialize(first), spec.specialize(second)) {
    ///             (first, "") => Cow::Borrowed(first),
    ///             ("", second) => Cow::Borrowed(second),
    ///             (first, second) => Cow::Owned([first, second].concat()),
    ///         }
    ///     } else if let Some(spec) = Specialization::<T, String>::try_new_static() {
    ///         let first = spec.specialize(first);
    ///         let second = spec.specialize(second);
    ///         match (first.is_empty(), second.is_empty()) {
    ///             (false | true, true) => Cow::Owned(first),
    ///             (true, false) => Cow::Owned(second),
    ///             (false, false) => Cow::Owned(first + &second),
    ///         }
    ///     } else {
    ///         Cow::Owned(format!("{first}{second}"))
    ///     }
    /// }
    ///
    /// assert!(matches!(concat_same("foo", "bar"), Cow::Owned(v) if v == "foobar"));
    /// assert!(matches!(concat_same("foo", ""), Cow::Borrowed("foo")));
    /// assert!(matches!(concat_same("", "bar"), Cow::Borrowed("bar")));
    /// let foo = String::from("foo");
    /// let bar = String::from("bar");
    /// assert!(matches!(concat_same(foo, bar), Cow::Owned(v) if v == "foobar"));
    /// let empty = String::new();
    /// let bar = String::from("bar");
    /// assert!(matches!(concat_same(empty, bar), Cow::Owned(v) if v == "bar"));
    /// let foo = String::from("foo");
    /// let empty = String::new();
    /// assert!(matches!(concat_same(foo, empty), Cow::Owned(v) if v == "foo"));
    /// assert!(matches!(concat_same(123, 456), Cow::Owned(v) if v == "123456"));
    /// ```
    ///
    /// Generate a placeholder with non-default value for some types:
    /// ```rust
    /// use try_specialize::Specialization;
    ///
    /// fn placeholder<T>() -> T
    /// where
    ///     T: 'static + Default,
    /// {
    ///     if let Some(spec) = Specialization::<T, &'static str>::try_new_static() {
    ///         spec.rev().specialize("dummy string")
    ///     } else if let Some(spec) = Specialization::<T, u32>::try_new() {
    ///         spec.rev().specialize(42)
    ///     } else if let Some(spec) = Specialization::<T, f64>::try_new() {
    ///         spec.rev().specialize(123.456)
    ///     // ...
    ///     } else {
    ///         T::default()
    ///     }
    /// }
    ///
    /// assert_eq!(placeholder::<&'static str>(), "dummy string");
    /// assert_eq!(placeholder::<(u8, u8)>(), (0, 0));
    /// assert_eq!(placeholder::<u32>(), 42);
    /// assert_eq!(placeholder::<f64>(), 123.456);
    /// assert_eq!(placeholder::<i128>(), 0);
    /// ```
    ///
    /// [`TrySpecialize`]: crate::TrySpecialize
    /// [`try_specialize_static`]: crate::TrySpecialize::try_specialize_static
    /// [`try_specialize_ref_static`]: crate::TrySpecialize::try_specialize_ref_static
    /// [`try_specialize_mut_static`]: crate::TrySpecialize::try_specialize_mut_static
    #[inline]
    #[must_use]
    pub fn try_new_static() -> Option<Self>
    where
        T1: 'static,
        T2: 'static,
    {
        // SAFETY: `T1` can be specialized to `T2` if the types are equal.
        static_type_eq::<T1, T2>().then_some(unsafe { Self::new_unchecked() })
    }

    /// Checks the types `T1` and `T2` for equality and returns the
    /// specialization provider if the types are equal ignoring lifetimes.
    ///
    /// For simple cases consider using [`TrySpecialize`] methods like
    /// [`try_specialize_ignore_lifetimes`],
    /// [`try_specialize_ref_ignore_lifetimes`], and
    /// [`try_specialize_mut_ignore_lifetimes`] instead.
    ///
    /// # Safety
    ///
    /// This method doesn't validate type lifetimes. Lifetimes equality should
    /// be validated separately.
    ///
    /// # Examples
    ///
    /// Specialized to third-party library item that can definitely be
    /// `LifetimeFree`.
    /// ```rust
    /// mod third_party_lib {
    ///     #[derive(Eq, PartialEq, Default, Debug)]
    ///     pub struct Marker(pub u32);
    /// }
    ///
    /// use third_party_lib::Marker;
    /// use try_specialize::Specialization;
    ///
    /// fn inc_if_marker<T>(value: T) -> T {
    ///     // SAFETY: `Marker` type has no lifetime parameters.
    ///     if let Some(spec) = unsafe { Specialization::<T, Marker>::try_new_ignore_lifetimes() } {
    ///         spec.rev().specialize(Marker(spec.specialize(value).0 + 1))
    ///     } else {
    ///         value
    ///     }
    /// }
    ///
    /// assert_eq!(inc_if_marker(123), 123);
    /// assert_eq!(inc_if_marker("str"), "str");
    /// assert_eq!(inc_if_marker(Marker(123)), Marker(124));
    /// ```
    ///
    /// [`TrySpecialize`]: crate::TrySpecialize
    /// [`try_specialize_ignore_lifetimes`]: crate::TrySpecialize::try_specialize_ignore_lifetimes
    /// [`try_specialize_ref_ignore_lifetimes`]: crate::TrySpecialize::try_specialize_ref_ignore_lifetimes
    /// [`try_specialize_mut_ignore_lifetimes`]: crate::TrySpecialize::try_specialize_mut_ignore_lifetimes
    #[inline]
    #[must_use]
    pub unsafe fn try_new_ignore_lifetimes() -> Option<Self> {
        // SAFETY: `T1` can be specialized to `T2` if the caller guarantees that
        // type lifetimes are equal.
        type_eq_ignore_lifetimes::<T1, T2>().then_some(unsafe { Self::new_unchecked() })
    }

    /// Construct a new `Specialization<T1, T2>` without any types
    /// equality checks.
    ///
    /// # Safety
    ///
    /// Calling this method for `Specialization<T1, T2>` with different
    /// types in `T1` and `T2` is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    #[must_use]
    pub const unsafe fn new_unchecked() -> Self {
        Self(PhantomData, PhantomData)
    }

    /// Reverses the specialization.
    ///
    /// It can be used to convert the target type back to source type and also
    /// to create a specialization from a type which implements `LifetimeFree`,
    /// for example: `Specialization::<u8, T>::new().rev()`.
    ///
    /// For simple cases consider using [`TrySpecialize`] methods like
    /// [`try_specialize_from`],
    /// [`try_specialize_from_ref`], and
    /// [`try_specialize_from_mut`] instead.
    ///
    /// # Examples
    ///
    /// Synthetic example with custom behavior for `u32` type:
    /// ```rust
    /// use try_specialize::{LifetimeFree, Specialization};
    ///
    /// fn inc_if_u32<T>(value: T) -> T
    /// where
    ///     T: LifetimeFree,
    /// {
    ///     if let Some(spec) = Specialization::<T, u32>::try_new() {
    ///         spec.rev().specialize(spec.specialize(value) + 1)
    ///     } else {
    ///         value
    ///     }
    /// }
    ///
    /// assert_eq!(inc_if_u32(123_u32), 124);
    /// assert_eq!(inc_if_u32(123_i32), 123);
    /// assert_eq!(inc_if_u32(123_u8), 123);
    /// ```
    ///
    /// More realistic example can be found at
    /// [`examples/encode.rs`](https://github.com/zheland/try-specialize/blob/v0.1.0/examples/encode.rs).
    ///
    /// [`TrySpecialize`]: crate::TrySpecialize
    /// [`try_specialize_from`]: crate::TrySpecialize::try_specialize_from
    /// [`try_specialize_from_ref`]: crate::TrySpecialize::try_specialize_from_ref
    /// [`try_specialize_from_mut`]: crate::TrySpecialize::try_specialize_from_mut
    #[inline]
    #[must_use]
    pub const fn rev(&self) -> Specialization<T2, T1> {
        Specialization(PhantomData, PhantomData)
    }

    /// Maps the specialization types to other types using a specified
    /// `TypeFn`.
    ///
    /// This can be useful to specialize third-party wrappers or the trait
    /// associated types if they are based on `LifetimeFree` types.
    ///
    /// # Examples
    ///
    /// Simplified custom vec-like type processing optimization example:
    /// ```rust
    /// mod third_party_lib {
    ///     pub struct CustomVec<T> {
    /// #       pub inner: Vec<T>
    ///         // ...
    ///     }
    /// }
    ///
    /// use third_party_lib::CustomVec;
    /// use try_specialize::{Specialization, TypeFn};
    ///
    /// fn process<T>(data: CustomVec<T>) {
    ///     struct MapIntoCustomVec;
    ///     impl<T> TypeFn<T> for MapIntoCustomVec {
    ///         type Output = CustomVec<T>;
    ///     }
    ///
    ///     if let Some(spec) = Specialization::<T, u8>::try_new() {
    ///         let data: CustomVec<u8> = spec.map::<MapIntoCustomVec>().specialize(data);
    ///         // optimized specialized implementation...
    ///     } else {
    ///         // default implementation...
    ///     }
    /// }
    /// # process(CustomVec { inner: vec![1_u8, 2, 3] });
    /// # process(CustomVec { inner: vec![1_i8, 2, 3] });
    /// ```
    ///
    /// Simplified custom `hashbrown::HashMap` type processing optimization
    /// example with multiple type generics:
    /// ```rust
    /// use hashbrown::HashMap;
    /// use try_specialize::{Specialization, TypeFn};
    ///
    /// fn process<K, V>(data: HashMap<K, V>)
    /// where
    ///     K: 'static,
    ///     V: 'static,
    /// {
    ///     struct MapIntoHashMap;
    ///     impl<K, V> TypeFn<(K, V)> for MapIntoHashMap {
    ///         type Output = HashMap<K, V>;
    ///     }
    ///
    ///     if let Some(spec) = Specialization::<(K, V), (char, char)>::try_new_static() {
    ///         let data: HashMap<char, char> = spec.map::<MapIntoHashMap>().specialize(data);
    ///         // optimized specialized implementation...
    ///     } else if let Some(spec) = Specialization::<(K, V), (String, String)>::try_new_static() {
    ///         let data: HashMap<String, String> = spec.map::<MapIntoHashMap>().specialize(data);
    ///         // optimized specialized implementation...
    ///     } else {
    ///         // default implementation...
    ///     }
    /// }
    /// # process([('a', 'b'), ('c', 'd')].into_iter().collect());
    /// # process(
    /// #     [
    /// #         ("foo".to_owned(), "abc".to_owned()),
    /// #         ("bar".to_owned(), "def".to_owned()),
    /// #     ]
    /// #     .into_iter()
    /// #     .collect(),
    /// # );
    /// # process([(123, 234), (345, 456)].into_iter().collect());
    /// ```
    ///
    /// Custom data encoders and decoders with customizable per-type encoding
    /// and decoding errors and optimized byte array encoding and decoding.
    /// Full example code is available at
    /// [`examples/encode.rs`](https://github.com/zheland/try-specialize/blob/v0.1.0/examples/encode.rs).
    /// ```rust
    /// # use core::convert::Infallible;
    /// # use core::{array, slice};
    /// # use std::io::{self, Read, Write};
    /// #
    /// # use try_specialize::{Specialization, TypeFn};
    /// #
    /// # pub trait Encode {
    /// #     type EncodeError;
    /// #     fn encode_to<W>(&self, writer: &mut W) -> Result<(), Self::EncodeError>
    /// #     where
    /// #         W: ?Sized + Write;
    /// # }
    /// #
    /// # pub trait Decode: Sized {
    /// #     type DecodeError;
    /// #     fn decode_from<R>(reader: &mut R) -> Result<Self, Self::DecodeError>
    /// #     where
    /// #         R: ?Sized + Read;
    /// # }
    /// #
    /// # impl Encode for () {
    /// #     type EncodeError = Infallible;
    /// #
    /// #     #[inline]
    /// #     fn encode_to<W>(&self, _writer: &mut W) -> Result<(), Self::EncodeError>
    /// #     where
    /// #         W: ?Sized + Write,
    /// #     {
    /// #         Ok(())
    /// #     }
    /// # }
    /// #
    /// # impl Decode for () {
    /// #     type DecodeError = Infallible;
    /// #
    /// #     #[inline]
    /// #     fn decode_from<R>(_reader: &mut R) -> Result<Self, Self::DecodeError>
    /// #     where
    /// #         R: ?Sized + Read,
    /// #     {
    /// #         Ok(())
    /// #     }
    /// # }
    /// #
    /// # impl Encode for u8 {
    /// #     type EncodeError = io::Error;
    /// #
    /// #     #[inline]
    /// #     fn encode_to<W>(&self, writer: &mut W) -> Result<(), Self::EncodeError>
    /// #     where
    /// #         W: ?Sized + Write,
    /// #     {
    /// #         writer.write_all(&[*self])?;
    /// #         Ok(())
    /// #     }
    /// # }
    /// #
    /// # impl Decode for u8 {
    /// #     type DecodeError = io::Error;
    /// #
    /// #     #[inline]
    /// #     fn decode_from<R>(reader: &mut R) -> Result<Self, Self::DecodeError>
    /// #     where
    /// #         R: ?Sized + Read,
    /// #     {
    /// #         let mut byte: Self = 0;
    /// #         reader.read_exact(slice::from_mut(&mut byte))?;
    /// #         Ok(byte)
    /// #     }
    /// # }
    /// // ...
    ///
    /// impl<T> Encode for [T]
    /// where
    ///     T: Encode,
    /// {
    ///     type EncodeError = T::EncodeError;
    ///
    ///     #[inline]
    ///     fn encode_to<W>(&self, writer: &mut W) -> Result<(), Self::EncodeError>
    ///     where
    ///         W: ?Sized + Write,
    ///     {
    ///         if let Some(spec) = Specialization::<[T], [u8]>::try_new() {
    ///             // Specialize self from `[T; N]` to `[u32; N]`
    ///             let bytes: &[u8] = spec.specialize_ref(self);
    ///             // Map type specialization to its associated error specialization.
    ///             let spec_err = spec.rev().map::<MapToEncodeError>();
    ///             writer
    ///                 .write_all(bytes)
    ///                 // Specialize error from `io::Error` to `Self::EncodeError`.
    ///                 .map_err(|err| spec_err.specialize(err))?;
    ///         } else {
    ///             for item in self {
    ///                 item.encode_to(writer)?;
    ///             }
    ///         }
    ///         Ok(())
    ///     }
    /// }
    ///
    /// // ...
    /// # impl<T, const N: usize> Encode for [T; N]
    /// # where
    /// #     T: Encode,
    /// # {
    /// #     type EncodeError = T::EncodeError;
    /// #
    /// #     #[inline]
    /// #     fn encode_to<W>(&self, writer: &mut W) -> Result<(), Self::EncodeError>
    /// #     where
    /// #         W: ?Sized + Write,
    /// #     {
    /// #         self.as_slice().encode_to(writer)
    /// #     }
    /// # }
    /// #
    /// # impl<T, const N: usize> Decode for [T; N]
    /// # where
    /// #     T: Decode + Default,
    /// # {
    /// #     type DecodeError = T::DecodeError;
    /// #
    /// #     #[inline]
    /// #     fn decode_from<R>(reader: &mut R) -> Result<Self, Self::DecodeError>
    /// #     where
    /// #         R: ?Sized + Read,
    /// #     {
    /// #         let spec = Specialization::<[T; N], [u8; N]>::try_new();
    /// #
    /// #         if let Some(spec) = spec {
    /// #             let mut array = [0; N];
    /// #             reader
    /// #                 .read_exact(&mut array)
    /// #                 // Specialize `<[u8; N]>::Error` to `<[T; N]>::Error`
    /// #                 .map_err(|err| spec.rev().map::<MapToDecodeError>().specialize(err))?;
    /// #             // Specialize `[u8; N]` to `[T; N]`
    /// #             let array = spec.rev().specialize(array);
    /// #             Ok(array)
    /// #         } else {
    /// #             // In real code it can be done without `Default` bound.
    /// #             // But then the code would be unnecessarily complex for the example.
    /// #             let mut array = array::from_fn(|_| T::default());
    /// #             for item in &mut array {
    /// #                 *item = T::decode_from(reader)?;
    /// #             }
    /// #             Ok(array)
    /// #         }
    /// #     }
    /// # }
    /// #
    /// # struct MapToEncodeError;
    /// #
    /// # impl<T> TypeFn<T> for MapToEncodeError
    /// # where
    /// #     T: ?Sized + Encode,
    /// # {
    /// #     type Output = T::EncodeError;
    /// # }
    /// #
    /// # struct MapToDecodeError;
    /// # impl<T> TypeFn<T> for MapToDecodeError
    /// # where
    /// #     T: Decode,
    /// # {
    /// #     type Output = T::DecodeError;
    /// # }
    /// #
    /// # let mut buf = Vec::new();
    /// # [1_u8, 2, 3].encode_to(&mut buf).unwrap();
    /// # 4_u8.encode_to(&mut buf).unwrap();
    /// # [(), (), (), ()].encode_to(&mut buf).unwrap();
    /// # [5_u8, 6].encode_to(&mut buf).unwrap();
    /// # assert_eq!(buf, [1, 2, 3, 4, 5, 6]);
    /// # let buf = &mut buf.as_slice();
    /// # assert_eq!(u8::decode_from(buf).unwrap(), 1);
    /// # assert_eq!(<[u8; 4]>::decode_from(buf).unwrap(), [2, 3, 4, 5]);
    /// # assert_eq!(<[(); 16]>::decode_from(buf).unwrap(), [(); 16]);
    /// # assert_eq!(<[u8; 1]>::decode_from(buf).unwrap(), [6]);
    /// # assert!(u8::decode_from(buf).is_err());
    /// ```
    #[inline]
    #[must_use]
    pub const fn map<M>(
        &self,
    ) -> Specialization<<M as TypeFn<T1>>::Output, <M as TypeFn<T2>>::Output>
    where
        M: TypeFn<T1> + TypeFn<T2>,
    {
        Specialization(PhantomData, PhantomData)
    }

    /// Infallibly specialize value with type `T1` as `T2`.
    ///
    /// This method can only be called for a `Specialization<T1, T2>` whose
    /// existing instance indicates that types `T1` and `T2` are equivalent.
    ///
    /// For simple cases consider using [`TrySpecialize`] methods like
    /// [`try_specialize`],
    /// [`try_specialize_from`], and
    /// [`try_specialize_static`] instead.
    ///
    /// [`TrySpecialize`]: crate::TrySpecialize
    /// [`try_specialize`]: crate::TrySpecialize::try_specialize
    /// [`try_specialize_from`]: crate::TrySpecialize::try_specialize_from
    /// [`try_specialize_static`]: crate::TrySpecialize::try_specialize_static
    #[inline]
    pub fn specialize(&self, value: T1) -> T2
    where
        T1: Sized,
        T2: Sized,
    {
        // SAFETY: `Specialization` can only be constructed if `T1` and
        // `T2` types are equal.
        // SAFETY: `T` and `ManuallyDrop<T>` have the same layout.
        unsafe { transmute_copy::<T1, T2>(&ManuallyDrop::new(value)) }
    }

    /// Infallibly specialize value with type `&T1` as `&T2`.
    ///
    /// This method can only be called for a `Specialization<T1, T2>` whose
    /// existing instance indicates that types `T1` and `T2` are equivalent.
    ///
    /// For simple cases consider using [`TrySpecialize`] methods like
    /// [`try_specialize_ref`],
    /// [`try_specialize_from_ref`], and
    /// [`try_specialize_ref_static`] instead.
    ///
    /// [`TrySpecialize`]: crate::TrySpecialize
    /// [`try_specialize_ref`]: crate::TrySpecialize::try_specialize_ref
    /// [`try_specialize_from_ref`]: crate::TrySpecialize::try_specialize_from_ref
    /// [`try_specialize_ref_static`]: crate::TrySpecialize::try_specialize_ref_static
    #[inline]
    pub const fn specialize_ref<'a>(&self, value: &'a T1) -> &'a T2 {
        // SAFETY: `Specialization` can only be constructed if `T1` and
        // `T2` types are equal.
        unsafe { transmute_copy::<&'a T1, &'a T2>(&value) }
    }

    /// Infallibly specialize value with type `&mut T1` as `&mut T2`.
    ///
    /// This method can only be called for a `Specialization<T1, T2>` whose
    /// existing instance indicates that types `T1` and `T2` are equivalent.
    ///
    /// For simple cases consider using [`TrySpecialize`] methods like
    /// [`try_specialize_mut`],
    /// [`try_specialize_from_mut`], and
    /// [`try_specialize_mut_static`] instead.
    ///
    /// [`TrySpecialize`]: crate::TrySpecialize
    /// [`try_specialize_mut`]: crate::TrySpecialize::try_specialize_mut
    /// [`try_specialize_from_mut`]: crate::TrySpecialize::try_specialize_from_mut
    /// [`try_specialize_mut_static`]: crate::TrySpecialize::try_specialize_mut_static
    #[inline]
    pub fn specialize_mut<'a>(&self, value: &'a mut T1) -> &'a mut T2 {
        // SAFETY: `Specialization` can only be constructed if `T1` and
        // `T2` types are equal.
        unsafe { transmute_copy::<&'a mut T1, &'a mut T2>(&value) }
    }
}

impl<T1, T2> Copy for Specialization<T1, T2>
where
    T1: ?Sized,
    T2: ?Sized,
{
}

impl<T1, T2> Clone for Specialization<T1, T2>
where
    T1: ?Sized,
    T2: ?Sized,
{
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T1, T2> Eq for Specialization<T1, T2>
where
    T1: ?Sized,
    T2: ?Sized,
{
}

impl<T1, T2> PartialEq for Specialization<T1, T2>
where
    T1: ?Sized,
    T2: ?Sized,
{
    #[inline]
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl<T1, T2> Ord for Specialization<T1, T2>
where
    T1: ?Sized,
    T2: ?Sized,
{
    #[inline]
    fn cmp(&self, _: &Self) -> Ordering {
        Ordering::Equal
    }
}

impl<T1, T2> PartialOrd for Specialization<T1, T2>
where
    T1: ?Sized,
    T2: ?Sized,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T1, T2> Hash for Specialization<T1, T2>
where
    T1: ?Sized,
    T2: ?Sized,
{
    #[inline]
    fn hash<H: Hasher>(&self, _: &mut H) {}
}

impl<T1, T2> Debug for Specialization<T1, T2>
where
    T1: ?Sized,
    T2: ?Sized,
{
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Self(f0, f1) => f
                .debug_tuple("Specialization")
                .field(&f0)
                .field(&f1)
                .finish(),
        }
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "std")]
    use alloc::format;
    #[cfg(feature = "std")]
    use core::hash::{Hash, Hasher};
    #[cfg(feature = "std")]
    use std::hash::DefaultHasher;

    use crate::{LifetimeFree, Specialization, TypeFn};

    #[expect(clippy::arithmetic_side_effects, reason = "okay in tests")]
    fn specialized_inc_if_i32_dec_if_u32<T>(value: T) -> T
    where
        T: LifetimeFree,
    {
        if let Some(spec) = Specialization::<T, i32>::try_new() {
            spec.rev().specialize(spec.specialize(value) + 1)
        } else if let Some(spec) = Specialization::<T, u32>::try_new() {
            spec.rev().specialize(spec.specialize(value) - 1)
        } else {
            value
        }
    }

    #[test]
    fn test_checked_specialization() {
        assert_eq!(specialized_inc_if_i32_dec_if_u32(123_i32), 124);
        assert_eq!(specialized_inc_if_i32_dec_if_u32(123_u32), 122);
        assert_eq!(specialized_inc_if_i32_dec_if_u32(123_i16), 123);
        assert_eq!(specialized_inc_if_i32_dec_if_u32(123_u16), 123);
    }

    #[test]
    fn test_checked_specialization_map() {
        #[derive(Eq, PartialEq, Debug)]
        struct Wrapper<T>(T);

        fn as_wrapped_u32_ref<T>(value: &Wrapper<T>) -> Option<&Wrapper<u32>>
        where
            T: LifetimeFree,
        {
            struct MapIntoWrapper;
            impl<T> TypeFn<T> for MapIntoWrapper {
                type Output = Wrapper<T>;
            }

            Some(
                Specialization::<T, u32>::try_new()?
                    .map::<MapIntoWrapper>()
                    .specialize_ref(value),
            )
        }

        assert_eq!(
            as_wrapped_u32_ref(&Wrapper(123_u32)),
            Some(&Wrapper(123_u32))
        );
        assert_eq!(as_wrapped_u32_ref(&Wrapper(123_i32)), None);
        assert_eq!(as_wrapped_u32_ref(&Wrapper((1, 2, 3, 4))), None);
    }

    #[cfg(feature = "std")]
    #[test]
    fn test_checked_specialization_basic_trait_impls() {
        #[expect(clippy::unwrap_used, reason = "Okay in tests")]
        let spec1 = Specialization::<u32, u32>::try_new().unwrap();
        let spec2 = spec1;
        #[expect(clippy::clone_on_copy, reason = "Okay in tests")]
        let _ = spec1.clone();
        assert_eq!(spec1, spec2);
        assert!(spec1 <= spec2);

        let mut hasher = DefaultHasher::new();
        let hash1 = hasher.finish();
        spec1.hash(&mut hasher);
        let hash2 = hasher.finish();
        assert_eq!(hash1, hash2);

        assert_eq!(
            format!("{spec1:?}"),
            "Specialization(PhantomData<u32>, PhantomData<u32>)"
        );
    }
}
