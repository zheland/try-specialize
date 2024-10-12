#![no_std]
#![cfg_attr(docsrs, feature(doc_cfg))]

//! The `try-specialize` crate provides limited, [zero-cost](#zero-cost)
//! specialization in generic context on stable Rust.
//!
//! ```rust
//! use try_specialize::TrySpecialize;
//!
//! fn example_specialize_by_value<T>(value: T) -> Result<u32, T> {
//!     value.try_specialize()
//! }
//!
//! fn example_specialize_by_ref<T: ?Sized>(value: &T) -> Option<&str> {
//!     value.try_specialize_ref()
//! }
//! #
//! # assert_eq!(example_specialize_by_value(123_u32), Ok(123));
//! # assert_eq!(example_specialize_by_value(123_i32), Err(123));
//! # assert_eq!(example_specialize_by_ref("foo"), Some("foo"));
//! # assert_eq!(example_specialize_by_ref(&123), None);
//! # assert_eq!(example_specialize_by_ref(&[1, 2, 3]), None);
//! ```
//!
//! # Introduction
//!
//! While specialization in Rust can be a tempting solution in many use cases,
//! I encourage you to reconsider using traits instead as a more idiomatic
//! alternatives. The use of traits is the idiomatic way to achieve polymorphism
//! in Rust, promoting better code clarity, reusability, and maintainability.
//!
//! However the specialization in Rust can be suitable when you need to
//! optimize performance by providing specialized optimized implementations
//! for some types without altering the code logic. Also it can be useful
//! in highly specific type-level programming related usecases like
//! comparisons between types from different libraries.
//!
//! For a simple use cases, I recommend checking out the [`castaway`] crate,
//! which offers a much simpler API and is easier to work with. On nightly Rust,
//! I recommend to use [`min_specialization`] feature instead. Note that Rust
//! standard library can and already use [`min_specialization`] in stable for
//! many optimizations. For a more detailed comparison, see the
//! [Alternative crates](#alternative-crates) section below.
//!
//! # About
//!
//! This crate provides a comprehensive API for solving various specialization
//! challenges to save you from using `unsafe` code or at least to take over
//! some of the checks. This crate provides specialization from unconstrained
//! types, to unconstrained types, between `'static` types, between types
//! references and mutable references, and more.
//!
//! <a name="zero-cost"></a> Library tests ensure that the
//! specializations are performed at compile time, fully optimized and do not
//! come with any run-time cost with `opt-level >= 1`. Note that [release]
//! profile uses `opt-level = 3` by default.
//!
//! # Usage
//!
//! Add this to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! try-specialize = "0.1.0"
//! ```
//!
//! Then, in most cases, it will be enough to use [`TrySpecialize`] trait
//! methods like [`TrySpecialize::try_specialize`],
//! [`TrySpecialize::try_specialize_ref`] and
//! [`TrySpecialize::try_specialize_static`]. If you want to check the
//! possibility of specialization in advance and then use it infallibly multiple
//! times including using reversed or mapped specialization, check
//! [`Specialization`] struct methods.
//!
//! Note that even in expression position, unlike casting, [subtyping], and
//! [coercion], specialization does not alter the underlying type or its data.
//! It only qualifies the underlying types of generics. Specialization from a
//! generic type `T1` to another generic type `T2` succeeds only when the
//! underlying types of T1 and T2 are equal.
//!
//! # Examples
//!
//! Specialize type to any [`LifetimeFree`] type:
//! ```rust
//! # #[cfg(feature = "alloc")] {
//! use try_specialize::TrySpecialize;
//!
//! fn func<T>(value: T) {
//!     match value.try_specialize::<(u32, String)>() {
//!         Ok(value) => specialized_impl(value),
//!         Err(value) => default_impl(value),
//!     }
//! }
//! # fn specialized_impl(_value: (u32, String)) {}
//! # fn default_impl<T>(_value: T) {}
//! # func((42_u32, "abc".to_owned()));
//! # func((42_i32, "abc".to_owned()));
//! # }
//! ```
//!
//! Specialize `'static` type to any `'static` type:
//! ```rust
//! use try_specialize::TrySpecialize;
//!
//! fn func<T>(value: T)
//! where
//!     T: 'static,
//! {
//!     match value.try_specialize_static::<(u32, &'static str)>() {
//!         Ok(value) => specialized_impl(value),
//!         Err(value) => default_impl(value),
//!     }
//! }
//! # fn specialized_impl(_value: (u32, &'static str)) {}
//! # fn default_impl<T>(_value: T) {}
//! # func((42_u32, "abc"));
//! # func((42_i32, "abc"));
//! ```
//!
//! Specialize `Sized` or `Unsized` type reference to any [`LifetimeFree`] type
//! reference:
//! ```rust
//! use try_specialize::TrySpecialize;
//!
//! fn func<T>(value: &T)
//! where
//!     T: ?Sized, // Relax the implicit `Sized` bound.
//! {
//!     match value.try_specialize_ref::<str>() {
//!         Some(value) => specialized_impl(value),
//!         None => default_impl(value),
//!     }
//! }
//! # fn specialized_impl(_value: &str) {}
//! # fn default_impl<T: ?Sized>(_value: &T) {}
//! # func("abc");
//! # func(&42);
//! ```
//!
//! Specialize `Sized` or `Unsized` type mutable reference to any
//! [`LifetimeFree`] type mutable reference:
//! ```rust
//! use try_specialize::TrySpecialize;
//!
//! fn func<T>(value: &mut T)
//! where
//!     T: ?Sized, // Relax the implicit `Sized` bound.
//! {
//!     match value.try_specialize_mut::<[u8]>() {
//!         Some(value) => specialized_impl(value),
//!         None => default_impl(value),
//!     }
//! }
//! # fn specialized_impl(_value: &mut [u8]) {}
//! # fn default_impl<T: ?Sized>(_value: &mut T) {
//! #     core::hint::black_box(());
//! # }
//! # func(&mut [1_u8, 2, 3][..]);
//! # func(&mut [1_i8, 2, 3][..]);
//! ```
//!
//! Specialize a third-party library container with generic types:
//! ```rust
//! use try_specialize::{Specialization, TypeFn};
//!
//! fn func<K, V>(value: hashbrown::HashMap<K, V>) {
//!     struct MapIntoHashMap;
//!     impl<K, V> TypeFn<(K, V)> for MapIntoHashMap {
//!         type Output = hashbrown::HashMap<K, V>;
//!     }
//!
//!     if let Some(spec) = Specialization::<(K, V), (u32, char)>::try_new() {
//!         let spec = spec.map::<MapIntoHashMap>();
//!         let value: hashbrown::HashMap<u32, char> = spec.specialize(value);
//!         specialized_impl(value);
//!     } else {
//!         default_impl(value);
//!     }
//! }
//! # fn default_impl<K, V>(_value: hashbrown::HashMap<K, V>) {}
//! # fn specialized_impl(_value: hashbrown::HashMap<u32, char>) {}
//! # func([(12_u32, 'a'), (23_u32, 'b')].into_iter().collect());
//! # func([(12_i32, 'a'), (23_i32, 'b')].into_iter().collect());
//! ```
//!
//! You can also check out a more comprehensive example that implements custom
//! data encoders and decoders with customizable per-type encoding and decoding
//! errors and optimized byte array encoding and decoding. The full example is
//! available at at: [`examples/encode.rs`].
//! The part of the example related to the `Encode` implementation for a slice:
//! ```rust
//! # use core::convert::Infallible;
//! # use core::{array, slice};
//! # use std::io::{self, Read, Write};
//! #
//! # use try_specialize::{Specialization, TypeFn};
//! #
//! # pub trait Encode {
//! #     type EncodeError;
//! #     fn encode_to<W>(&self, writer: &mut W) -> Result<(), Self::EncodeError>
//! #     where
//! #         W: ?Sized + Write;
//! # }
//! #
//! # pub trait Decode: Sized {
//! #     type DecodeError;
//! #     fn decode_from<R>(reader: &mut R) -> Result<Self, Self::DecodeError>
//! #     where
//! #         R: ?Sized + Read;
//! # }
//! #
//! # impl Encode for () {
//! #     type EncodeError = Infallible;
//! #
//! #     #[inline]
//! #     fn encode_to<W>(&self, _writer: &mut W) -> Result<(), Self::EncodeError>
//! #     where
//! #         W: ?Sized + Write,
//! #     {
//! #         Ok(())
//! #     }
//! # }
//! #
//! # impl Decode for () {
//! #     type DecodeError = Infallible;
//! #
//! #     #[inline]
//! #     fn decode_from<R>(_reader: &mut R) -> Result<Self, Self::DecodeError>
//! #     where
//! #         R: ?Sized + Read,
//! #     {
//! #         Ok(())
//! #     }
//! # }
//! #
//! # impl<T> Encode for Box<T>
//! # where
//! #     T: Encode,
//! # {
//! #     type EncodeError = T::EncodeError;
//! #
//! #     #[inline]
//! #     fn encode_to<W>(&self, writer: &mut W) -> Result<(), Self::EncodeError>
//! #     where
//! #         W: ?Sized + Write,
//! #     {
//! #         T::encode_to(self, writer)
//! #     }
//! # }
//! #
//! # impl<T> Decode for Box<T>
//! # where
//! #     T: Decode,
//! # {
//! #     type DecodeError = T::DecodeError;
//! #
//! #     #[inline]
//! #     fn decode_from<R>(reader: &mut R) -> Result<Self, Self::DecodeError>
//! #     where
//! #         R: ?Sized + Read,
//! #     {
//! #         Ok(Self::new(T::decode_from(reader)?))
//! #     }
//! # }
//! #
//! # impl Encode for u8 {
//! #     type EncodeError = io::Error;
//! #
//! #     #[inline]
//! #     fn encode_to<W>(&self, writer: &mut W) -> Result<(), Self::EncodeError>
//! #     where
//! #         W: ?Sized + Write,
//! #     {
//! #         writer.write_all(&[*self])?;
//! #         Ok(())
//! #     }
//! # }
//! #
//! # impl Decode for u8 {
//! #     type DecodeError = io::Error;
//! #
//! #     #[inline]
//! #     fn decode_from<R>(reader: &mut R) -> Result<Self, Self::DecodeError>
//! #     where
//! #         R: ?Sized + Read,
//! #     {
//! #         let mut byte: Self = 0;
//! #         reader.read_exact(slice::from_mut(&mut byte))?;
//! #         Ok(byte)
//! #     }
//! # }
//! // ...
//!
//! impl<T> Encode for [T]
//! where
//!     T: Encode,
//! {
//!     type EncodeError = T::EncodeError;
//!
//!     #[inline]
//!     fn encode_to<W>(&self, writer: &mut W) -> Result<(), Self::EncodeError>
//!     where
//!         W: ?Sized + Write,
//!     {
//!         if let Some(spec) = Specialization::<[T], [u8]>::try_new() {
//!             // Specialize self from `[T; N]` to `[u32; N]`
//!             let bytes: &[u8] = spec.specialize_ref(self);
//!             // Map type specialization to its associated error specialization.
//!             let spec_err = spec.rev().map::<MapToEncodeError>();
//!             writer
//!                 .write_all(bytes)
//!                 // Specialize error from `io::Error` to `Self::EncodeError`.
//!                 .map_err(|err| spec_err.specialize(err))?;
//!         } else {
//!             for item in self {
//!                 item.encode_to(writer)?;
//!             }
//!         }
//!         Ok(())
//!     }
//! }
//!
//! // ...
//! # impl<T, const N: usize> Encode for [T; N]
//! # where
//! #     T: Encode,
//! # {
//! #     type EncodeError = T::EncodeError;
//! #
//! #     #[inline]
//! #     fn encode_to<W>(&self, writer: &mut W) -> Result<(), Self::EncodeError>
//! #     where
//! #         W: ?Sized + Write,
//! #     {
//! #         self.as_slice().encode_to(writer)
//! #     }
//! # }
//! #
//! # impl<T, const N: usize> Decode for [T; N]
//! # where
//! #     T: Decode + Default,
//! # {
//! #     type DecodeError = T::DecodeError;
//! #
//! #     #[inline]
//! #     fn decode_from<R>(reader: &mut R) -> Result<Self, Self::DecodeError>
//! #     where
//! #         R: ?Sized + Read,
//! #     {
//! #         let spec = Specialization::<[T; N], [u8; N]>::try_new();
//! #
//! #         if let Some(spec) = spec {
//! #             let mut array = [0; N];
//! #             reader
//! #                 .read_exact(&mut array)
//! #                 // Specialize `<[u8; N]>::Error` to `<[T; N]>::Error`
//! #                 .map_err(|err| spec.rev().map::<MapToDecodeError>().specialize(err))?;
//! #             // Specialize `[u8; N]` to `[T; N]`
//! #             let array = spec.rev().specialize(array);
//! #             Ok(array)
//! #         } else {
//! #             // In real code it can be done without `Default` bound.
//! #             // But then the code would be unnecessarily complex for the example.
//! #             let mut array = array::from_fn(|_| T::default());
//! #             for item in &mut array {
//! #                 *item = T::decode_from(reader)?;
//! #             }
//! #             Ok(array)
//! #         }
//! #     }
//! # }
//! #
//! # struct MapToEncodeError;
//! #
//! # impl<T> TypeFn<T> for MapToEncodeError
//! # where
//! #     T: ?Sized + Encode,
//! # {
//! #     type Output = T::EncodeError;
//! # }
//! #
//! # struct MapToDecodeError;
//! # impl<T> TypeFn<T> for MapToDecodeError
//! # where
//! #     T: Decode,
//! # {
//! #     type Output = T::DecodeError;
//! # }
//! #
//! # let mut array_buf = [0; 8];
//! # let mut buf = &mut array_buf[..];
//! # [1_u8, 2, 3].encode_to(&mut buf).unwrap();
//! # 4_u8.encode_to(&mut buf).unwrap();
//! # [(), (), (), ()].encode_to(&mut buf).unwrap();
//! # [5_u8, 6, 7, 8].map(Box::new).encode_to(&mut buf).unwrap();
//! # assert!(9_u8.encode_to(&mut buf).is_err());
//! # assert!([9_u8, 10].encode_to(&mut buf).is_err());
//! # ().encode_to(&mut buf).unwrap();
//! # [(), (), ()].encode_to(&mut buf).unwrap();
//! # assert!([9_u8, 10].map(Box::new).encode_to(&mut buf).is_err());
//! # assert_eq!(array_buf, [1, 2, 3, 4, 5, 6, 7, 8]);
//! #
//! # let buf = &mut array_buf.as_slice();
//! # assert_eq!(u8::decode_from(buf).unwrap(), 1);
//! # assert_eq!(<[u8; 4]>::decode_from(buf).unwrap(), [2, 3, 4, 5]);
//! # assert_eq!(<[(); 16]>::decode_from(buf).unwrap(), [(); 16]);
//! # assert_eq!(<[u8; 1]>::decode_from(buf).unwrap(), [6]);
//! # assert_eq!(
//! #     <[Box<u8>; 2]>::decode_from(buf).unwrap(),
//! #     [Box::new(7), Box::new(8)]
//! # );
//! # assert!(u8::decode_from(buf).is_err());
//! # assert!(<[u8; 1]>::decode_from(buf).is_err());
//! # assert_eq!(<[(); 2]>::decode_from(buf).unwrap(), [(); 2]);
//! # assert!(<[Box<u8>; 2]>::decode_from(buf).is_err());
//! ```
//!
//! Find values by type in generic composite types:
//! ```rust
//! use try_specialize::{LifetimeFree, TrySpecialize};
//!
//! pub trait ConsListLookup {
//!     fn find<T>(&self) -> Option<&T>
//!     where
//!         T: ?Sized + LifetimeFree;
//! }
//!
//! impl ConsListLookup for () {
//!     #[inline]
//!     fn find<T>(&self) -> Option<&T>
//!     where
//!         T: ?Sized + LifetimeFree,
//!     {
//!         None
//!     }
//! }
//!
//! impl<T1, T2> ConsListLookup for (T1, T2)
//! where
//!     T2: ConsListLookup,
//! {
//!     #[inline]
//!     fn find<T>(&self) -> Option<&T>
//!     where
//!         T: ?Sized + LifetimeFree,
//!     {
//!         self.0.try_specialize_ref().or_else(|| self.1.find::<T>())
//!     }
//! }
//!
//! #[derive(Eq, PartialEq, Debug)]
//! struct StaticStr(&'static str);
//! // SAFETY: It is safe to implement `LifetimeFree` for structs with no
//! // parameters.
//! unsafe impl LifetimeFree for StaticStr {}
//!
//! let input = (
//!     123_i32,
//!     (
//!         [1_u32, 2, 3, 4],
//!         (1_i32, (StaticStr("foo"), (('a', false), ()))),
//!     ),
//! );
//!
//! assert_eq!(input.find::<u32>(), None);
//! assert_eq!(input.find::<i32>(), Some(&123_i32));
//! assert_eq!(input.find::<[u32; 4]>(), Some(&[1, 2, 3, 4]));
//! assert_eq!(input.find::<[u32]>(), None);
//! assert_eq!(input.find::<StaticStr>(), Some(&StaticStr("foo")));
//! assert_eq!(input.find::<char>(), None);
//! assert_eq!(input.find::<(char, bool)>(), Some(&('a', false)));
//! ```
//!
//! # Documentation
//!
//! [API Documentation]
//!
//! # Feature flags
//!
//! - `alloc` (implied by `std`, enabled by default): enables [`LifetimeFree`]
//!   implementations for `alloc` types, like `Box`, `Arc`, `String`, `Vec`,
//!   `BTreeMap` etc.
//! - `std` (enabled by default): enables `alloc` feature and [`LifetimeFree`]
//!   implementations for `std` types, like `OsStr`, `Path`, `PathBuf`,
//!   `Instant`, `HashMap` etc.
//! - `unreliable`: enables unreliable functions, methods and macros that rely
//!   on Rust standard library undocumented behavior. See [`unreliable`] module
//!   documentation for details.
//!
//! # How it works
//!
//! - Type comparison when both types are `'static` is performed using
//!   [`TypeId::of`] comparison.
//! - Type comparison when one of types is [`LifetimeFree`] is performed by
//!   converting type wrapped as `&dyn PhantomData<T>` to `&dyn PhantomData<T> +
//!   'static` and comparing their [`TypeId::of`].
//! - Specialization is performed using type comparison and [`transmute_copy`]
//!   when the equality of types is proved.
//! - Unreliable trait implementation check is performed using an expected, but
//!   undocumented behavior of the Rust stdlib [`PartialEq`] implementation for
//!   [`Arc<T>`]. [`Arc::eq`] uses fast path comparing references before
//!   comparing data if `T` implements [`Eq`].
//!
//! # Alternative crates
//!
//! - [`castaway`]: A very similar crate and a great simpler alternative that
//!   can cover most usecases. Its macro uses [Autoref-Based Specialization] and
//!   automatically determines the appropriate type of specialization, making it
//!   much easier to use. However, if no specialization is applicable because of
//!   the same [Autoref-Based Specialization], the compiler generates completely
//!   unclear errors, which makes it difficult to use it in complex cases. Uses
//!   `unsafe` code for type comparison and specialization.
//! - [`coe-rs`]: Smaller and simpler, but supports only static types and don't
//!   safely combine type equality check and specialization. Uses `unsafe` code
//!   for type specialization.
//! - [`downcast-rs`]: Specialized on trait objects (`dyn`) downcasting. Can't
//!   be used to specialize unconstrained types. Doesn't use `unsafe` code.
//! - [`syllogism`] and [`syllogism_macro`]: Requires to provide all possible
//!   types to macro that generate a lot of boilerplate code and can't be used
//!   to specialize stdlib types because of orphan rules. Doesn't use `unsafe`
//!   code.
//! - [`specialize`](https://crates.io/crates/specialize): Requires nightly.
//!   Adds a simple macro to inline nightly [`min_specialization`] usage into
//!   simple `if let` expressions.
//! - [`specialized-dispatch`]: Requires nightly. Adds a macro to inline nightly
//!   [`min_specialization`] usage into a `match`-like macro.
//! - [`spez`]: Specializes expression types, using[Autoref-Based
//!   Specialization]. It won't works in generic context but can be used in the
//!   code generated by macros.
//! - [`impls`]: Determine if a type implements a trait. Can't detect erased
//!   type bounds, so not applicable in generic context, but can be used in the
//!   code generated by macros.
//!
//! ## Comparison of libraries supporting specialization in generic context:
//!
//! |  | crate <br /> `try-specialize` | crate <br /> [`castaway`] | crate <br /> [`coe-rs`] | crate <br /> [`downcast-rs`] | crate <br /> [`syllogism`] | [`min_spec...`] <br /> nightly feature | crate <br /> [`specialize`](https://crates.io/crates/specialize) | crate <br /> [`spec...ch`]
//! | --: | :--: | :--: | :--: | :--: | :--: | :--: | :--: | :--: |
//! | Rust toolchain | **Stable** | **Stable** | **Stable** | **Stable** | **Stable** | Nightly | Nightly | Nightly  |
//! | API complexity | Complex | **Simple** | **Simple** | Moderate | **Simple** | **Simple** | **Simple** | **Simple** |
//! | API difficulty | Difficult | **Easy** | **Easy** | Moderate | Moderate | **Easy** | **Easy** | Moderate |
//! | Zero-cost (compile-time optimized) | **YES** | **YES** | **YES** | no | **YES** | **YES** | **YES** | **YES** |
//! | Safely combines type eq check and specialization | **YES** | **YES** | no | **YES** | **YES** | **YES** |**YES** | **YES** |
//! | Specialize value references | **YES** | **YES** | **YES** | N/A | **YES** | **YES** | **YES** | no |
//! | Specialize values | **YES** | **YES** | no | N/A | **YES** | **YES** | **YES** | **YES** |
//! | Specialize values without consume on failure | **YES** | **YES** | no | N/A | **YES** | **YES** | no | **YES** |
//! | Limited non-static value specialization | **YES** | **YES** | no | N/A | **YES** | **YES** | **YES** | **YES** |
//! | Full non-static value specialization | no | no | no | N/A | **YES** | no | no | no |
//! | Specialize trait objects (`dyn`) | N/A | N/A | N/A | **YES** | N/A | N/A | N/A | N/A |
//! | Compare types without instantiation | **YES** | no | **YES** | no | **YES** | **YES** | **YES** | no |
//! | Support std types | **YES** | **YES** | **YES** | **YES** | no | **YES** | **YES** | **YES** |
//! | Specialize from unconstrained type | **YES** | **YES** | no | no | no | **YES** | **YES** | **YES** |
//! | Specialize to unconstrained type | **YES** | no | no | no | no | **YES** | **YES** | **YES** |
//! | Check generic implements "erased" trait | **YES**, but [`unreliable`] | no | no | no | no | **YES** | **YES** | **YES** |
//! | Specialize to generic with added bounds | no | no | no | no | no | **YES** | **YES** | **YES** |
//! | API based on | Traits | Macros | Traits | Macros + Traits | Traits | Language | Macros | Macros |
//! | Type comparison implementation based on | [`TypeId`] <br /> + [`transmute`] | [`TypeId`] <br /> + [`transmute`] |[`TypeId`] | N/A | Traits | Language | Nightly <br /> feature | Nightly <br /> feature |
//! | Type casting implementation based on | [`transmute_copy`] | [`ptr::read`] | [`transmute`] | [`std::any::Any`] | Traits | Language | Nightly <br /> feature | Nightly <br /> feature |
//! | Implementation free of `unsafe` | no | no | no | **YES** | **YES** | **YES** | **YES** | **YES** |
//!
//! ## Primitive example of the value specialization using different libraries
//!
//! <table><tbody><tr><td style="vertical-align: top">
//!
//! crate `try_specialize`:
//!
//! ```rust
//! use try_specialize::TrySpecialize;
//!
//! fn spec<T>(value: T) -> Result<u32, T> {
//!     value.try_specialize()
//! }
//!
//! assert_eq!(spec(42_u32), Ok(42));
//! assert_eq!(spec(42_i32), Err(42));
//! assert_eq!(spec("abc"), Err("abc"));
//! ```
//!
//! </td><td style="vertical-align: top">
//!
//! crate [`castaway`]:
//!
//! ```rust
//! use castaway::cast;
//!
//! fn spec<T>(value: T) -> Result<u32, T> {
//!     cast!(value, _)
//! }
//!
//! assert_eq!(spec(42_u32), Ok(42));
//! assert_eq!(spec(42_i32), Err(42));
//! assert_eq!(spec("abc"), Err("abc"));
//! ```
//!
//! </td></tr><tr><td style="vertical-align: top">
//!
//! crate [`coe-rs`]:
//!
//! ```rust
//! use coe::{is_same, Coerce};
//!
//! // Library don't support non-reference.
//! // specialization. Using reference.
//! fn spec<T>(value: &T) -> Option<&u32>
//! where
//!     // Library don't support specialization of
//!     // unconstrained non-static types.
//!     T: 'static,
//! {
//!     is_same::<u32, T>().then(|| value.coerce())
//! }
//!
//! fn main() {
//!     assert_eq!(spec(&42_u32), Some(&42));
//!     assert_eq!(spec(&42_i32), None);
//!     assert_eq!(spec(&"abc"), None);
//! }
//! ```
//!
//! </td><td style="vertical-align: top">
//!
//! crates [`downcast-rs`]:
//!
//! ```rust
//! use downcast_rs::{impl_downcast, DowncastSync};
//!
//! trait Base: DowncastSync {}
//! impl_downcast!(sync Base);
//!
//! // Library requires all specializable
//! // types to be defined in advance.
//! impl Base for u32 {}
//! impl Base for i32 {}
//! impl Base for &'static str {}
//!
//! // Library support only trait objects (`dyn`).
//! fn spec(value: &dyn Base) -> Option<&u32> {
//!     value.downcast_ref::<u32>()
//! }
//!
//! fn main() {
//!     assert_eq!(spec(&42_u32), Some(&42));
//!     assert_eq!(spec(&42_i32), None);
//!     assert_eq!(spec(&"abc"), None);
//! }
//! ```
//!
//! </td></tr><tr><td style="vertical-align: top">
//!
//! crate [`specialize`](https://crates.io/crates/specialize):
//!
//! ```rust
//! # #![cfg_attr(feature = "__test_nightly", feature(min_specialization))]
//! # #[cfg(feature = "__test_nightly")] {
//! // Requires nightly.
//! #![feature(min_specialization)]
//!
//! use specialize::constrain;
//!
//! // Library don't support non-consuming
//! // value specialization. Using reference.
//! fn spec<T: ?Sized>(value: &T) -> Option<&u32> {
//!     constrain!(ref value as u32)
//! }
//!
//! assert_eq!(spec(&42_u32), Some(&42));
//! assert_eq!(spec(&42_i32), None);
//! assert_eq!(spec("abc"), None);
//! # }
//! ```
//!
//! </td><td style="vertical-align: top">
//!
//! crate [`specialized-dispatch`]:
//! ```rust
//! # #![cfg_attr(feature = "__test_nightly", feature(min_specialization))]
//! # #[cfg(feature = "__test_nightly")] {
//! // Requires nightly.
//! #![feature(min_specialization)]
//!
//! use specialized_dispatch::specialized_dispatch;
//!
//! // The library don't support using generics.
//! // from outer item. Using `Option`.
//! fn spec<T>(value: T) -> Option<u32> {
//!     specialized_dispatch! {
//!         T -> Option<u32>,
//!         fn (value: u32) => Some(value),
//!         default fn <T>(_: T) => None,
//!         value,
//!     }
//! }
//!
//! assert_eq!(spec(42_u32), Some(42));
//! assert_eq!(spec(42_i32), None);
//! assert_eq!(spec("abc"), None);
//! # }
//! ```
//!
//! </td></tr><tr><td style="vertical-align: top">
//!
//! crates [`syllogism`] and [`syllogism_macro`]:
//!
//! ```rust
//! # #[rustfmt::skip]
//! use syllogism::{Distinction, Specialize};
//! use syllogism_macro::impl_specialization;
//!
//! // Library specialization can not be
//! // implemented for std types because of
//! // orphan rules. Using custom local types.
//! #[derive(Eq, PartialEq, Debug)]
//! struct U32(u32);
//! #[derive(Eq, PartialEq, Debug)]
//! struct I32(i32);
//! #[derive(Eq, PartialEq, Debug)]
//! struct Str<'a>(&'a str);
//!
//! // Library requires all specializable
//! // types to be defined in one place.
//! impl_specialization!(
//!     type U32;
//!     type I32;
//!     type Str<'a>;
//! );
//!
//! fn spec<T>(value: T) -> Result<U32, T>
//! where
//!     T: Specialize<U32>,
//! {
//!     match value.specialize() {
//!         Distinction::Special(value) => Ok(value),
//!         Distinction::Generic(value) => Err(value),
//!     }
//! }
//!
//! assert_eq!(spec(U32(42)), Ok(U32(42)));
//! assert_eq!(spec(I32(42_i32)), Err(I32(42)));
//! assert_eq!(spec(Str("abc")), Err(Str("abc")));
//! ```
//!
//! </td><td style="vertical-align: top">
//!
//! [`min_specialization`] nightly feature:
//!
//! ```rust
//! # #![cfg_attr(feature = "__test_nightly", feature(min_specialization))]
//! # #[cfg(feature = "__test_nightly")] {
//! // Requires nightly.
//! #![feature(min_specialization)]
//!
//! // The artificial example looks a bit long.
//! // More real-world use cases are usually
//! // on the contrary more clear and understandable.
//! pub trait Spec: Sized {
//!     fn spec(self) -> Result<u32, Self>;
//! }
//!
//! impl<T> Spec for T {
//!     default fn spec(self) -> Result<u32, Self> {
//!         Err(self)
//!     }
//! }
//!
//! impl Spec for u32 {
//!     fn spec(self) -> Result<u32, Self> {
//!         Ok(self)
//!     }
//! }
//!
//! assert_eq!(Spec::spec(42_u32), Ok(42));
//! assert_eq!(Spec::spec(42_i32), Err(42));
//! assert_eq!(Spec::spec("abc"), Err("abc"));
//! # }
//! ```
//!
//! </td></tr></tbody></table>
//!
//! # License
//!
//! Licensed under either of
//!
//! - Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or <https://www.apache.org/licenses/LICENSE-2.0>)
//! - MIT license ([LICENSE-MIT](LICENSE-MIT) or <https://opensource.org/licenses/MIT>)
//!
//! at your option.
//!
//! # Contribution
//!
//! Unless you explicitly state otherwise, any contribution intentionally
//! submitted for inclusion in the work by you, as defined in the Apache-2.0
//! license, shall be dual licensed as above, without any
//! additional terms or conditions.
//!
//! [API Documentation]: https://docs.rs/try-specialize
//! [subtyping]: https://doc.rust-lang.org/nomicon/subtyping.html
//! [coercion]: https://doc.rust-lang.org/nomicon/coercions.html
//! [release]: https://doc.rust-lang.org/cargo/reference/profiles.html#release
//! [`min_specialization`]: https://github.com/rust-lang/rust/pull/68970
//! [`min_spec...`]: https://github.com/rust-lang/rust/pull/68970 "min_specialization"
//!
//! [`examples/encode.rs`]: https://github.com/zheland/try-specialize/blob/v0.1.0/examples/encode.rs
//!
//! [`TypeId`]: std::any::TypeId
//! [`TypeId::of`]: std::any::TypeId::of
//! [`transmute`]: https://doc.rust-lang.org/std/mem/fn.transmute.html "std::mem::transmute"
//! [`transmute_copy`]: std::mem::transmute_copy
//! [`ptr::read`]: std::ptr::read
//! [`PartialEq`]: std::cmp::PartialEq
//! [`Eq`]: std::cmp::Eq
//! [`Arc::eq`]: std::sync::Arc::eq "<std::sync::Arc as PartialEq>::eq"
//! [`Arc<T>`]: std::sync::Arc
//!
//! [`try_new`]: Specialization::try_new
//! [`try_new_static`]: Specialization::try_new_static
//! [`try_new_ignore_lifetimes`]: Specialization::try_new_ignore_lifetimes
//! [`rev`]: Specialization::rev
//! [`map`]: Specialization::map
//! [`specialize`]: Specialization::specialize
//! [`specialize_ref`]: Specialization::specialize_ref
//! [`specialize_mut`]: Specialization::specialize_mut
//!
//! [`WeakSpecialization`]: unreliable::WeakSpecialization
//! [`try_new_if_lifetime_free_weak`]: unreliable::WeakSpecialization::try_new_if_lifetime_free_weak
//!
//! [`try_specialize`]: TrySpecialize::try_specialize
//! [`try_specialize_ref`]: TrySpecialize::try_specialize_ref
//! [`try_specialize_from`]: TrySpecialize::try_specialize_from
//! [`try_specialize_from_ref`]: TrySpecialize::try_specialize_from_ref
//! [`try_specialize_static`]: TrySpecialize::try_specialize_static
//! [`try_specialize_ref_static`]: TrySpecialize::try_specialize_ref_static
//! [`..._ignore_lifetimes`]: TrySpecialize::try_specialize_ignore_lifetimes
//! [`..._ref_ignore_lifetimes`]: TrySpecialize::try_specialize_ref_ignore_lifetimes
//! [`..._mut_ignore_lifetimes`]: TrySpecialize::try_specialize_mut_ignore_lifetimes
//!
//! [`TrySpecializeWeak`]: unreliable::TrySpecializeWeak
//! [`..._if_lifetime_free_weak`]: unreliable::TrySpecializeWeak::try_specialize_if_lifetime_free_weak
//! [`..._ref_if_lifetime_free_weak`]: unreliable::TrySpecializeWeak::try_specialize_ref_if_lifetime_free_weak
//! [`..._mut_if_lifetime_free_weak`]: unreliable::TrySpecializeWeak::try_specialize_mut_if_lifetime_free_weak
//!
//! [`castaway`]: https://crates.io/crates/castaway
//! [`syllogism`]: https://crates.io/crates/syllogism
//! [`syllogism_macro`]: https://crates.io/crates/syllogism_macro
//! [`specialized-dispatch`]: https://crates.io/crates/specialized-dispatch
//! [`spec...ch`]: https://crates.io/crates/specialized-dispatch "specialized-dispatch"
//! [`spez`]: https://crates.io/crates/spez
//! [`coe-rs`]: https://crates.io/crates/coe-rs
//! [`downcast-rs`]: https://crates.io/crates/downcast-rs
//! [`impls`]: https://crates.io/crates/impls
//!
//! [Autoref-Based Specialization]: https://lukaskalbertodt.github.io/2019/12/05/generalized-autoref-based-specialization.html

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

mod lifetime_free;
mod specialization;
mod try_specialize;
mod type_eq;
mod type_fn;

#[cfg(all(feature = "alloc", feature = "unreliable"))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "alloc", feature = "unreliable"))))]
pub mod unreliable;

pub use lifetime_free::*;
pub use specialization::*;
pub use try_specialize::*;
pub use type_eq::*;
pub use type_fn::*;

#[cfg(all(test, not(doc)))]
mod integration_tests_deps {
    use {paste as _, rustversion as _, version_sync as _};
}

#[cfg(all(test, not(doc)))]
mod doc_tests_deps {
    use {
        castaway as _, coe as _, downcast_rs as _, hashbrown as _, specialize as _,
        specialized_dispatch as _, syllogism as _, syllogism_macro as _,
    };
}

#[doc(hidden)]
#[cfg(all(feature = "alloc", feature = "unreliable"))]
pub mod macro_deps {
    pub use alloc::rc::Rc;
}
