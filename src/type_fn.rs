/// A trait that defines a mapping between an input type and an output type.
///
/// This trait is used to map specialization types to other wrapped or
/// associated specialization types. If generic types `T1` and `T2` are proven
/// to be equivalent, then types `<Mapper as TypeFn<T1>>::Output` and
/// `<Mapper as TypeFn<T2>>::Output` are also equivalent.
///
/// This trait can also be used to specialize
/// generics of the third-party library types that do not implement
/// [`LifetimeFree`].
///
/// [`LifetimeFree`]: crate::LifetimeFree
///
/// # Examples
///
/// Custom data encoders and decoders with customizable per-type encoding
/// and decoding errors and optimized byte array encoding and decoding.
/// Full example code is available at
/// [`examples/encode.rs`](https://github.com/zheland/try-specialize/blob/v0.1.1/examples/encode.rs).
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
/// # impl<T> Encode for Box<T>
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
/// #         T::encode_to(self, writer)
/// #     }
/// # }
/// #
/// # impl<T> Decode for Box<T>
/// # where
/// #     T: Decode,
/// # {
/// #     type DecodeError = T::DecodeError;
/// #
/// #     #[inline]
/// #     fn decode_from<R>(reader: &mut R) -> Result<Self, Self::DecodeError>
/// #     where
/// #         R: ?Sized + Read,
/// #     {
/// #         Ok(Self::new(T::decode_from(reader)?))
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
/// # let mut array_buf = [0; 8];
/// # let mut buf = &mut array_buf[..];
/// # [1_u8, 2, 3].encode_to(&mut buf).unwrap();
/// # 4_u8.encode_to(&mut buf).unwrap();
/// # [(), (), (), ()].encode_to(&mut buf).unwrap();
/// # [5_u8, 6, 7, 8].map(Box::new).encode_to(&mut buf).unwrap();
/// # assert!(9_u8.encode_to(&mut buf).is_err());
/// # assert!([9_u8, 10].encode_to(&mut buf).is_err());
/// # ().encode_to(&mut buf).unwrap();
/// # [(), (), ()].encode_to(&mut buf).unwrap();
/// # assert!([9_u8, 10].map(Box::new).encode_to(&mut buf).is_err());
/// # assert_eq!(array_buf, [1, 2, 3, 4, 5, 6, 7, 8]);
/// #
/// # let buf = &mut array_buf.as_slice();
/// # assert_eq!(u8::decode_from(buf).unwrap(), 1);
/// # assert_eq!(<[u8; 4]>::decode_from(buf).unwrap(), [2, 3, 4, 5]);
/// # assert_eq!(<[(); 16]>::decode_from(buf).unwrap(), [(); 16]);
/// # assert_eq!(<[u8; 1]>::decode_from(buf).unwrap(), [6]);
/// # assert_eq!(
/// #     <[Box<u8>; 2]>::decode_from(buf).unwrap(),
/// #     [Box::new(7), Box::new(8)]
/// # );
/// # assert!(u8::decode_from(buf).is_err());
/// # assert!(<[u8; 1]>::decode_from(buf).is_err());
/// # assert_eq!(<[(); 2]>::decode_from(buf).unwrap(), [(); 2]);
/// # assert!(<[Box<u8>; 2]>::decode_from(buf).is_err());
/// ```
///
/// We can't use `reader.read_exact(&mut array)?;` in the example above because
/// its error variant is `io::Error` while the function error variant is
/// `T::Error`. But we can use the same specialization, but reversed and mapped:
/// - `[T; N] => [u8; N]`,
/// - with `.rev()`: `[u8; N] => [T; N]`,
/// - with `.map::<MapError>()`: `<[u8; N] as Decode>::Error => <[T; N] as
///   Decode>::Error`,
/// - and for the compiler `<[u8; N] as Decode>::Error` and `io::Error` are
///   equal types, so we can specialize the error as well: `io::Error => <[T; N]
///   as Decode>::Error`.
///
/// Truncated synthetic example with multiple generics specialization for a
/// third-party type:
/// ```rust
/// # #[cfg(feature = "std")] {
/// use try_specialize::{Specialization, TypeFn};
///
/// fn some_generic_fn<K, V>(value: hashbrown::HashMap<K, V>) -> &'static str {
///     struct MapIntoHashMap;
///     impl<K, V> TypeFn<(K, V)> for MapIntoHashMap {
///         type Output = hashbrown::HashMap<K, V>;
///     }
///
///     if let Some(spec) = Specialization::<(K, V), (u32, char)>::try_new() {
///         let spec = spec.map::<MapIntoHashMap>();
///         let value = spec.specialize(value);
///         specialized_impl(value)
///     } else {
///         default_impl(value)
///     }
/// }
///
/// fn default_impl<K, V>(value: hashbrown::HashMap<K, V>) -> &'static str {
///     // ...
/// #     "default impl"
/// }
///
/// fn specialized_impl(value: hashbrown::HashMap<u32, char>) -> &'static str {
///     // ...
/// #     "specialized impl"
/// }
/// #
/// # assert_eq!(
/// #     some_generic_fn([(0_i32, 'a'), (1, 'b'), (2, 'c')].into_iter().collect()),
/// #     "default impl"
/// # );
/// #
/// # assert_eq!(
/// #     some_generic_fn(
/// #         [(0_u32, "zero"), (1, "one"), (2, "two")]
/// #             .into_iter()
/// #             .collect()
/// #     ),
/// #     "default impl"
/// # );
/// #
/// # assert_eq!(
/// #     some_generic_fn([(0_u32, 'a'), (1, 'b'), (2, 'c')].into_iter().collect()),
/// #     "specialized impl"
/// # );
/// # }
/// ```
pub trait TypeFn<T>
where
    T: ?Sized,
{
    /// The returned type.
    type Output: ?Sized;
}
