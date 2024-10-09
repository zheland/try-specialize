#![allow(missing_docs, reason = "okay in examples")]
#![expect(
    clippy::missing_errors_doc,
    unused_crate_dependencies,
    reason = "okay in examples"
)]

//! This example implements custom data encoders and decoders with customizable
//! per-type encoding and decoding errors and optimized byte array encoding and
//! decoding.
//!
//! Both encoder and decoder tries to specialize `[T; N]` to `[u8; N]`
//! in order to branch to better-optimized bytes slice reader and writers.
//!
//! Also it uses:
//! - `Specialization::rev` to convert read `[u8; N]` back to `[T; N]`.
//! - `Specialization::map` to convert read `<[u8; N]>::Error` to `<[T;
//!   N]>::Error`.

use core::convert::Infallible;
use core::{array, slice};
use std::io::{self, Read, Write};

use try_specialize::{Specialization, TypeFn};

pub trait Encode {
    type EncodeError;
    fn encode_to<W>(&self, writer: &mut W) -> Result<(), Self::EncodeError>
    where
        W: ?Sized + Write;
}

pub trait Decode: Sized {
    type DecodeError;
    fn decode_from<R>(reader: &mut R) -> Result<Self, Self::DecodeError>
    where
        R: ?Sized + Read;
}

impl Encode for () {
    type EncodeError = Infallible;

    #[inline]
    fn encode_to<W>(&self, _writer: &mut W) -> Result<(), Self::EncodeError>
    where
        W: ?Sized + Write,
    {
        Ok(())
    }
}

impl Decode for () {
    type DecodeError = Infallible;

    #[inline]
    fn decode_from<R>(_reader: &mut R) -> Result<Self, Self::DecodeError>
    where
        R: ?Sized + Read,
    {
        Ok(())
    }
}

impl Encode for u8 {
    type EncodeError = io::Error;

    #[inline]
    fn encode_to<W>(&self, writer: &mut W) -> Result<(), Self::EncodeError>
    where
        W: ?Sized + Write,
    {
        writer.write_all(&[*self])?;
        Ok(())
    }
}

impl Decode for u8 {
    type DecodeError = io::Error;

    #[inline]
    fn decode_from<R>(reader: &mut R) -> Result<Self, Self::DecodeError>
    where
        R: ?Sized + Read,
    {
        let mut byte: Self = 0;
        reader.read_exact(slice::from_mut(&mut byte))?;
        Ok(byte)
    }
}

impl<T> Encode for [T]
where
    T: Encode,
{
    type EncodeError = T::EncodeError;

    #[inline]
    fn encode_to<W>(&self, writer: &mut W) -> Result<(), Self::EncodeError>
    where
        W: ?Sized + Write,
    {
        if let Some(spec) = Specialization::<[T], [u8]>::try_new() {
            // Specialize self from `[T; N]` to `[u32; N]`
            let bytes: &[u8] = spec.specialize_ref(self);
            // Map type specialization to its associated error specialization.
            let spec_err = spec.rev().map::<MapToEncodeError>();
            writer
                .write_all(bytes)
                // Specialize error from `io::Error` to `Self::EncodeError`.
                .map_err(|err| spec_err.specialize(err))?;
        } else {
            for item in self {
                item.encode_to(writer)?;
            }
        }
        Ok(())
    }
}

impl<T, const N: usize> Encode for [T; N]
where
    T: Encode,
{
    type EncodeError = T::EncodeError;

    #[inline]
    fn encode_to<W>(&self, writer: &mut W) -> Result<(), Self::EncodeError>
    where
        W: ?Sized + Write,
    {
        self.as_slice().encode_to(writer)
    }
}

impl<T, const N: usize> Decode for [T; N]
where
    T: Decode + Default,
{
    type DecodeError = T::DecodeError;

    #[inline]
    fn decode_from<R>(reader: &mut R) -> Result<Self, Self::DecodeError>
    where
        R: ?Sized + Read,
    {
        let spec = Specialization::<[T; N], [u8; N]>::try_new();

        if let Some(spec) = spec {
            let mut array = [0; N];
            reader
                .read_exact(&mut array)
                // Specialize `<[u8; N]>::Error` to `<[T; N]>::Error`
                .map_err(|err| spec.rev().map::<MapToDecodeError>().specialize(err))?;
            // Specialize `[u8; N]` to `[T; N]`
            let array = spec.rev().specialize(array);
            Ok(array)
        } else {
            // In real code it can be done without `Default` bound.
            // But then the code would be unnecessarily complex for the example.
            let mut array = array::from_fn(|_| T::default());
            for item in &mut array {
                *item = T::decode_from(reader)?;
            }
            Ok(array)
        }
    }
}

struct MapToEncodeError;

impl<T> TypeFn<T> for MapToEncodeError
where
    T: ?Sized + Encode,
{
    type Output = T::EncodeError;
}

struct MapToDecodeError;
impl<T> TypeFn<T> for MapToDecodeError
where
    T: Decode,
{
    type Output = T::DecodeError;
}

#[expect(clippy::unwrap_used, reason = "okay in examples")]
fn main() {
    let mut buf = Vec::new();
    [1_u8, 2, 3].encode_to(&mut buf).unwrap();
    4_u8.encode_to(&mut buf).unwrap();
    [(), (), (), ()].encode_to(&mut buf).unwrap();
    [5_u8, 6].encode_to(&mut buf).unwrap();
    assert_eq!(buf, [1, 2, 3, 4, 5, 6]);
    let buf = &mut buf.as_slice();
    assert_eq!(u8::decode_from(buf).unwrap(), 1);
    assert_eq!(<[u8; 4]>::decode_from(buf).unwrap(), [2, 3, 4, 5]);
    assert_eq!(<[(); 16]>::decode_from(buf).unwrap(), [(); 16]);
    assert_eq!(<[u8; 1]>::decode_from(buf).unwrap(), [6]);
    assert!(u8::decode_from(buf).is_err());
}
