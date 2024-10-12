# try-specialize

[![Build Status](https://github.com/zheland/try-specialize/workflows/build/badge.svg)](https://github.com/zheland/try-specialize/actions)
[![Latest Version](https://img.shields.io/crates/v/try-specialize.svg)](https://crates.io/crates/try-specialize)
[![Documentation](https://docs.rs/try-specialize/badge.svg)](https://docs.rs/try-specialize)
[![Codecov](https://codecov.io/gh/zheland/try-specialize/graph/badge.svg)](https://codecov.io/gh/zheland/try-specialize)
[![Dependencies status](https://deps.rs/repo/github/zheland/try-specialize/status.svg)](https://deps.rs/repo/github/zheland/try-specialize)
[![Downloads](https://img.shields.io/crates/d/try-specialize)](https://crates.io/crates/try-specialize)
[![License](https://img.shields.io/crates/l/try-specialize)](https://github.com/zheland/try-specialize/#license)
[![MSRV 1.81+](https://img.shields.io/badge/rustc-1.81+-blue.svg)](https://blog.rust-lang.org/2024/09/05/Rust-1.81.0.html)

The `try-specialize` crate provides limited, [zero-cost](#zero-cost)
specialization in generic context on stable Rust.

```rust
use try_specialize::TrySpecialize;

fn example_specialize_by_value<T>(value: T) -> Result<u32, T> {
    value.try_specialize()
}

fn example_specialize_by_ref<T: ?Sized>(value: &T) -> Option<&str> {
    value.try_specialize_ref()
}
```

## Introduction

While specialization in Rust can be a tempting solution in many use cases,
it is usually more idiomatic to use traits instead. Traits are the idiomatic
way to achieve polymorphism in Rust, promoting better code clarity,
reusability, and maintainability.

However, specialization can be suitable when you need to optimize
performance by providing specialized implementations for some types without
altering the code logic. It's also useful in specific, type-level
programming use cases like comparisons between types from different
libraries.

For a simple use cases, consider the [`castaway`] crate, which offers a much
simpler API. On nightly Rust, consider using [`min_specialization`] feature
instead. The Rust standard library already uses [`min_specialization`] for
many optimizations. For a more detailed comparison, see the
[Alternative crates](#alternative-crates) section below.

## About

This crate offers a comprehensive API for addressing various specialization
challenges, reducing the need for unsafe code. It provides specialization
from unconstrained types, to unconstrained types, between 'static types,
and between type references and mutable references, and more.

<a name="zero-cost"></a> Library tests ensure that specializations are
performed at compile time and are fully optimized with no runtime cost at
`opt-level >= 1`. Note that the [release] profile uses `opt-level = 3`
by default.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
try-specialize = "0.1.0"
```

Then, you can use [`TrySpecialize`] trait methods like
[`TrySpecialize::try_specialize`], [`TrySpecialize::try_specialize_ref`] and
[`TrySpecialize::try_specialize_static`]. To check the possibility of
specialization in advance and use it infallibly multiple times, including
reversed or mapped specialization, use [`Specialization`] struct methods.

Note that unlike casting, [subtyping], and [coercion], specialization does
not alter the underlying type or data. It merely qualifies the underlying
types of generics, succeeding only when the underlying types of `T1` and
`T2` are equal.

## Examples

Specialize type to any [`LifetimeFree`] type:
```rust
use try_specialize::TrySpecialize;

fn func<T>(value: T) {
    match value.try_specialize::<(u32, String)>() {
        Ok(value) => specialized_impl(value),
        Err(value) => default_impl(value),
    }
}
```

Specialize `'static` type to any `'static` type:
```rust
use try_specialize::TrySpecialize;

fn func<T>(value: T)
where
    T: 'static,
{
    match value.try_specialize_static::<(u32, &'static str)>() {
        Ok(value) => specialized_impl(value),
        Err(value) => default_impl(value),
    }
}
```

Specialize `Sized` or `Unsized` type reference to any [`LifetimeFree`] type
reference:
```rust
use try_specialize::TrySpecialize;

fn func<T>(value: &T)
where
    T: ?Sized, // Relax the implicit `Sized` bound.
{
    match value.try_specialize_ref::<str>() {
        Some(value) => specialized_impl(value),
        None => default_impl(value),
    }
}
```

Specialize `Sized` or `Unsized` type mutable reference to any
[`LifetimeFree`] type mutable reference:
```rust
use try_specialize::TrySpecialize;

fn func<T>(value: &mut T)
where
    T: ?Sized, // Relax the implicit `Sized` bound.
{
    match value.try_specialize_mut::<[u8]>() {
        Some(value) => specialized_impl(value),
        None => default_impl(value),
    }
}
```

Specialize a third-party library container with generic types:
```rust
use try_specialize::{Specialization, TypeFn};

fn func<K, V>(value: hashbrown::HashMap<K, V>) {
    struct MapIntoHashMap;
    impl<K, V> TypeFn<(K, V)> for MapIntoHashMap {
        type Output = hashbrown::HashMap<K, V>;
    }

    if let Some(spec) = Specialization::<(K, V), (u32, char)>::try_new() {
        let spec = spec.map::<MapIntoHashMap>();
        let value: hashbrown::HashMap<u32, char> = spec.specialize(value);
        specialized_impl(value);
    } else {
        default_impl(value);
    }
}
```

For a more comprehensive example, see the [`examples/encode.rs`], which
implements custom data encoders and decoders with per-type encoding and
decoding errors and optimized byte array encoding and decoding.
The part of this example related to the `Encode` implementation for a slice:
```rust
// ...

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

// ...
```

Find values by type in generic composite types:
```rust
use try_specialize::{LifetimeFree, TrySpecialize};

pub trait ConsListLookup {
    fn find<T>(&self) -> Option<&T>
    where
        T: ?Sized + LifetimeFree;
}

impl ConsListLookup for () {
    #[inline]
    fn find<T>(&self) -> Option<&T>
    where
        T: ?Sized + LifetimeFree,
    {
        None
    }
}

impl<T1, T2> ConsListLookup for (T1, T2)
where
    T2: ConsListLookup,
{
    #[inline]
    fn find<T>(&self) -> Option<&T>
    where
        T: ?Sized + LifetimeFree,
    {
        self.0.try_specialize_ref().or_else(|| self.1.find::<T>())
    }
}

#[derive(Eq, PartialEq, Debug)]
struct StaticStr(&'static str);
// SAFETY: It is safe to implement `LifetimeFree` for structs with no
// parameters.
unsafe impl LifetimeFree for StaticStr {}

let input = (
    123_i32,
    (
        [1_u32, 2, 3, 4],
        (1_i32, (StaticStr("foo"), (('a', false), ()))),
    ),
);

assert_eq!(input.find::<u32>(), None);
assert_eq!(input.find::<i32>(), Some(&123_i32));
assert_eq!(input.find::<[u32; 4]>(), Some(&[1, 2, 3, 4]));
assert_eq!(input.find::<[u32]>(), None);
assert_eq!(input.find::<StaticStr>(), Some(&StaticStr("foo")));
assert_eq!(input.find::<char>(), None);
assert_eq!(input.find::<(char, bool)>(), Some(&('a', false)));
```

## Documentation

[API Documentation]

## Feature flags

- `alloc` (implied by `std`, enabled by default): enables [`LifetimeFree`]
  implementations for `alloc` types, like `Box`, `Arc`, `String`, `Vec`,
  `BTreeMap` etc.
- `std` (enabled by default): enables `alloc` feature and [`LifetimeFree`]
  implementations for `std` types, like `OsStr`, `Path`, `PathBuf`,
  `Instant`, `HashMap` etc.
- `unreliable`: enables functions, methods and macros that rely on Rust
  standard library undocumented behavior. Refer to the [`unreliable`] module
  documentation for details.

## How it works

- Type comparison between `'static` types compares their [`TypeId::of`]s.
- Type comparison between unconstrained and [`LifetimeFree`] type treats
  them as `'static` and compares their [`TypeId::of`]s.
- Specialization relies on type comparison and [`transmute_copy`] when the
  equality of types is established.
- Unreliable trait implementation checks are performed using an expected,
  but undocumented behavior of the Rust stdlib [`PartialEq`] implementation
  for [`Arc<T>`]. [`Arc::eq`] uses fast path comparing references before
  comparing data if `T` implements [`Eq`].

## Alternative crates

- [`castaway`]: A similar crate with a much simpler macro-based API. The
  macro uses [Autoref-Based Specialization] and automatically determines the
  appropriate type of specialization, making it much easier to use. However,
  if no specialization is applicable because of the same [Autoref-Based
  Specialization], the compiler generates completely unclear errors, which
  makes it difficult to use it in complex cases. Internally uses `unsafe`
  code for type comparison and specialization.
- [`coe-rs`]: Smaller and simpler, but supports only static types and don't
  safely combine type equality check and specialization. Internally uses
  `unsafe` code for type specialization.
- [`downcast-rs`]: Specialized on trait objects (`dyn`) downcasting. Can't
  be used to specialize unconstrained types.
- [`syllogism`] and [`syllogism_macro`]: Requires to provide all possible
  types to macro that generate a lot of boilerplate code and can't be used
  to specialize stdlib types because of orphan rules.
- [`specialize`](https://crates.io/crates/specialize): Requires nightly.
  Adds a simple macro to inline nightly [`min_specialization`] usage into
  simple `if let` expressions.
- [`specialized-dispatch`]: Requires nightly. Adds a macro to inline nightly
  [`min_specialization`] usage into a `match`-like macro.
- [`spez`]: Specializes expression types, using [Autoref-Based
  Specialization]. It won't works in generic context but can be used in the
  code generated by macros.
- [`impls`]: Determine if a type implements a trait. Can't detect erased
  type bounds, so not applicable in generic context, but can be used in the
  code generated by macros.

### Comparison of libraries supporting specialization in generic context:

|  | crate <br /> `try-specialize` | crate <br /> [`castaway`] | crate <br /> [`coe-rs`] | crate <br /> [`downcast-rs`] | crate <br /> [`syllogism`] | [`min_spec...`] <br /> nightly feature | crate <br /> [`specialize`](https://crates.io/crates/specialize) | crate <br /> [`spec...ch`]
| --: | :--: | :--: | :--: | :--: | :--: | :--: | :--: | :--: |
| Rust toolchain | **Stable** | **Stable** | **Stable** | **Stable** | **Stable** | Nightly | Nightly | Nightly  |
| API complexity | Complex | **Simple** | **Simple** | Moderate | **Simple** | **Simple** | **Simple** | **Simple** |
| API difficulty | Difficult | **Easy** | **Easy** | Moderate | Moderate | **Easy** | **Easy** | Moderate |
| Zero-cost (compile-time optimized) | **YES** | **YES** | **YES** | no | **YES** | **YES** | **YES** | **YES** |
| Safely combines type eq check and specialization | **YES** | **YES** | no | **YES** | **YES** | **YES** |**YES** | **YES** |
| Specialize value references | **YES** | **YES** | **YES** | N/A | **YES** | **YES** | **YES** | no |
| Specialize values | **YES** | **YES** | no | N/A | **YES** | **YES** | **YES** | **YES** |
| Specialize values without consume on failure | **YES** | **YES** | no | N/A | **YES** | **YES** | no | **YES** |
| Limited non-static value specialization | **YES** | **YES** | no | N/A | **YES** | **YES** | **YES** | **YES** |
| Full non-static value specialization | no | no | no | N/A | **YES** | no | no | no |
| Specialize trait objects (`dyn`) | N/A | N/A | N/A | **YES** | N/A | N/A | N/A | N/A |
| Compare types without instantiation | **YES** | no | **YES** | no | **YES** | **YES** | **YES** | no |
| Support std types | **YES** | **YES** | **YES** | **YES** | no | **YES** | **YES** | **YES** |
| Specialize from unconstrained type | **YES** | **YES** | no | no | no | **YES** | **YES** | **YES** |
| Specialize to unconstrained type | **YES** | no | no | no | no | **YES** | **YES** | **YES** |
| Check generic implements "erased" trait | **YES**, but [`unreliable`] | no | no | no | no | **YES** | **YES** | **YES** |
| Specialize to generic with added bounds | no | no | no | no | no | **YES** | **YES** | **YES** |
| API based on | Traits | Macros | Traits | Macros + Traits | Traits | Language | Macros | Macros |
| Type comparison implementation based on | [`TypeId`] <br /> + [`transmute`] | [`TypeId`] <br /> + [`transmute`] |[`TypeId`] | N/A | Traits | Language | Nightly <br /> feature | Nightly <br /> feature |
| Type casting implementation based on | [`transmute_copy`] | [`ptr::read`] | [`transmute`] | [`std::any::Any`] | Traits | Language | Nightly <br /> feature | Nightly <br /> feature |
| Implementation free of `unsafe` | no | no | no | **YES** | **YES** | **YES** | **YES** | **YES** |

### Primitive example of the value specialization using different libraries

<table><tbody><tr><td style="vertical-align: top">

crate `try_specialize`:

```rust
use try_specialize::TrySpecialize;

fn spec<T>(value: T) -> Result<u32, T> {
    value.try_specialize()
}

assert_eq!(spec(42_u32), Ok(42));
assert_eq!(spec(42_i32), Err(42));
assert_eq!(spec("abc"), Err("abc"));
```

</td><td style="vertical-align: top">

crate [`castaway`]:

```rust
use castaway::cast;

fn spec<T>(value: T) -> Result<u32, T> {
    cast!(value, _)
}

assert_eq!(spec(42_u32), Ok(42));
assert_eq!(spec(42_i32), Err(42));
assert_eq!(spec("abc"), Err("abc"));
```

</td></tr><tr><td style="vertical-align: top">

crate [`coe-rs`]:

```rust
use coe::{is_same, Coerce};

// Library don't support non-reference.
// specialization. Using reference.
fn spec<T>(value: &T) -> Option<&u32>
where
    // Library don't support specialization of
    // unconstrained non-static types.
    T: 'static,
{
    is_same::<u32, T>().then(|| value.coerce())
}

fn main() {
    assert_eq!(spec(&42_u32), Some(&42));
    assert_eq!(spec(&42_i32), None);
    assert_eq!(spec(&"abc"), None);
}
```

</td><td style="vertical-align: top">

crates [`downcast-rs`]:

```rust
use downcast_rs::{impl_downcast, DowncastSync};

trait Base: DowncastSync {}
impl_downcast!(sync Base);

// Library requires all specializable
// types to be defined in advance.
impl Base for u32 {}
impl Base for i32 {}
impl Base for &'static str {}

// Library support only trait objects (`dyn`).
fn spec(value: &dyn Base) -> Option<&u32> {
    value.downcast_ref::<u32>()
}

fn main() {
    assert_eq!(spec(&42_u32), Some(&42));
    assert_eq!(spec(&42_i32), None);
    assert_eq!(spec(&"abc"), None);
}
```

</td></tr><tr><td style="vertical-align: top">

crate [`specialize`](https://crates.io/crates/specialize):

```rust
// Requires nightly.
#![feature(min_specialization)]

use specialize::constrain;

// Library don't support non-consuming
// value specialization. Using reference.
fn spec<T: ?Sized>(value: &T) -> Option<&u32> {
    constrain!(ref value as u32)
}

assert_eq!(spec(&42_u32), Some(&42));
assert_eq!(spec(&42_i32), None);
assert_eq!(spec("abc"), None);
```

</td><td style="vertical-align: top">

crate [`specialized-dispatch`]:
```rust
// Requires nightly.
#![feature(min_specialization)]

use specialized_dispatch::specialized_dispatch;

// The library don't support using generics.
// from outer item. Using `Option`.
fn spec<T>(value: T) -> Option<u32> {
    specialized_dispatch! {
        T -> Option<u32>,
        fn (value: u32) => Some(value),
        default fn <T>(_: T) => None,
        value,
    }
}

assert_eq!(spec(42_u32), Some(42));
assert_eq!(spec(42_i32), None);
assert_eq!(spec("abc"), None);
```

</td></tr><tr><td style="vertical-align: top">

crates [`syllogism`] and [`syllogism_macro`]:

```rust
use syllogism::{Distinction, Specialize};
use syllogism_macro::impl_specialization;

// Library specialization can not be
// implemented for std types because of
// orphan rules. Using custom local types.
#[derive(Eq, PartialEq, Debug)]
struct U32(u32);
#[derive(Eq, PartialEq, Debug)]
struct I32(i32);
#[derive(Eq, PartialEq, Debug)]
struct Str<'a>(&'a str);

// Library requires all specializable
// types to be defined in one place.
impl_specialization!(
    type U32;
    type I32;
    type Str<'a>;
);

fn spec<T>(value: T) -> Result<U32, T>
where
    T: Specialize<U32>,
{
    match value.specialize() {
        Distinction::Special(value) => Ok(value),
        Distinction::Generic(value) => Err(value),
    }
}

assert_eq!(spec(U32(42)), Ok(U32(42)));
assert_eq!(spec(I32(42_i32)), Err(I32(42)));
assert_eq!(spec(Str("abc")), Err(Str("abc")));
```

</td><td style="vertical-align: top">

[`min_specialization`] nightly feature:

```rust
// Requires nightly.
#![feature(min_specialization)]

// The artificial example looks a bit long.
// More real-world use cases are usually
// on the contrary more clear and understandable.
pub trait Spec: Sized {
    fn spec(self) -> Result<u32, Self>;
}

impl<T> Spec for T {
    default fn spec(self) -> Result<u32, Self> {
        Err(self)
    }
}

impl Spec for u32 {
    fn spec(self) -> Result<u32, Self> {
        Ok(self)
    }
}

assert_eq!(Spec::spec(42_u32), Ok(42));
assert_eq!(Spec::spec(42_i32), Err(42));
assert_eq!(Spec::spec("abc"), Err("abc"));
```

</td></tr></tbody></table>

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or <https://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <https://opensource.org/licenses/MIT>)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any
additional terms or conditions.

[API Documentation]: https://docs.rs/try-specialize
[subtyping]: https://doc.rust-lang.org/nomicon/subtyping.html
[coercion]: https://doc.rust-lang.org/nomicon/coercions.html
[release]: https://doc.rust-lang.org/cargo/reference/profiles.html#release
[`min_specialization`]: https://github.com/rust-lang/rust/pull/68970
[`min_spec...`]: https://github.com/rust-lang/rust/pull/68970 "min_specialization"

[`examples/encode.rs`]: https://github.com/zheland/try-specialize/blob/v0.1.0/examples/encode.rs

[`std::any::TypeId`]: https://doc.rust-lang.org/std/any/struct.TypeId.html
[`TypeId`]: https://doc.rust-lang.org/std/any/struct.TypeId.html "std::any::TypeId"
[`std::any::Any`]: https://doc.rust-lang.org/std/any/trait.Any.html
[`TypeId::of`]: https://doc.rust-lang.org/std/any/struct.TypeId.html#method.of "std::any::TypeId::of"
[`transmute`]: https://doc.rust-lang.org/std/mem/fn.transmute.html "std::mem::transmute"
[`transmute_copy`]: https://doc.rust-lang.org/std/mem/fn.transmute_copy.html "std::mem::transmute_copy"
[`ptr::read`]: https://doc.rust-lang.org/std/ptr/fn.read.html "std::ptr::read"
[`PartialEq`]: https://doc.rust-lang.org/std/cmp/trait.PartialEq.html "std::cmp::PartialEq"
[`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html "std::cmp::Eq"
[`Arc::eq`]: https://doc.rust-lang.org/std/sync/struct.Arc.html#method.eq "<std::sync::Arc as PartialEq>::eq"
[`Arc<T>`]: https://doc.rust-lang.org/std/sync/struct.Arc.html "std::sync::Arc"

[`unreliable`]: https://docs.rs/try-specialize/latest/try_specialize/unreliable/index.html
[`LifetimeFree`]: https://docs.rs/try-specialize/latest/try_specialize/trait.LifetimeFree.html

[`Specialization`]: https://docs.rs/try-specialize/latest/try_specialize/struct.Specialization.html
[`try_new`]: https://docs.rs/try-specialize/latest/try_specialize/struct.Specialization.html#method.try_new "Specialization::try_new"
[`try_new_static`]: https://docs.rs/try-specialize/latest/try_specialize/struct.Specialization.html#method.try_new_static "Specialization::try_new_static"
[`try_new_ignore_lifetimes`]: https://docs.rs/try-specialize/latest/try_specialize/struct.Specialization.html#method.try_new_ignore_lifetimes "Specialization::try_new_ignore_lifetimes"
[`rev`]: https://docs.rs/try-specialize/latest/try_specialize/struct.Specialization.html#method.rev "Specialization::rev"
[`map`]: https://docs.rs/try-specialize/latest/try_specialize/struct.Specialization.html#method.map "Specialization::map"
[`specialize`]: https://docs.rs/try-specialize/latest/try_specialize/struct.Specialization.html#method.specialize "Specialization::specialize"
[`specialize_ref`]: https://docs.rs/try-specialize/latest/try_specialize/struct.Specialization.html#method.specialize_ref "Specialization::specialize_ref"
[`specialize_mut`]: https://docs.rs/try-specialize/latest/try_specialize/struct.Specialization.html#method.specialize_mut "Specialization::specialize_mut"

[`WeakSpecialization`]: https://docs.rs/try-specialize/latest/try_specialize/unreliable/trait.WeakSpecialization.html
[`try_new_if_lifetime_free_weak`]: https://docs.rs/try-specialize/latest/try_specialize/unreliable/trait.WeakSpecialization.html#method.try_new_if_lifetime_free_weak "unreliable::WeakSpecialization::try_new_if_lifetime_free_weak"

[`TrySpecialize`]: https://docs.rs/try-specialize/latest/try_specialize/trait.TrySpecialize.html
[`TrySpecialize::try_specialize`]: https://docs.rs/try-specialize/latest/try_specialize/trait.TrySpecialize.html#method.try_specialize
[`try_specialize`]: https://docs.rs/try-specialize/latest/try_specialize/trait.TrySpecialize.html#method.try_specialize "TrySpecialize::try_specialize"
[`TrySpecialize::try_specialize_ref`]: https://docs.rs/try-specialize/latest/try_specialize/trait.TrySpecialize.html#method.try_specialize_ref
[`try_specialize_ref`]: https://docs.rs/try-specialize/latest/try_specialize/trait.TrySpecialize.html#method.try_specialize_ref "TrySpecialize::try_specialize_ref"
[`try_specialize_from`]: https://docs.rs/try-specialize/latest/try_specialize/trait.TrySpecialize.html#method.try_specialize_from "TrySpecialize::try_specialize_from"
[`try_specialize_from_ref`]: https://docs.rs/try-specialize/latest/try_specialize/trait.TrySpecialize.html#method.try_specialize_from_ref "TrySpecialize::try_specialize_from_ref"
[`TrySpecialize::try_specialize_static`]: https://docs.rs/try-specialize/latest/try_specialize/trait.TrySpecialize.html#method.try_specialize_static
[`try_specialize_static`]: https://docs.rs/try-specialize/latest/try_specialize/trait.TrySpecialize.html#method.try_specialize_static "TrySpecialize::try_specialize_static"
[`try_specialize_ref_static`]: https://docs.rs/try-specialize/latest/try_specialize/trait.TrySpecialize.html#method.try_specialize_ref_static "TrySpecialize::try_specialize_ref_static"
[`..._ignore_lifetimes`]: https://docs.rs/try-specialize/latest/try_specialize/trait.TrySpecialize.html#method.try_specialize_ignore_lifetimes "TrySpecialize::try_specialize_ignore_lifetimes"
[`..._ref_ignore_lifetimes`]: https://docs.rs/try-specialize/latest/try_specialize/trait.TrySpecialize.html#method.try_specialize_ref_ignore_lifetimes "TrySpecialize::try_specialize_ref_ignore_lifetimes"
[`..._mut_ignore_lifetimes`]: https://docs.rs/try-specialize/latest/try_specialize/trait.TrySpecialize.html#method.try_specialize_mut_ignore_lifetimes "TrySpecialize::try_specialize_mut_ignore_lifetimes"

[`TrySpecializeWeak`]: https://docs.rs/try-specialize/latest/try_specialize/unreliable/trait.TrySpecializeWeak.html
[`..._if_lifetime_free_weak`]: https://docs.rs/try-specialize/latest/try_specialize/unreliable/trait.TrySpecializeWeak.html#method.try_specialize_if_lifetime_free_weak "unreliable::TrySpecializeWeak::try_specialize_if_lifetime_free_weak"
[`..._ref_if_lifetime_free_weak`]: https://docs.rs/try-specialize/latest/try_specialize/unreliable/trait.TrySpecializeWeak.html#method.try_specialize_ref_if_lifetime_free_weak "unreliable::TrySpecializeWeak::try_specialize_ref_if_lifetime_free_weak"
[`..._mut_if_lifetime_free_weak`]: https://docs.rs/try-specialize/latest/try_specialize/unreliable/trait.TrySpecializeWeak.html#method.try_specialize_mut_if_lifetime_free_weak "unreliable::TrySpecializeWeak::try_specialize_mut_if_lifetime_free_weak"

[`castaway`]: https://crates.io/crates/castaway
[`syllogism`]: https://crates.io/crates/syllogism
[`syllogism_macro`]: https://crates.io/crates/syllogism_macro
[`specialized-dispatch`]: https://crates.io/crates/specialized-dispatch
[`spec...ch`]: https://crates.io/crates/specialized-dispatch "specialized-dispatch"
[`spez`]: https://crates.io/crates/spez
[`coe-rs`]: https://crates.io/crates/coe-rs
[`downcast-rs`]: https://crates.io/crates/downcast-rs
[`impls`]: https://crates.io/crates/impls

[Autoref-Based Specialization]: https://lukaskalbertodt.github.io/2019/12/05/generalized-autoref-based-specialization.html
