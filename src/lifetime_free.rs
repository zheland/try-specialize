#![expect(
    clippy::undocumented_unsafe_blocks,
    reason = "safety comment for all unsafe implementation specified for the `LifetimeFree` trait"
)]

/// A marker trait for types that do not contain any lifetime parameters.
///
/// Such types are safe to specialize from non-static type parameters if their
/// types are equal. This trait is used to determine safe specialization methods
/// in [`TrySpecialize`] trait and safe constructor for [`Specialization`]. The
/// `LifetimeFree` bound is stricter than `'static` bound. All `LifetimeFree`
/// types are also `'static`, but the reverse is not true.
///
/// This trait is **not** automatically generated for all lifetime free types.
/// Use [`Specialization::rev`] to specialize from a `LifetimeFree`
/// type to an unconstrained type.
///
/// # Safety
///
/// When implementing this trait for a `struct`, `enum`, or `union` type, you
/// must ensure that the type does **not** contain any lifetime parameters.
/// When implementing this trait for a type alias, you must ensure that the
/// underlying `struct`, `enum`, or `union` type does **not** contain any
/// lifetime parameters.
///
/// Note, however, that the use of `'static` values in type fields is allowed.
/// So:
/// - `struct First<'a, T>( /* ... */ )` is not a lifetime free type.
/// - `type Second<T> = First<'static, T>` is not a lifetime free type.
/// - `type Third = Second<u32>` is not a lifetime free type, because the
///   underlying type is still `First<'static, T>`.
///
/// Whereas for `T: LifetimeFree` the
/// `struct Fourth<T>(&'static str, Cow<'static, T>)` and its aliases can be
/// considered as lifetime free types, since the underlying struct has no
/// lifetime parameters. It only has fields with lifetimes, which is allowed.
/// Therefore, it is safe to
/// `impl LifetimeFree<T> for Fourth<T> where T: LifetimeFree {}`.
///
/// Implementing this trait for types which uses lifetimes may result in
/// *[undefined behavior]*.
///
/// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
///
/// # Examples
///
/// ```rust
/// use try_specialize::LifetimeFree;
///
/// struct MarkerType;
/// struct U32Pair(u32, u32);
/// struct CustomVec<T> {
///     ptr: *mut T,
///     cap: usize,
///     len: usize,
/// }
/// struct Data {
///     // ...
/// }
/// enum Either<T1, T2> {
///     Left(T1),
///     Right(T2),
/// }
///
/// unsafe impl LifetimeFree for MarkerType {}
/// unsafe impl LifetimeFree for U32Pair {}
/// unsafe impl<T: LifetimeFree> LifetimeFree for CustomVec<T> {}
/// unsafe impl LifetimeFree for Data {}
/// unsafe impl<T1, T2> LifetimeFree for Either<T1, T2>
/// where
///     T1: LifetimeFree,
///     T2: LifetimeFree,
/// {
/// }
/// ```
///
/// Safe examples with `'static` used in fields:
/// ```rust
/// use std::borrow::Cow;
///
/// use try_specialize::LifetimeFree;
///
/// // Original type must not implement `LifetimeFree` because it has lifetime parameters.
/// // However its wrapper without lifetime parameters can implement `LifetimeFree`.
/// struct WithLifetimes<'a, 'b, T, U>(&'a str, &'b [u8], T, U);
///
/// struct StaticStrWrapper(pub &'static str);
/// struct StaticRefWrapper<T: LifetimeFree>(pub &'static T);
/// struct StaticCowWrapper<T: LifetimeFree + ToOwned>(pub Cow<'static, T>);
/// struct WithLifetimesWrapper<T, U>(pub WithLifetimes<'static, 'static, T, U>);
///
/// unsafe impl LifetimeFree for StaticStrWrapper {}
/// unsafe impl<T: LifetimeFree> LifetimeFree for StaticRefWrapper<T> {}
/// unsafe impl<T: LifetimeFree + ToOwned> LifetimeFree for StaticCowWrapper<T> {}
/// unsafe impl<T: LifetimeFree, U: LifetimeFree> LifetimeFree for WithLifetimesWrapper<T, U> {}
/// ```
///
/// Invalid usage examples with explicit or implicit `'static` parameters:
/// ```rust,compile_fail
/// # macro_rules UB! { ( $( $tt:tt )* ) => { $( $tt )* } };
/// #
/// use std::borrow::Cow;
///
/// use try_specialize::LifetimeFree;
///
/// struct WithLifetimes<'a, 'b, T, U>(&'a str, &'b [u8], T, U);
///
/// type StaticStrAlias = &'static str;
/// type StaticRefAlias<T> = &'static T;
/// type StaticCowAlias<T> = Cow<'static, T>;
/// type WithLifetimesAlias<T, U> = WithLifetimes<'static, 'static, T, U>;
///
/// // Do not implement use it!
/// // Any implementation below may result to undefined behavior!
/// UB!{ unsafe impl LifetimeFree for StaticStrAlias {} }
/// UB!{ unsafe impl<T: LifetimeFree> LifetimeFree for StaticRefAlias<T> {} }
/// UB!{ unsafe impl<T: LifetimeFree> LifetimeFree for StaticCowAlias<T> {} }
/// UB!{
///     unsafe impl<T: LifetimeFree, U: LifetimeFree> LifetimeFree
///         for WithLifetimes<'static, 'static, T, U> {}
/// }
/// UB!{
///     unsafe impl<T: LifetimeFree, U: LifetimeFree> LifetimeFree
///         for WithLifetimesAlias<T, U> {}
/// }
/// ```
///
/// [`TrySpecialize`]: crate::TrySpecialize
/// [`Specialization`]: crate::Specialization
/// [`Specialization::rev`]: crate::Specialization::rev
/// [`Specialization::map`]: crate::Specialization::map
pub unsafe trait LifetimeFree: 'static {}

unsafe impl LifetimeFree for bool {}
unsafe impl LifetimeFree for char {}
unsafe impl LifetimeFree for u8 {}
unsafe impl LifetimeFree for u16 {}
unsafe impl LifetimeFree for u32 {}
unsafe impl LifetimeFree for u64 {}
unsafe impl LifetimeFree for u128 {}
unsafe impl LifetimeFree for usize {}
unsafe impl LifetimeFree for i8 {}
unsafe impl LifetimeFree for i16 {}
unsafe impl LifetimeFree for i32 {}
unsafe impl LifetimeFree for i64 {}
unsafe impl LifetimeFree for i128 {}
unsafe impl LifetimeFree for isize {}
unsafe impl LifetimeFree for f32 {}
unsafe impl LifetimeFree for f64 {}

unsafe impl LifetimeFree for ::core::num::NonZeroU8 {}
unsafe impl LifetimeFree for ::core::num::NonZeroU16 {}
unsafe impl LifetimeFree for ::core::num::NonZeroU32 {}
unsafe impl LifetimeFree for ::core::num::NonZeroU64 {}
unsafe impl LifetimeFree for ::core::num::NonZeroU128 {}
unsafe impl LifetimeFree for ::core::num::NonZeroUsize {}
unsafe impl LifetimeFree for ::core::num::NonZeroI8 {}
unsafe impl LifetimeFree for ::core::num::NonZeroI16 {}
unsafe impl LifetimeFree for ::core::num::NonZeroI32 {}
unsafe impl LifetimeFree for ::core::num::NonZeroI64 {}
unsafe impl LifetimeFree for ::core::num::NonZeroI128 {}
unsafe impl LifetimeFree for ::core::num::NonZeroIsize {}

#[cfg(target_has_atomic = "8")]
unsafe impl LifetimeFree for core::sync::atomic::AtomicBool {}
#[cfg(target_has_atomic = "8")]
unsafe impl LifetimeFree for core::sync::atomic::AtomicI8 {}
#[cfg(target_has_atomic = "16")]
unsafe impl LifetimeFree for core::sync::atomic::AtomicI16 {}
#[cfg(target_has_atomic = "32")]
unsafe impl LifetimeFree for core::sync::atomic::AtomicI32 {}
#[cfg(target_has_atomic = "64")]
unsafe impl LifetimeFree for core::sync::atomic::AtomicI64 {}
#[cfg(target_has_atomic = "ptr")]
unsafe impl LifetimeFree for core::sync::atomic::AtomicIsize {}
#[cfg(target_has_atomic = "8")]
unsafe impl LifetimeFree for core::sync::atomic::AtomicU8 {}
#[cfg(target_has_atomic = "16")]
unsafe impl LifetimeFree for core::sync::atomic::AtomicU16 {}
#[cfg(target_has_atomic = "32")]
unsafe impl LifetimeFree for core::sync::atomic::AtomicU32 {}
#[cfg(target_has_atomic = "64")]
unsafe impl LifetimeFree for core::sync::atomic::AtomicU64 {}
#[cfg(target_has_atomic = "ptr")]
unsafe impl LifetimeFree for core::sync::atomic::AtomicUsize {}
unsafe impl LifetimeFree for core::sync::atomic::Ordering {}

unsafe impl<T> LifetimeFree for core::num::Saturating<T> where T: LifetimeFree {}
unsafe impl<T> LifetimeFree for core::num::Wrapping<T> where T: LifetimeFree {}

unsafe impl<T> LifetimeFree for Option<T> where T: LifetimeFree {}
unsafe impl<T, E> LifetimeFree for Result<T, E>
where
    T: LifetimeFree,
    E: LifetimeFree,
{
}

unsafe impl LifetimeFree for str {}
unsafe impl LifetimeFree for core::ffi::CStr {}
unsafe impl<T> LifetimeFree for [T] where T: LifetimeFree {}

unsafe impl<T, const N: usize> LifetimeFree for [T; N] where T: LifetimeFree {}

unsafe impl<T> LifetimeFree for *const T where T: ?Sized + LifetimeFree {}
unsafe impl<T> LifetimeFree for *mut T where T: ?Sized + LifetimeFree {}
unsafe impl<T> LifetimeFree for core::ptr::NonNull<T> where T: ?Sized + LifetimeFree {}

unsafe impl LifetimeFree for core::convert::Infallible {}
unsafe impl LifetimeFree for core::marker::PhantomPinned {}
unsafe impl<T> LifetimeFree for core::marker::PhantomData<T> where T: ?Sized + LifetimeFree {}
unsafe impl<T> LifetimeFree for core::cell::Cell<T> where T: ?Sized + LifetimeFree {}
unsafe impl<T> LifetimeFree for core::cell::RefCell<T> where T: ?Sized + LifetimeFree {}
unsafe impl<T> LifetimeFree for core::cell::OnceCell<T> where T: LifetimeFree {}
unsafe impl<T> LifetimeFree for core::cell::UnsafeCell<T> where T: LifetimeFree {}
unsafe impl<T, F> LifetimeFree for core::cell::LazyCell<T, F>
where
    T: LifetimeFree,
    F: LifetimeFree,
{
}

unsafe impl LifetimeFree for core::time::Duration {}
unsafe impl LifetimeFree for core::net::IpAddr {}
unsafe impl LifetimeFree for core::net::Ipv4Addr {}
unsafe impl LifetimeFree for core::net::Ipv6Addr {}
unsafe impl LifetimeFree for core::net::SocketAddr {}
unsafe impl LifetimeFree for core::net::SocketAddrV4 {}
unsafe impl LifetimeFree for core::net::SocketAddrV6 {}
unsafe impl LifetimeFree for core::cmp::Ordering {}
unsafe impl LifetimeFree for core::ops::RangeFull {}

unsafe impl<T> LifetimeFree for core::pin::Pin<T> where T: LifetimeFree {}
unsafe impl<T> LifetimeFree for core::task::Poll<T> where T: LifetimeFree {}
unsafe impl<T> LifetimeFree for core::ops::Bound<T> where T: LifetimeFree {}
unsafe impl<T> LifetimeFree for core::ops::Range<T> where T: LifetimeFree {}
unsafe impl<T> LifetimeFree for core::ops::RangeFrom<T> where T: LifetimeFree {}
unsafe impl<T> LifetimeFree for core::ops::RangeInclusive<T> where T: LifetimeFree {}
unsafe impl<T> LifetimeFree for core::ops::RangeTo<T> where T: LifetimeFree {}
unsafe impl<T> LifetimeFree for core::ops::RangeToInclusive<T> where T: LifetimeFree {}
unsafe impl<B, C> LifetimeFree for core::ops::ControlFlow<B, C>
where
    B: LifetimeFree,
    C: LifetimeFree,
{
}

unsafe impl LifetimeFree for core::alloc::Layout {}
unsafe impl LifetimeFree for core::alloc::LayoutError {}
unsafe impl LifetimeFree for core::any::TypeId {}
unsafe impl<T, const N: usize> LifetimeFree for core::array::IntoIter<T, N> where T: LifetimeFree {}
unsafe impl LifetimeFree for core::array::TryFromSliceError {}
unsafe impl LifetimeFree for core::ascii::EscapeDefault {}
unsafe impl LifetimeFree for core::cell::BorrowError {}
unsafe impl LifetimeFree for core::cell::BorrowMutError {}
unsafe impl LifetimeFree for core::char::CharTryFromError {}
unsafe impl<I> LifetimeFree for core::char::DecodeUtf16<I> where
    I: LifetimeFree + Iterator<Item = u16>
{
}
unsafe impl LifetimeFree for core::char::DecodeUtf16Error {}
unsafe impl LifetimeFree for core::char::EscapeDebug {}
unsafe impl LifetimeFree for core::char::EscapeDefault {}
unsafe impl LifetimeFree for core::char::EscapeUnicode {}
unsafe impl LifetimeFree for core::char::ParseCharError {}
unsafe impl LifetimeFree for core::char::ToLowercase {}
unsafe impl LifetimeFree for core::char::ToUppercase {}
unsafe impl LifetimeFree for core::char::TryFromCharError {}
unsafe impl<T> LifetimeFree for core::cmp::Reverse<T> where T: LifetimeFree {}

unsafe impl LifetimeFree for core::ffi::c_void {}
unsafe impl LifetimeFree for core::fmt::Error {}
unsafe impl LifetimeFree for core::fmt::Alignment {}

unsafe impl<T> LifetimeFree for core::future::Pending<T> where T: LifetimeFree {}
unsafe impl<F> LifetimeFree for core::future::PollFn<F> where F: LifetimeFree {}
unsafe impl<T> LifetimeFree for core::future::Ready<T> where T: LifetimeFree {}

unsafe impl<H> LifetimeFree for core::hash::BuildHasherDefault<H> where H: LifetimeFree {}

unsafe impl<A, B> LifetimeFree for core::iter::Chain<A, B>
where
    A: LifetimeFree,
    B: LifetimeFree,
{
}
unsafe impl<I> LifetimeFree for core::iter::Cloned<I> where I: LifetimeFree {}
unsafe impl<I> LifetimeFree for core::iter::Copied<I> where I: LifetimeFree {}
unsafe impl<I> LifetimeFree for core::iter::Cycle<I> where I: LifetimeFree {}
unsafe impl<T> LifetimeFree for core::iter::Empty<T> where T: LifetimeFree {}
unsafe impl<I> LifetimeFree for core::iter::Enumerate<I> where I: LifetimeFree {}
unsafe impl<I, P> LifetimeFree for core::iter::Filter<I, P>
where
    I: LifetimeFree,
    P: LifetimeFree,
{
}
unsafe impl<I, F> LifetimeFree for core::iter::FilterMap<I, F>
where
    I: LifetimeFree,
    F: LifetimeFree,
{
}
unsafe impl<I, U, F> LifetimeFree for core::iter::FlatMap<I, U, F>
where
    I: LifetimeFree,
    U: LifetimeFree + IntoIterator,
    F: LifetimeFree,
{
}
unsafe impl<I> LifetimeFree for core::iter::Flatten<I>
where
    I: LifetimeFree + Iterator,
    <I as Iterator>::Item: IntoIterator,
{
}
unsafe impl<F> LifetimeFree for core::iter::FromFn<F> where F: LifetimeFree {}
unsafe impl<I> LifetimeFree for core::iter::Fuse<I> where I: LifetimeFree {}
unsafe impl<I, F> LifetimeFree for core::iter::Inspect<I, F>
where
    I: LifetimeFree,
    F: LifetimeFree,
{
}
unsafe impl<I, F> LifetimeFree for core::iter::Map<I, F>
where
    I: LifetimeFree,
    F: LifetimeFree,
{
}
unsafe impl<I, F> LifetimeFree for core::iter::MapWhile<I, F>
where
    I: LifetimeFree,
    F: LifetimeFree,
{
}
unsafe impl<F> LifetimeFree for core::iter::OnceWith<F> where F: LifetimeFree {}
unsafe impl<I> LifetimeFree for core::iter::Peekable<I> where I: LifetimeFree + Iterator {}
unsafe impl<A> LifetimeFree for core::iter::Repeat<A> where A: LifetimeFree {}
unsafe impl<F> LifetimeFree for core::iter::RepeatWith<F> where F: LifetimeFree {}
unsafe impl<T> LifetimeFree for core::iter::Rev<T> where T: LifetimeFree {}
unsafe impl<I, St, F> LifetimeFree for core::iter::Scan<I, St, F>
where
    I: LifetimeFree,
    St: LifetimeFree,
    F: LifetimeFree,
{
}
unsafe impl<I> LifetimeFree for core::iter::Skip<I> where I: LifetimeFree {}
unsafe impl<I, P> LifetimeFree for core::iter::SkipWhile<I, P>
where
    I: LifetimeFree,
    P: LifetimeFree,
{
}
unsafe impl<I> LifetimeFree for core::iter::StepBy<I> where I: LifetimeFree {}
unsafe impl<T, F> LifetimeFree for core::iter::Successors<T, F>
where
    T: LifetimeFree,
    F: LifetimeFree,
{
}
unsafe impl<I> LifetimeFree for core::iter::Take<I> where I: LifetimeFree {}
unsafe impl<I, P> LifetimeFree for core::iter::TakeWhile<I, P>
where
    I: LifetimeFree,
    P: LifetimeFree,
{
}
unsafe impl<A, B> LifetimeFree for core::iter::Zip<A, B>
where
    A: LifetimeFree,
    B: LifetimeFree,
{
}

unsafe impl<T> LifetimeFree for core::mem::Discriminant<T> where T: LifetimeFree {}
unsafe impl<T> LifetimeFree for core::mem::ManuallyDrop<T> where T: LifetimeFree {}

unsafe impl LifetimeFree for core::net::AddrParseError {}

unsafe impl LifetimeFree for core::num::ParseFloatError {}
unsafe impl LifetimeFree for core::num::ParseIntError {}
unsafe impl LifetimeFree for core::num::TryFromIntError {}
unsafe impl LifetimeFree for core::num::FpCategory {}
unsafe impl LifetimeFree for core::num::IntErrorKind {}

unsafe impl<A> LifetimeFree for core::option::IntoIter<A> where A: LifetimeFree {}
unsafe impl<T> LifetimeFree for core::result::IntoIter<T> where T: LifetimeFree {}
unsafe impl<T> LifetimeFree for core::panic::AssertUnwindSafe<T> where T: LifetimeFree {}

unsafe impl LifetimeFree for core::str::ParseBoolError {}
unsafe impl LifetimeFree for core::str::Utf8Error {}

unsafe impl LifetimeFree for core::task::RawWaker {}
unsafe impl LifetimeFree for core::task::RawWakerVTable {}
unsafe impl LifetimeFree for core::task::Waker {}

unsafe impl LifetimeFree for core::time::TryFromFloatSecsError {}

macro_rules! impl_for_tuples {
    ( $( $args:ident ),* $(,)? ) => {
        impl_for_tuples!( @impl [] [ $( $args ),* ] );
    };
    ( @impl [ $( $args:ident ),* ] [ $next:ident $(, $rest:ident )* ] ) => {
        impl_for_tuples!( @impl [ $( $args ),* ] [] );
        impl_for_tuples!( @impl [ $( $args, )* $next ] [ $( $rest ),* ] );
    };
    ( @impl [ $( $args:ident ),* ] [] ) => {
        unsafe impl<$( $args ),*> LifetimeFree for ( $( $args, )* )
        where
            $( $args: LifetimeFree, )*
        {
        }
    };
}

impl_for_tuples! { T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12 }

macro_rules! impl_for_fn_ptrs {
    ( $abi:literal, $( $args:ident ),* $(,)? ) => {
        impl_for_fn_ptrs!( @impl $abi [] [ $( $args ),* ] );
    };
    ( @impl $abi:literal [ $( $args:ident ),* ] [ $next:ident $(, $rest:ident )* ] ) => {
        impl_for_fn_ptrs!( @impl $abi [ $( $args ),* ] [] );
        impl_for_fn_ptrs!( @impl $abi [ $( $args, )* $next ] [ $( $rest ),* ] );
    };
    ( @impl $abi:literal [ $( $args:ident ),* ] [] ) => {
        unsafe impl<$( $args, )* R> LifetimeFree for extern $abi fn( $( $args, )* ) -> R
        where
            $( $args: LifetimeFree, )*
            R: LifetimeFree,
        {
        }
    };
}

impl_for_fn_ptrs! { "Rust", T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12 }
impl_for_fn_ptrs! { "C", T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12 }
impl_for_fn_ptrs! { "system", T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12 }

#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
mod alloc_impls {
    use crate::LifetimeFree;

    unsafe impl<T> LifetimeFree for alloc::boxed::Box<T> where T: ?Sized + LifetimeFree {}
    unsafe impl<T> LifetimeFree for alloc::rc::Rc<T> where T: ?Sized + LifetimeFree {}
    unsafe impl<T> LifetimeFree for alloc::rc::Weak<T> where T: ?Sized + LifetimeFree {}
    #[cfg(target_has_atomic = "ptr")]
    unsafe impl<T> LifetimeFree for alloc::sync::Arc<T> where T: ?Sized + LifetimeFree {}
    #[cfg(target_has_atomic = "ptr")]
    unsafe impl<T> LifetimeFree for alloc::sync::Weak<T> where T: ?Sized + LifetimeFree {}

    unsafe impl LifetimeFree for alloc::string::String {}
    unsafe impl LifetimeFree for alloc::ffi::CString {}

    unsafe impl<T> LifetimeFree for alloc::vec::Vec<T> where T: LifetimeFree {}
    unsafe impl<T> LifetimeFree for alloc::collections::VecDeque<T> where T: LifetimeFree {}
    unsafe impl<T> LifetimeFree for alloc::collections::LinkedList<T> where T: LifetimeFree {}
    unsafe impl<T> LifetimeFree for alloc::collections::BinaryHeap<T> where T: LifetimeFree {}
    unsafe impl<T> LifetimeFree for alloc::collections::BTreeSet<T> where T: LifetimeFree {}

    unsafe impl<K, V> LifetimeFree for alloc::collections::BTreeMap<K, V>
    where
        K: LifetimeFree,
        V: LifetimeFree,
    {
    }

    unsafe impl LifetimeFree for alloc::string::FromUtf8Error {}
    unsafe impl LifetimeFree for alloc::string::FromUtf16Error {}

    unsafe impl LifetimeFree for alloc::collections::TryReserveError {}
    unsafe impl<T> LifetimeFree for alloc::collections::binary_heap::IntoIter<T> where T: LifetimeFree {}
    unsafe impl<K, V> LifetimeFree for alloc::collections::btree_map::IntoIter<K, V>
    where
        K: LifetimeFree,
        V: LifetimeFree,
    {
    }
    unsafe impl<K, V> LifetimeFree for alloc::collections::btree_map::IntoKeys<K, V>
    where
        K: LifetimeFree,
        V: LifetimeFree,
    {
    }
    unsafe impl<K, V> LifetimeFree for alloc::collections::btree_map::IntoValues<K, V>
    where
        K: LifetimeFree,
        V: LifetimeFree,
    {
    }
    unsafe impl<T> LifetimeFree for alloc::collections::btree_set::IntoIter<T> where T: LifetimeFree {}
    unsafe impl<T> LifetimeFree for alloc::vec::IntoIter<T> where T: LifetimeFree {}
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
mod std_impls {
    use crate::LifetimeFree;

    unsafe impl LifetimeFree for std::ffi::OsStr {}
    unsafe impl LifetimeFree for std::path::Path {}

    unsafe impl LifetimeFree for std::ffi::OsString {}
    unsafe impl LifetimeFree for std::path::PathBuf {}
    unsafe impl LifetimeFree for std::time::Instant {}
    unsafe impl LifetimeFree for std::time::SystemTime {}

    unsafe impl LifetimeFree for std::hash::DefaultHasher {}
    unsafe impl LifetimeFree for std::hash::RandomState {}

    unsafe impl<T, S> LifetimeFree for std::collections::HashSet<T, S>
    where
        T: LifetimeFree,
        S: LifetimeFree,
    {
    }

    unsafe impl<K, V, S> LifetimeFree for std::collections::HashMap<K, V, S>
    where
        K: LifetimeFree,
        V: LifetimeFree,
        S: LifetimeFree,
    {
    }

    unsafe impl LifetimeFree for std::alloc::System {}
    unsafe impl LifetimeFree for std::backtrace::Backtrace {}
    unsafe impl LifetimeFree for std::backtrace::BacktraceStatus {}

    unsafe impl<K, V> LifetimeFree for std::collections::hash_map::IntoIter<K, V>
    where
        K: LifetimeFree,
        V: LifetimeFree,
    {
    }
    unsafe impl<K, V> LifetimeFree for std::collections::hash_map::IntoKeys<K, V>
    where
        K: LifetimeFree,
        V: LifetimeFree,
    {
    }
    unsafe impl<K, V> LifetimeFree for std::collections::hash_map::IntoValues<K, V>
    where
        K: LifetimeFree,
        V: LifetimeFree,
    {
    }
    unsafe impl<T> LifetimeFree for std::collections::hash_set::IntoIter<T> where T: LifetimeFree {}

    unsafe impl<T> LifetimeFree for std::collections::vec_deque::IntoIter<T> where T: LifetimeFree {}

    unsafe impl LifetimeFree for std::env::Args {}
    unsafe impl LifetimeFree for std::env::ArgsOs {}
    unsafe impl LifetimeFree for std::env::JoinPathsError {}
    unsafe impl LifetimeFree for std::env::Vars {}
    unsafe impl LifetimeFree for std::env::VarsOs {}
    unsafe impl LifetimeFree for std::env::VarError {}

    unsafe impl LifetimeFree for std::fs::DirBuilder {}
    unsafe impl LifetimeFree for std::fs::DirEntry {}
    unsafe impl LifetimeFree for std::fs::File {}
    unsafe impl LifetimeFree for std::fs::FileTimes {}
    unsafe impl LifetimeFree for std::fs::FileType {}
    unsafe impl LifetimeFree for std::fs::Metadata {}
    unsafe impl LifetimeFree for std::fs::OpenOptions {}
    unsafe impl LifetimeFree for std::fs::Permissions {}
    unsafe impl LifetimeFree for std::fs::ReadDir {}

    unsafe impl<R> LifetimeFree for std::io::BufReader<R> where R: ?Sized + LifetimeFree {}
    unsafe impl<W> LifetimeFree for std::io::BufWriter<W> where W: ?Sized + LifetimeFree + std::io::Write
    {}
    unsafe impl<R> LifetimeFree for std::io::Bytes<R> where R: LifetimeFree {}
    unsafe impl<T, U> LifetimeFree for std::io::Chain<T, U>
    where
        T: LifetimeFree,
        U: LifetimeFree,
    {
    }
    unsafe impl<T> LifetimeFree for std::io::Cursor<T> where T: LifetimeFree {}
    unsafe impl LifetimeFree for std::io::Empty {}
    unsafe impl LifetimeFree for std::io::Error {}
    unsafe impl<W> LifetimeFree for std::io::IntoInnerError<W> where W: LifetimeFree {}
    unsafe impl<W> LifetimeFree for std::io::LineWriter<W> where
        W: ?Sized + LifetimeFree + std::io::Write
    {
    }
    unsafe impl<B> LifetimeFree for std::io::Lines<B> where B: LifetimeFree {}
    unsafe impl LifetimeFree for std::io::Repeat {}
    unsafe impl LifetimeFree for std::io::Sink {}
    unsafe impl<B> LifetimeFree for std::io::Split<B> where B: LifetimeFree {}
    unsafe impl LifetimeFree for std::io::Stderr {}
    unsafe impl LifetimeFree for std::io::Stdin {}
    unsafe impl LifetimeFree for std::io::Stdout {}
    unsafe impl<T> LifetimeFree for std::io::Take<T> where T: LifetimeFree {}
    unsafe impl LifetimeFree for std::io::WriterPanicked {}
    unsafe impl LifetimeFree for std::io::ErrorKind {}
    unsafe impl LifetimeFree for std::io::SeekFrom {}

    unsafe impl LifetimeFree for std::net::TcpListener {}
    unsafe impl LifetimeFree for std::net::TcpStream {}
    unsafe impl LifetimeFree for std::net::UdpSocket {}
    unsafe impl LifetimeFree for std::net::Shutdown {}

    unsafe impl LifetimeFree for std::path::StripPrefixError {}

    unsafe impl LifetimeFree for std::process::Child {}
    unsafe impl LifetimeFree for std::process::ChildStderr {}
    unsafe impl LifetimeFree for std::process::ChildStdin {}
    unsafe impl LifetimeFree for std::process::ChildStdout {}
    unsafe impl LifetimeFree for std::process::Command {}
    unsafe impl LifetimeFree for std::process::ExitCode {}
    unsafe impl LifetimeFree for std::process::ExitStatus {}
    unsafe impl LifetimeFree for std::process::Output {}
    unsafe impl LifetimeFree for std::process::Stdio {}

    unsafe impl LifetimeFree for std::sync::Barrier {}
    unsafe impl LifetimeFree for std::sync::BarrierWaitResult {}
    unsafe impl LifetimeFree for std::sync::Condvar {}
    unsafe impl<T, F> LifetimeFree for std::sync::LazyLock<T, F>
    where
        T: LifetimeFree,
        F: LifetimeFree,
    {
    }
    unsafe impl<T> LifetimeFree for std::sync::Mutex<T> where T: ?Sized + LifetimeFree {}
    unsafe impl LifetimeFree for std::sync::Once {}
    unsafe impl<T> LifetimeFree for std::sync::OnceLock<T> where T: LifetimeFree {}
    unsafe impl LifetimeFree for std::sync::OnceState {}
    unsafe impl<T> LifetimeFree for std::sync::PoisonError<T> where T: LifetimeFree {}
    unsafe impl<T> LifetimeFree for std::sync::RwLock<T> where T: ?Sized + LifetimeFree {}
    unsafe impl LifetimeFree for std::sync::WaitTimeoutResult {}
    unsafe impl<T> LifetimeFree for std::sync::TryLockError<T> where T: LifetimeFree {}

    unsafe impl<T> LifetimeFree for std::sync::mpsc::IntoIter<T> where T: LifetimeFree {}
    unsafe impl<T> LifetimeFree for std::sync::mpsc::Receiver<T> where T: LifetimeFree {}
    unsafe impl LifetimeFree for std::sync::mpsc::RecvError {}
    unsafe impl<T> LifetimeFree for std::sync::mpsc::SendError<T> where T: LifetimeFree {}
    unsafe impl<T> LifetimeFree for std::sync::mpsc::Sender<T> where T: LifetimeFree {}
    unsafe impl<T> LifetimeFree for std::sync::mpsc::SyncSender<T> where T: LifetimeFree {}
    unsafe impl LifetimeFree for std::sync::mpsc::RecvTimeoutError {}
    unsafe impl LifetimeFree for std::sync::mpsc::TryRecvError {}
    unsafe impl<T> LifetimeFree for std::sync::mpsc::TrySendError<T> where T: LifetimeFree {}

    unsafe impl LifetimeFree for std::thread::AccessError {}
    unsafe impl LifetimeFree for std::thread::Builder {}
    unsafe impl<T> LifetimeFree for std::thread::JoinHandle<T> where T: LifetimeFree {}
    unsafe impl LifetimeFree for std::thread::Thread {}
    unsafe impl LifetimeFree for std::thread::ThreadId {}

    unsafe impl LifetimeFree for std::time::SystemTimeError {}
}

#[cfg(target_arch = "x86")]
#[cfg_attr(docsrs, doc(cfg(target_arch = "x86")))]
mod x86_impls {
    use crate::LifetimeFree;

    unsafe impl LifetimeFree for core::arch::x86::CpuidResult {}
    unsafe impl LifetimeFree for core::arch::x86::__m128 {}
    unsafe impl LifetimeFree for core::arch::x86::__m256 {}
    unsafe impl LifetimeFree for core::arch::x86::__m512 {}
    unsafe impl LifetimeFree for core::arch::x86::__m128d {}
    unsafe impl LifetimeFree for core::arch::x86::__m128i {}
    unsafe impl LifetimeFree for core::arch::x86::__m256d {}
    unsafe impl LifetimeFree for core::arch::x86::__m256i {}
    unsafe impl LifetimeFree for core::arch::x86::__m512d {}
    unsafe impl LifetimeFree for core::arch::x86::__m512i {}
}

#[cfg(target_arch = "x86_64")]
#[cfg_attr(docsrs, doc(cfg(target_arch = "x86_64")))]
mod x86_64_impls {
    use crate::LifetimeFree;

    unsafe impl LifetimeFree for core::arch::x86_64::CpuidResult {}
    unsafe impl LifetimeFree for core::arch::x86_64::__m128 {}
    unsafe impl LifetimeFree for core::arch::x86_64::__m256 {}
    unsafe impl LifetimeFree for core::arch::x86_64::__m512 {}
    unsafe impl LifetimeFree for core::arch::x86_64::__m128d {}
    unsafe impl LifetimeFree for core::arch::x86_64::__m128i {}
    unsafe impl LifetimeFree for core::arch::x86_64::__m256d {}
    unsafe impl LifetimeFree for core::arch::x86_64::__m256i {}
    unsafe impl LifetimeFree for core::arch::x86_64::__m512d {}
    unsafe impl LifetimeFree for core::arch::x86_64::__m512i {}
}

#[cfg(any(target_arch = "aarch64", target_arch = "arm64ec"))]
#[cfg_attr(
    docsrs,
    doc(cfg(any(target_arch = "aarch64", target_arch = "arm64ec")))
)]
mod aarch64_impls {
    use crate::LifetimeFree;

    unsafe impl LifetimeFree for core::arch::aarch64::float32x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::float32x2x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::float32x2x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::float32x2x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::float32x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::float32x4x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::float32x4x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::float32x4x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::float64x1_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::float64x1x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::float64x1x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::float64x1x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::float64x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::float64x2x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::float64x2x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::float64x2x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int8x8_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int8x8x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int8x8x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int8x8x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int8x16_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int8x16x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int8x16x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int8x16x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int16x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int16x4x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int16x4x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int16x4x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int16x8_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int16x8x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int16x8x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int16x8x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int32x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int32x2x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int32x2x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int32x2x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int32x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int32x4x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int32x4x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int32x4x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int64x1_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int64x1x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int64x1x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int64x1x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int64x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int64x2x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int64x2x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::int64x2x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly8x8_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly8x8x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly8x8x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly8x8x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly8x16_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly8x16x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly8x16x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly8x16x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly16x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly16x4x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly16x4x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly16x4x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly16x8_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly16x8x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly16x8x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly16x8x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly64x1_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly64x1x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly64x1x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly64x1x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly64x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly64x2x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly64x2x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::poly64x2x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint8x8_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint8x8x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint8x8x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint8x8x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint8x16_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint8x16x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint8x16x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint8x16x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint16x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint16x4x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint16x4x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint16x4x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint16x8_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint16x8x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint16x8x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint16x8x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint32x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint32x2x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint32x2x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint32x2x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint32x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint32x4x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint32x4x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint32x4x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint64x1_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint64x1x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint64x1x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint64x1x4_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint64x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint64x2x2_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint64x2x3_t {}
    unsafe impl LifetimeFree for core::arch::aarch64::uint64x2x4_t {}
}

#[cfg(target_arch = "wasm32")]
#[cfg_attr(docsrs, doc(cfg(target_arch = "wasm32")))]
mod aarch64_impls {
    use crate::LifetimeFree;

    unsafe impl LifetimeFree for core::arch::wasm32::v128 {}
}

#[cfg(all(feature = "std", any(unix, target_os = "hermit", target_os = "wasi")))]
#[cfg_attr(
    docsrs,
    doc(cfg(all(feature = "std", any(unix, target_os = "hermit", target_os = "wasi"))))
)]
mod fd_impls {
    use crate::LifetimeFree;

    unsafe impl LifetimeFree for std::os::fd::OwnedFd {}
}

// First `cfg` is copied from stdlib sources.
#[cfg(not(any(
    all(target_arch = "wasm32", not(target_os = "wasi")),
    all(target_vendor = "fortanix", target_env = "sgx")
)))]
#[cfg(all(feature = "std", not(target_os = "hermit"), unix))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "std", unix))))]
mod unix_impls {
    use crate::LifetimeFree;

    unsafe impl LifetimeFree for std::os::unix::net::SocketAddr {}
    unsafe impl LifetimeFree for std::os::unix::net::UnixDatagram {}
    unsafe impl LifetimeFree for std::os::unix::net::UnixListener {}
    unsafe impl LifetimeFree for std::os::unix::net::UnixStream {}
}

// First `cfg` is copied from stdlib sources.
#[cfg(not(any(
    all(target_arch = "wasm32", not(target_os = "wasi")),
    all(target_vendor = "fortanix", target_env = "sgx")
)))]
#[cfg(all(feature = "std", windows))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "std", windows))))]
mod windows_impls {
    use crate::LifetimeFree;

    unsafe impl LifetimeFree for std::os::windows::io::HandleOrInvalid {}
    unsafe impl LifetimeFree for std::os::windows::io::HandleOrNull {}
    unsafe impl LifetimeFree for std::os::windows::io::InvalidHandleError {}
    unsafe impl LifetimeFree for std::os::windows::io::NullHandleError {}
    unsafe impl LifetimeFree for std::os::windows::io::OwnedHandle {}
    unsafe impl LifetimeFree for std::os::windows::io::OwnedSocket {}
}
