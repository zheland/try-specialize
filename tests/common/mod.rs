#![allow(dead_code)]

#[cfg(feature = "alloc")]
use std::borrow::Cow;
#[cfg(feature = "std")]
use std::collections::HashMap;
#[cfg(feature = "alloc")]
use std::collections::{BTreeMap, BTreeSet};
#[cfg(feature = "std")]
use std::path::Path;
#[cfg(feature = "std")]
use std::sync::Arc;

/// Allows to use the results of one macro as input for another macro in easy
/// way. Requires support for special `pipe`-like syntax from any macro in the
/// chain except the last one.
///
/// An example of the recursive macro expansion steps:
/// - `chain! { generator! | mapper! | filter! | flattener! | sink! }`,
/// - `generator! { chain! { | mapper! | filter! | flattener! | sink! }}`,
/// - `chain! { GENERATED_DATA | mapper! | filter! | flattener! | sink! }`,
/// - `mapper! { GENERATED_DATA | chain! { | filter! | flattener! | sink! }}`,
/// - `chain! { MAPPED_DATA | filter! | flattener! | sink! }`,
/// - `filter! { MAPPED_DATA | chain! { | flattener! | sink! }}`,
/// - `chain! { FILTERED_DATA | flattener! | sink! }`,
/// - `flattener! { FILTERED_DATA | chain! { | sink! }}`,
/// - `chain! { FLATTENED_DATA | sink! }`,
/// - `sink! FLATTENED_DATA`.
#[macro_export]
macro_rules! chain {
    { $in:tt { $( $tail:tt )* } } => {
        chain! { $in $( $tail )* }
    };
    { $in:tt | $func:ident! | $( $tail:tt )* } => {
        $func! { $in | chain! { | $( $tail )* } }
    };
    { $in:tt | $func:ident! } => {
        $func! $in
    };
    { $func:ident! | $( $tail:tt )* } => {
        $func! { chain! { | $( $tail )* } }
    };
}

/// Calls the callback macro for each item in a list.
#[macro_export]
macro_rules! for_each {
    { [ $( $tt:tt )* ] | $func:ident! $args:tt } => {
        $( $func! { $tt $args } )*
    };
}

/// Calls the callback macro for each pair of list cartesian square set.
#[macro_export]
macro_rules! for_each_cartesian_square_pair {
    { [ $( $tt:tt )* ] | $func:ident! $args:tt } => {
        for_each_cartesian_product_pair! {
            ( [ $( $tt )* ] x [ $( $tt )* ] ) | $func! $args
        }
    };
}

/// Calls the callback macro for each pair of two lists cartesian product set.
#[macro_export]
macro_rules! for_each_cartesian_product_pair {
    { ( [] x [ $( $right:tt )* ] ) | $func:ident! $args:tt } => {};
    {
        ( [ $left_next:tt $( $left_rest:tt )* ] x [ $( $right_all:tt )* ] )
        | $func:ident! $args:tt
    } => {
        $( $func! { { $left_next $right_all } $args } )*
        for_each_cartesian_product_pair! {
            ( [ $( $left_rest )* ] x [ $( $right_all )* ] ) | $func! $args
        }
    };
}

/// Computes if-then-else-like expressions.
///
/// Keep in mind that in Rust the order of macro expansion is undefined,
/// which forces to use recursion more often in the auxiliary macros
/// implementations.
#[macro_export]
macro_rules! mif {
    { if true { $( $then:tt )* } $( else { $( $else:tt )* } )? } => {
        $( $then )*
    };
    { if false { $( $then:tt )* } $( else { $( $else:tt )* } )? } => {
        $( $( $else )* )?
    };

    { if core $( $tt:tt )* } => { mif! { if true $( $tt )* } };
    { if alloc $( $tt:tt )* } => { mif_alloc! { $( $tt )* } };
    { if std $( $tt:tt )* } => { mif_std! { $( $tt )* } };

    { if ( eq $left:tt $right:tt ) $( $tt:tt )* } => {
        mif_eq! { ($left, $right) $( $tt )* }
    };
    { if ( not $cond:tt ) $then:tt } => {
        mif! { if $cond {} else $then }
    };
    { if ( not $cond:tt ) $then:tt else $else:tt } => {
        mif! { if $cond $else else $then }
    };
    { if ( all ) $( $tt:tt )* } => {
        mif! { if true $( $tt )* }
    };
    { if ( all $first:tt $( $rest:tt )* ) $( $tt:tt )* } => {
        mif! {
            if $first {
                mif! { if ( all $( $rest )* ) $( $tt )* }
            } else {
                mif! { if false $( $tt )* }
            }
        }
    };
}

/// An auxiliary feature-dependent macro for a `mif` macro.
#[macro_export]
#[cfg(feature = "alloc")]
macro_rules! mif_alloc {
    { $( $tt:tt )* } => { mif! { if true $( $tt )* } }
}

/// An auxiliary feature-dependent macro for a `mif` macro.
#[macro_export]
#[cfg(not(feature = "alloc"))]
macro_rules! mif_alloc {
    { $( $tt:tt )* } => { mif! { if false $( $tt )* } }
}

/// An auxiliary feature-dependent macro for a `mif` macro.
#[macro_export]
#[cfg(feature = "std")]
macro_rules! mif_std {
    { $( $tt:tt )* } => { mif! { if true $( $tt )* } }
}

/// An auxiliary feature-dependent macro for a `mif` macro.
#[macro_export]
#[cfg(not(feature = "std"))]
macro_rules! mif_std {
    { $( $tt:tt )* } => { mif! { if false $( $tt )* } }
}

/// An auxiliary equality check macro for a `mif` macro.
#[macro_export]
macro_rules! mif_eq {
    { ( core, core ) $( $tt:tt )* } => { mif! { if true $( $tt )* } };
    { ( $_:tt, core ) $( $tt:tt )* } => { mif! { if false $( $tt )* } };
    { ( ltfree, ltfree ) $( $tt:tt )* } => { mif! { if true $( $tt )* } };
    { ( $_:tt, ltfree ) $( $tt:tt )* } => { mif! { if false $( $tt )* } };
    { ( sized, sized ) $( $tt:tt )* } => { mif! { if true $( $tt )* } };
    { ( $_:tt, sized ) $( $tt:tt )* } => { mif! { if false $( $tt )* } };
}

/// For a given checked type, determines the set of required reference
/// functions, and calls the callback macro for each such function.
#[macro_export]
macro_rules! for_each_reference_fn {
    {
        { $lib:tt $lt:tt $size:tt $name:ident: $ty:ty = $example:expr }
        | $func:ident! $args:tt
    } => {
        mif! { if $lib {
            mif! { if (eq $size sized) {
                $func! { { { $lib $name: $ty } { value, false } } $args }
                $func! { { { $lib $name: $ty } { value, true } } $args }
            }}
            $func! { { { $lib $name: &$ty } { ref, false } } $args }
            $func! { { { $lib $name: &$ty } { ref, true } } $args }
            $func! { { { $lib $name: &mut $ty } { mut, false } } $args }
            $func! { { { $lib $name: &mut $ty } { mut, true } } $args }
        }}
    };
}

/// For a given pair of checked types, determines the set of required checked
/// functions, and calls the callback macro for each such function.
#[macro_export]
macro_rules! for_each_cartesian_pair_tested_fn {
    {
        {
            { $lib1:tt $lt1:tt $size1:tt $name1:ident: $ty1:ty = $example1:expr }
            { $lib2:tt $lt2:tt $size2:tt $name2:ident: $ty2:ty = $example2:expr }
        } | $func:ident! $args:tt
    } => {
        mif! { if (all $lib1 $lib2) {
            mif! { if (eq $lt2 ltfree) {
                mif! { if (all (eq $size1 sized) (eq $size2 sized)) {
                    $func! {
                        {
                            { $lib1 $lt1 $size1 $name1: $ty1 = $example1 }
                            { $lib2 $lt2 $size2 $name2: $ty2 = $example2 }
                            { to_ltfree, arg => arg.try_specialize::<$ty2>() }
                            { Ok(_ok), Err(_err), Ok($example2), Err($example1) }
                        }
                        $args
                    }
                }}
                $func! {
                    {
                        { $lib1 $lt1 $size1 $name1: &$ty1 = &$example1 }
                        { $lib2 $lt2 $size2 $name2: &$ty2 = &$example2 }
                        { to_ltfree_ref, arg => arg.try_specialize_ref::<$ty2>() }
                        { Some(_some), None, Some(&$example2), None }
                    }
                    $args
                }
                $func! {
                    {
                        { $lib1 $lt1 $size1 $name1: &mut $ty1 = &mut $example1 }
                        { $lib2 $lt2 $size2 $name2: &mut $ty2 = &mut $example2 }
                        { to_ltfree_mut, arg => arg.try_specialize_mut::<$ty2>() }
                        { Some(_some), None, Some(&mut $example2), None }
                    }
                    $args
                }
            }}
            mif! { if (eq $lt1 ltfree) {
                mif! { if (all (eq $size1 sized) (eq $size2 sized)) {
                    $func! {
                        {
                            { $lib1 $lt1 $size1 $name1: $ty1 = $example1 }
                            { $lib2 $lt2 $size2 $name2: $ty2 = $example2 }
                            { from_ltfree, arg => <$ty2>::try_specialize_from(arg) }
                            { Ok(_ok), Err(_err), Ok($example2), Err($example1) }
                        }
                        $args
                    }
                }}
                $func! {
                    {
                        { $lib1 $lt1 $size1 $name1: &$ty1 = &$example1 }
                        { $lib2 $lt2 $size2 $name2: &$ty2 = &$example2 }
                        { from_ltfree_ref, arg => <$ty2>::try_specialize_from_ref(arg) }
                        { Some(_some), None, Some(&$example2), None }
                    }
                    $args
                }
                $func! {
                    {
                        { $lib1 $lt1 $size1 $name1: &mut $ty1 = &mut $example1 }
                        { $lib2 $lt2 $size2 $name2: &mut $ty2 = &mut $example2 }
                        { from_ltfree_mut, arg => <$ty2>::try_specialize_from_mut(arg) }
                        { Some(_some), None, Some(&mut $example2), None }
                    }
                    $args
                }
            }}
            mif! { if (all (eq $size1 sized) (eq $size2 sized)) {
                $func! {
                    {
                        { $lib1 $lt1 $size1 $name1: $ty1 = $example1 }
                        { $lib2 $lt2 $size2 $name2: $ty2 = $example2 }
                        { static, arg => arg.try_specialize_static::<$ty2>() }
                        { Ok(_ok), Err(_err), Ok($example2), Err($example1) }
                    }
                    $args
                }
            }}
            $func! {
                {
                    { $lib1 $lt1 $size1 $name1: &$ty1 = &$example1 }
                    { $lib2 $lt2 $size2 $name2: &$ty2 = &$example2 }
                    { static_ref, arg => arg.try_specialize_ref_static::<$ty2>() }
                    { Some(_some), None, Some(&$example2), None }
                }
                $args
            }
            $func! {
                {
                    { $lib1 $lt1 $size1 $name1: &mut $ty1 = &mut $example1 }
                    { $lib2 $lt2 $size2 $name2: &mut $ty2 = &mut $example2 }
                    { static_mut, arg => arg.try_specialize_mut_static::<$ty2>() }
                    { Some(_some), None, Some(&mut $example2), None }
                }
                $args
            }
        }}
    }
}

/// Calls the callback macro will all checked types.
///
/// Adding each additional type non-linearly increases compilation time.
#[macro_export]
macro_rules! for_all_types {
    ($func:ident ! $args:tt) => {
        $func! {
            [
                { core ltfree sized unit: () = () }
                { core ltfree sized bool: bool = true }
                { core ltfree sized u32: u32 = 123_456_789 }
                { core ltfree sized i32: i32 = -123_456_789 }
                { core ltfree sized f64: f64 = 123.456 }
                { core ltfree sized u128: u128 = u128::MAX - 123_456_789 }
                { core ltfree sized array_u8_8: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8] }
                { core ltfree sized tuple_u32_f64_u8: (u32, f64, u8) = (987_654_321, 987.654, 123) }
                { core ltfree sized option_u32: Option<u32> = Some(123_123_123) }
                {
                    core ltfree sized result_unit_i8:
                        Result<(), ::core::num::NonZero<u8>> =
                        Err(::core::num::NonZero::new(1).unwrap())
                }
                {
                    core ltfree unsized str: str =
                        *unsafe { ::core::str::from_utf8_unchecked_mut(&mut { *b"bar" }) }
                    // expression above is used to make string literal mutable if needed
                }
                {
                    core ltfree unsized slice_option_u16: [Option<i16>] = [
                        Some(12_345), None, Some(-123), None, Some(1)
                    ]
                }
                { core static sized str_static_ref: &'static str = "foo" }
                {
                    alloc ltfree sized btreeset_string_vec_u8:
                        ::std::collections::BTreeSet<String> =
                        $crate::common::btreeset_string_vec_u8_example()
                }
                {
                    alloc static sized btreemap_cow_str_string:
                        ::std::collections::BTreeMap<
                            ::std::borrow::Cow<'static, str>,
                            String
                        > = $crate::common::btreemap_cow_str_string_example()
                }
                {
                    alloc static unsized slice_cow_static_u32:
                        [::std::borrow::Cow<'static, u8>] = [
                            ::std::borrow::Cow::Owned(12),
                            ::std::borrow::Cow::Borrowed(&23),
                            ::std::borrow::Cow::Owned(34),
                            ::std::borrow::Cow::Borrowed(&45)
                        ]
                }
                {
                    std ltfree sized hashmap_i32_box_str:
                        ::std::collections::HashMap<i32, Box<str>> =
                        $crate::common::hashmap_i32_box_str_example()
                }
                {
                    std static sized hashmap_arc_path_static_str:
                        ::std::collections::HashMap<
                            ::std::sync::Arc<::std::path::Path>,
                            &'static [u8]
                        > = $crate::common::hashmap_arc_path_static_str_example()
                }
            ]
            $args
        }
    };
}

#[cfg(feature = "alloc")]
#[must_use]
pub fn btreeset_string_vec_u8_example() -> BTreeSet<String> {
    ["a", "b", "c"]
        .map(ToString::to_string)
        .into_iter()
        .collect()
}

#[cfg(feature = "alloc")]
#[must_use]
pub fn btreemap_cow_str_string_example() -> BTreeMap<Cow<'static, str>, String> {
    [
        (Cow::Owned("a".to_string() + "bc"), String::from("qwe")),
        (Cow::Borrowed("efg"), String::from("asd")),
        (Cow::Borrowed("ijk"), String::from("zxc")),
    ]
    .into_iter()
    .collect()
}

#[cfg(feature = "std")]
#[must_use]
pub fn hashmap_i32_box_str_example() -> HashMap<i32, Box<str>> {
    [
        (1, Box::from("foo")),
        (2, Box::from("bar")),
        (3, Box::from("qwe")),
    ]
    .into_iter()
    .collect()
}

#[cfg(feature = "std")]
#[must_use]
pub fn hashmap_arc_path_static_str_example() -> HashMap<Arc<Path>, &'static [u8]> {
    [
        (Arc::from(Path::new("here")), &b"first"[..]),
        (Arc::from(Path::new("there")), &[1, 2, 3]),
        (Arc::from(Path::new("nowhere")), &[123; 12]),
    ]
    .into_iter()
    .collect()
}

// When called, it implicitly coerce function to function pointer.
#[expect(clippy::as_conversions, reason = "okay in tests")]
pub const fn fn_raw_ptr<T, R>(func: extern "Rust" fn(T) -> R) -> *const u8 {
    (func as *const fn(T) -> R).cast::<u8>()
}
