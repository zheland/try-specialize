#![allow(missing_docs, reason = "okay in tests")]
#![expect(unused_crate_dependencies, reason = "okay in tests")]
#![cfg(not(miri))]
#![cfg(not(debug_assertions))] // Requires `profile.opt-level >= 1`

use std::collections::{HashMap, HashSet};

use paste::paste;
use try_specialize::TrySpecialize;

mod common;

#[cfg(feature = "__test_extern_fn_merging")]
#[rustversion::all(before(2024-08-13), before(1.82))]
const RUST_VERSION_GE_1_82: bool = false;

#[cfg(feature = "__test_extern_fn_merging")]
#[rustversion::any(since(2024-08-13), since(1.82))]
const RUST_VERSION_GE_1_82: bool = true;

#[test]
fn test_zero_cost_specialization_fn_ptrs() {
    #[derive(Clone, Default, Debug)]
    struct Stats {
        matched: usize,
        alternative_fn_ptrs: HashSet<*const u8>,
        total: usize,
    }

    let reference_fn_ptrs = collect_reference_fn_ptrs();
    let tested_fn_ptrs = collect_tested_fn_ptrs();

    let mut stats: HashMap<_, _> = [
        ("core", Stats::default()),
        ("alloc", Stats::default()),
        ("std", Stats::default()),
    ]
    .into_iter()
    .collect();

    for ((lib1, tested_fn_kind, ty1, ty2), tested_fn_ptr) in tested_fn_ptrs {
        let reference_fn_kind = match tested_fn_kind {
            "to_ltfree" | "from_ltfree" | "static" => "value",
            "to_ltfree_ref" | "from_ltfree_ref" | "static_ref" => "ref",
            "to_ltfree_mut" | "from_ltfree_mut" | "static_mut" => "mut",
            _ => panic!("unexpected function kind"),
        };

        let reference_fn_ptr = reference_fn_ptrs[&(reference_fn_kind, ty1, ty1 == ty2)];
        let stats = stats.get_mut(lib1).unwrap();
        if tested_fn_ptr == reference_fn_ptr {
            stats.matched += 1;
        } else {
            let _: bool = stats.alternative_fn_ptrs.insert(tested_fn_ptr);

            if lib1 == "core" || reference_fn_kind != "value" {
                #[cfg(feature = "__test_extern_fn_merging")]
                assert!(
                    (lib1 != "core" && reference_fn_kind == "value") || !RUST_VERSION_GE_1_82,
                    "Since Rust 1.82 it is expected that function merging might fail only for \
                     non-core types passed by value. Function data: ({}, {}, {}, {})",
                    lib1,
                    tested_fn_kind,
                    ty1,
                    ty2
                );

                let valid_expected = if ty1 == ty2 {
                    valid_ret_true_fn_asm()
                } else {
                    valid_ret_false_fn_asm()
                };

                assert!(
                    valid_expected
                        .iter()
                        .any(|expected| cmp_fn_asm(tested_fn_ptr, expected)),
                    "Generated function is not matched to any expected one"
                );
            }
        }
        stats.total += 1;
    }

    // Expected values depend on tested types amount.
    #[cfg(not(feature = "alloc"))]
    let expected = [1303, 0, 0];
    #[cfg(all(feature = "alloc", not(feature = "std")))]
    let expected = [1532, 267, 0];
    #[cfg(feature = "std")]
    let expected = [1711, 297, 233];

    assert_eq!(stats["core"].total, expected[0]);
    assert_eq!(stats["alloc"].total, expected[1]);
    assert_eq!(stats["std"].total, expected[2]);

    dbg!(&stats);

    #[cfg(feature = "__test_extern_fn_merging")]
    {
        if RUST_VERSION_GE_1_82 {
            // 100% of core fns are expected to have same asm since Rust 1.82.
            assert_eq!(stats["core"].matched, stats["core"].total);
        } else {
            // More than 99% of fns are expected to have same asm before Rust 1.82.
            assert!(stats["core"].matched >= stats["core"].total * 99 / 100);
        }

        // Thresholds below are approximate and may be adjusted in the future.
        assert!(stats["alloc"].matched >= stats["alloc"].total * 2 / 3);
        assert!(stats["std"].matched >= stats["std"].total * 2 / 3);
        if RUST_VERSION_GE_1_82 {
            assert!(stats["alloc"].alternative_fn_ptrs.len() < 4);
            assert!(stats["std"].alternative_fn_ptrs.len() < 4);
        } else {
            assert!(stats["alloc"].alternative_fn_ptrs.len() < 8);
            assert!(stats["std"].alternative_fn_ptrs.len() < 8);
        }
    }
}

fn cmp_fn_asm(fn_ptr: *const u8, expected: &[u8]) -> bool {
    for (offset, &expected) in expected.iter().enumerate() {
        // SAFETY: Locally defined extern functions should be readable.
        let byte = unsafe { fn_ptr.byte_add(offset).read() };
        if byte != expected {
            return false;
        }
    }
    true
}

#[rustversion::all(before(2024-08-13), before(1.82))]
fn valid_ret_false_fn_asm() -> &'static [&'static [u8]] {
    &[
        &[
            0x31, 0xC0, // xorl %eax, %eax
            0xC3, // retq
        ],
        // Generates suboptimal, but valid bytecode for `Option`s.
        // The `Option` tag (passed in %edi) can never be equal to 2, so it
        // will never return 1.
        //
        // Improved in:
        // - <https://github.com/rust-lang/rust/issues/50156>,
        // - <https://github.com/rust-lang/rust/commit/e08b80c0fb7667bdcd040761891701e576c42ec8>.
        &[
            0x83, 0xFF, 0x02, // cmpl $2, %edi
            0x0F, 0x94, 0xC0, // sete %al
            0xC3, // retq
        ],
    ]
}

#[rustversion::any(since(2024-08-13), since(1.82))]
fn valid_ret_false_fn_asm() -> &'static [&'static [u8]] {
    &[&[
        0x31, 0xC0, // xorl %eax, %eax
        0xC3, // retq
    ]]
}

fn valid_ret_true_fn_asm() -> &'static [&'static [u8]] {
    &[&[
        0xB0, 0x01, // movb $1, %al
        0xC3, // retq
    ]]
}

/// Defines the reference function that have a signature similar to the
/// functions being checked, but unlike them return the specified constant.
macro_rules! define_reference_fn {
    {
        { $lib:tt $name:ident: $ty:ty }
        { $kind:tt, $const:literal }
    } => {
        paste! {
            #[allow(clippy::missing_const_for_fn)]
            #[no_mangle]
            extern "Rust" fn [< $kind _from_ $name _to_ $const >](_: $ty) -> bool {
                $const
            }
        }
    };
}

// For all compatible ($kind, $ty, $const) defines reference fns like:
// - `fn ${kind}_from_${ty}_to_${const}(_: ${ty}) -> bool { ${const} }`.
chain! {
    for_all_types!
    | for_each!
    | for_each_reference_fn!
    | define_reference_fn!
}

/// Inserts checked to a specified map.
macro_rules! insert_reference_fn_to_map {
    ({ { $lib:tt $name:ident : $ty:ty } { $kind:tt, $const:literal } } { $map:path }) => {
        if $map
            .insert(
                (stringify!($kind), stringify!($name), $const),
                common::fn_raw_ptr(paste! { [< $kind _from_ $name _to_ $const >] }),
            )
            .is_some()
        {
            cold_unexpected_duplicate_reference_fn(stringify!($kind), stringify!($name), $const);
        }
    };
}

fn collect_reference_fn_ptrs() -> HashMap<(&'static str, &'static str, bool), *const u8> {
    let mut map = HashMap::new();

    macro_rules! with_local_map_var {
        ( $in:tt | $func:ident! $args:tt ) => {
            $func!( { $in { map }} $args )
        }
    }

    chain! {
        for_all_types!
        | for_each!
        | for_each_reference_fn!
        | with_local_map_var!
        | insert_reference_fn_to_map!
    }

    map
}

/// Defines tested function.
macro_rules! define_tested_fn {
    (
        { $lib1:tt $lt1:tt $size1:tt $name1:ident : $ty1:ty = $example1:expr } { $lib2:tt $lt2:tt $size2:tt $name2:ident : $ty2:ty = $example2:expr } { $kind:tt, $arg:ident => $try_specialize_expr:expr } { $ok_pat:pat, $fail_pat:pat, $ok:expr, $fail:expr }
    ) => {
        paste! {
            #[no_mangle]
            extern "Rust" fn [<
                $kind _from_ $name1 _to_ $name2 _is_ok
            >]( $arg: $ty1 ) -> bool {
                match $try_specialize_expr {
                    $ok_pat => true,
                    $fail_pat => false,
                }
            }
        }
    };
}

// For all compatible ($kind, $ty1, $ty2) defines reference fns like:
// - `fn {kind}_from_${ty1}_to_${ty2}(_: ${ty1}) -> bool { ... }`.
chain! {
    for_all_types!
    | for_each_cartesian_square_pair!
    | for_each_cartesian_pair_tested_fn!
    | define_tested_fn!
}

/// Inserts checked to a specified map.
macro_rules! insert_tested_fn_to_map {
    (
        {
            { $lib1:tt $lt1:tt $size1:tt $name1:ident : $ty1:ty = $example1:expr } { $lib2:tt $lt2:tt $size2:tt $name2:ident : $ty2:ty = $example2:expr } { $kind:tt, $arg:ident => $try_specialize_expr:expr } { $ok_pat:pat, $fail_pat:pat, $ok:expr, $fail:expr }
        } { $map:path }
    ) => {
        if $map
            .insert(
                (
                    stringify!($lib1),
                    stringify!($kind),
                    stringify!($name1),
                    stringify!($name2),
                ),
                common::fn_raw_ptr(paste! { [< $kind _from_ $name1 _to_ $name2 _is_ok >] }),
            )
            .is_some()
        {
            cold_unexpected_duplicate_tested_fn(
                stringify!($kind),
                stringify!($name1),
                stringify!($name2),
            );
        }
    };
}

fn collect_tested_fn_ptrs(
) -> HashMap<(&'static str, &'static str, &'static str, &'static str), *const u8> {
    let mut map = HashMap::new();

    macro_rules! with_local_map_var {
        ( $in:tt | $func:ident! $args:tt ) => {
            $func!( { $in { map }} $args )
        }
    }

    chain! {
        for_all_types!
        | for_each_cartesian_square_pair!
        | for_each_cartesian_pair_tested_fn!
        | with_local_map_var!
        | insert_tested_fn_to_map!
    }

    map
}

// Extracted to separate function to optimize test build times.
#[cold]
#[inline(never)]
fn cold_unexpected_duplicate_reference_fn(kind: &'static str, ty: &'static str, value: bool) -> ! {
    panic!("unexpected duplicate reference function found for {kind}, {ty}, {value}");
}

// Extracted to separate function to optimize test build times.
#[cold]
#[inline(never)]
fn cold_unexpected_duplicate_tested_fn(
    kind: &'static str,
    ty1: &'static str,
    ty2: &'static str,
) -> ! {
    panic!("unexpected duplicate tested function found for {kind}, {ty1}, {ty2}");
}
