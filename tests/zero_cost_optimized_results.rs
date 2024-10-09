#![allow(missing_docs, reason = "okay in tests")]
#![expect(unused_crate_dependencies, reason = "okay in tests")]
#![cfg(not(miri))]
#![cfg(not(debug_assertions))] // Requires `profile.opt-level >= 1`

use core::convert::identity;

use try_specialize::TrySpecialize;

mod common;

#[rustfmt::skip]
macro_rules! check_tested_fn {
    (
        {
            { $lib1:tt $lt1:tt $size1:tt $name1:ident : $ty1:ty = $example1:expr }
            { $lib2:tt $lt2:tt $size2:tt $name2:ident : $ty2:ty = $example2:expr }
            { $kind:tt, $arg:ident => $try_specialize_expr:expr }
            { $ok_pat:pat, $fail_pat:pat, $ok:expr, $fail:expr }
        } { $counters:path }
    ) => {{
        mif! { if (eq $lib1 core) {
            #[cfg(feature = "__test_extern_fn_dce")]
            extern "C" {
                // This function can not be linked.
                // Test checks that the code paths calling this function are optimized away.
                #[link_name = concat!(
                    "should_be_unreachable_on_link_time\n",
                    "ERROR: link time check failed for `",
                    stringify!($kind),
                    "_from_",
                    stringify!($name1),
                    "_to_",
                    stringify!($name2),
                    "_is_ok`\n",
                    "This check is highly dependent on the optimizer success, ",
                    "so an error in it does not necessarily mean an error in the ",
                    "library code."
                )]
                fn should_be_unreachable_on_link_time() -> !;
            }
        }}

        if stringify!($name1) == stringify!($name2) {
            $counters.num_eq_names += 1;
        } else {
            $counters.num_ne_names += 1;
        }

        match identity::<$ty1>($example1) {
            $arg => {
                let result = $try_specialize_expr;

                #[allow(unreachable_code, reason = "Okay in tests.")]
                if stringify!($name1) == stringify!($name2) {
                    if result != $ok {
                        cold_unexpected_specialization_success_panic(
                            stringify!($name1),
                            stringify!($name2),
                        );
                        mif! { if (eq $lib1 core) {
                            // Core types can be checked at compile time.
                            #[cfg(feature = "__test_extern_fn_dce")]
                            unsafe { should_be_unreachable_on_link_time() }
                        }}
                    }
                } else {
                    if result != $fail {
                        cold_unexpected_specialization_failure_panic(
                            stringify!($name1),
                            stringify!($name2),
                        );
                        mif! { if (eq $lib1 core) {
                            // Core types can be checked at compile time.
                            #[cfg(feature = "__test_extern_fn_dce")]
                            unsafe { should_be_unreachable_on_link_time() }
                        }}
                    }
                }
            }
        }
    }};
}

#[test]
fn test_zero_cost_specialization_fn_merging_and_results() {
    struct Counters {
        num_eq_names: usize,
        num_ne_names: usize,
    }

    let mut counters = Counters {
        num_eq_names: 0,
        num_ne_names: 0,
    };

    macro_rules! with_local_counters_var {
        ( $in:tt | $func:ident! $args:tt ) => {
            $func!( { $in { counters }} $args )
        }
    }

    chain! {
        for_all_types!
        | for_each_cartesian_square_pair!
        | for_each_cartesian_pair_tested_fn!
        | with_local_counters_var!
        | check_tested_fn!
    }

    // Expected values depend on tested types amount.
    #[cfg(not(feature = "alloc"))]
    let expected = [105, 1198];
    #[cfg(all(feature = "alloc", not(feature = "std")))]
    let expected = [119, 1680];
    #[cfg(feature = "std")]
    let expected = [131, 2110];

    assert_eq!(counters.num_eq_names, expected[0]);
    assert_eq!(counters.num_ne_names, expected[1]);
}

// Extracted to separate function to optimize test build times.
#[cold]
#[inline(never)]
fn cold_unexpected_specialization_success_panic(ty1: &'static str, ty2: &'static str) -> ! {
    panic!("unexpected specialization success for types {ty1}, {ty2}");
}

// Extracted to separate function to optimize test build times.
#[cold]
#[inline(never)]
fn cold_unexpected_specialization_failure_panic(ty1: &'static str, ty2: &'static str) -> ! {
    panic!("unexpected specialization failure for types {ty1}, {ty2}");
}
