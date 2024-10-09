#![allow(missing_docs, reason = "okay in tests")]
#![expect(unused_crate_dependencies, reason = "okay in tests")]
#![cfg(not(miri))]
#![cfg(not(debug_assertions))] // Requires `profile.opt-level >= 1`
#![cfg(all(feature = "alloc", feature = "unreliable"))]

use try_specialize::unreliable::{
    impls_clone_weak, impls_copy_weak, impls_eq_weak, impls_lifetime_free_weak,
    impls_partial_eq_weak,
};

#[cfg(feature = "__test_extern_fn_dce")]
extern "C" {
    // This function can not be linked.
    // Test checks that the code paths calling this function are optimized away.
    fn should_be_unreachable_on_link_time() -> !;
}

#[inline]
fn expect(value: bool) {
    if !value {
        #[cfg(feature = "__test_extern_fn_dce")]
        unsafe {
            should_be_unreachable_on_link_time()
        };
    }
}

#[test]
fn test_zero_cost_unreliable_impls_checks() {
    #[derive(Copy, Clone)]
    struct Copiable;
    #[derive(Clone)]
    struct Cloneable;
    struct NonCloneable;

    expect(impls_copy_weak::<()>());
    expect(impls_copy_weak::<u32>());
    expect(impls_copy_weak::<f64>());
    expect(impls_copy_weak::<Copiable>());
    expect(!impls_copy_weak::<Cloneable>());
    expect(!impls_copy_weak::<NonCloneable>());

    expect(impls_clone_weak::<()>());
    expect(impls_clone_weak::<u32>());
    expect(impls_clone_weak::<f64>());
    expect(impls_clone_weak::<Copiable>());
    expect(impls_clone_weak::<Cloneable>());
    expect(!impls_clone_weak::<NonCloneable>());

    expect(impls_eq_weak::<()>());
    expect(impls_eq_weak::<u32>());
    expect(!impls_eq_weak::<f64>());
    expect(impls_eq_weak::<&String>());
    expect(impls_eq_weak::<&Vec<u8>>());
    expect(impls_eq_weak::<String>());
    expect(impls_eq_weak::<Vec<u8>>());
    expect(impls_eq_weak::<&mut String>());
    expect(impls_eq_weak::<&mut Vec<u8>>());

    expect(impls_partial_eq_weak::<()>());
    expect(impls_partial_eq_weak::<u32>());
    expect(impls_partial_eq_weak::<f64>());
    expect(impls_partial_eq_weak::<&String>());
    expect(impls_partial_eq_weak::<&Vec<u8>>());
    expect(impls_partial_eq_weak::<String>());
    expect(impls_partial_eq_weak::<Vec<u8>>());
    expect(impls_partial_eq_weak::<&mut String>());
    expect(impls_partial_eq_weak::<&mut Vec<u8>>());

    expect(impls_lifetime_free_weak::<()>());
    expect(impls_lifetime_free_weak::<u32>());
    expect(impls_lifetime_free_weak::<f64>());
    expect(!impls_lifetime_free_weak::<&String>());
    expect(!impls_lifetime_free_weak::<&Vec<u8>>());
    expect(impls_lifetime_free_weak::<String>());
    expect(impls_lifetime_free_weak::<Vec<u8>>());
    expect(!impls_lifetime_free_weak::<&mut String>());
    expect(!impls_lifetime_free_weak::<&mut Vec<u8>>());
}
