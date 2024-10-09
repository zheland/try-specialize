#![allow(missing_docs, reason = "okay in tests")]
#![expect(unused_crate_dependencies, reason = "okay in tests")]
#![cfg(not(miri))]
#![cfg(not(debug_assertions))] // Requires `profile.opt-level >= 1`

use try_specialize::TrySpecialize;

mod common;

#[no_mangle]
#[inline(never)]
extern "Rust" fn take_option_u32_try_specialize_as_u32(value: Option<u32>) -> bool {
    value.try_specialize::<u32>().is_ok()
}

// Generates suboptimal, but valid bytecode for `Option`s.
// The `Option` tag (passed in %edi) can never be equal to 2, so it will never
// return 1.
#[rustversion::all(before(2024-08-13), before(1.82))]
const fn take_option_u32_try_specialize_as_u32_expected() -> &'static [u8] {
    &[
        0x83, 0xFF, 0x02, // cmpl $2, %edi
        0x0F, 0x94, 0xC0, // sete %al
        0xC3, // retq
    ]
}

// Improved in:
// - <https://github.com/rust-lang/rust/issues/50156>,
// - <https://github.com/rust-lang/rust/commit/e08b80c0fb7667bdcd040761891701e576c42ec8>.
#[rustversion::any(since(2024-08-13), since(1.82))]
const fn take_option_u32_try_specialize_as_u32_expected() -> &'static [u8] {
    &[
        0x31, 0xC0, // xorl %eax, %eax
        0xC3, // retq
    ]
}

#[test]
fn test_bytecode_changes() {
    for value in [None, Some(0), Some(1), Some(u32::MAX)] {
        assert!(!take_option_u32_try_specialize_as_u32(value));
    }

    let fns = [(
        common::fn_raw_ptr(take_option_u32_try_specialize_as_u32),
        take_option_u32_try_specialize_as_u32_expected(),
    )];

    for (fn_ptr, expected) in fns {
        for (offset, &expected) in expected.iter().enumerate() {
            // SAFETY: Locally defined extern functions should be readable.
            let byte = unsafe { fn_ptr.byte_add(offset).read() };
            assert_eq!(
                byte, expected,
                "at offset: {offset}, byte: {byte:#X}, expected: {expected:#X}"
            );
        }
    }
}
