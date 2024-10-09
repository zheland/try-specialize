#![allow(missing_docs, reason = "okay in tests")]
#![expect(unused_crate_dependencies, reason = "okay in tests")]
#![cfg(not(miri))]
#![cfg(any(target_arch = "x86", target_arch = "x86_64"))]

use try_specialize::TrySpecialize;

#[test]
fn test_lifetime_free_x86() {
    #[cfg(target_arch = "x86")]
    use core::arch::x86::*;
    #[cfg(target_arch = "x86_64")]
    use core::arch::x86_64::*;

    // SAFETY: Ignore too old processors without `cpuid` in tests.
    let cpuid_result = unsafe { __cpuid(0) };
    assert!(cpuid_result.try_specialize::<CpuidResult>().is_ok());
    assert!(cpuid_result.try_specialize::<u32>().is_err());
}
