#![no_std]
#![no_main]
#![allow(
    dead_code,
    missing_docs,
    clippy::empty_loop,
    clippy::missing_panics_doc,
    clippy::panic,
    clippy::undocumented_unsafe_blocks,
    clippy::unimplemented,
    reason = "okay in tests"
)]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "global-allocator")]
use core::alloc::{GlobalAlloc, Layout};
#[cfg(feature = "panic-handler")]
use core::panic::PanicInfo;

#[cfg(feature = "global-allocator")]
struct DummyAllocator;

#[cfg(feature = "global-allocator")]
#[global_allocator]
static GLOBAL_ALLOCATOR: DummyAllocator = DummyAllocator;

#[cfg(feature = "panic-handler")]
#[panic_handler]
const fn panic(_: &PanicInfo<'_>) -> ! {
    loop {}
}

#[no_mangle]
pub const extern "C" fn _start() -> ! {
    loop {}
}

#[cfg(feature = "global-allocator")]
unsafe impl GlobalAlloc for DummyAllocator {
    unsafe fn alloc(&self, _layout: Layout) -> *mut u8 {
        unimplemented!()
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {
        unimplemented!()
    }
}

#[no_mangle]
pub extern "C" fn test_core() {
    use try_specialize::TrySpecialize;

    assert_eq!(42_u32.try_specialize::<u32>(), Ok(42));
    assert_eq!(42_i32.try_specialize::<u32>(), Err(42));
    assert_eq!("abc".try_specialize::<u32>(), Err("abc"));
}

#[cfg(feature = "alloc")]
#[no_mangle]
pub extern "C" fn test_alloc() {
    use alloc::string::String;

    use try_specialize::TrySpecialize;

    assert_eq!(42_u32.try_specialize::<u32>(), Err(42));
    assert_eq!(42_i32.try_specialize::<u32>(), Err(42));
    assert_eq!("abc".try_specialize::<u32>(), Err("abc"));
    assert_eq!(
        String::from("abc").try_specialize::<String>(),
        Ok(String::from("abc"))
    );
}

#[cfg(feature = "std")]
#[no_mangle]
pub extern "C" fn test_std() {
    use alloc::string::String;
    use std::path::PathBuf;

    use try_specialize::TrySpecialize;

    assert_eq!(42_u32.try_specialize::<u32>(), Err(42));
    assert_eq!(42_i32.try_specialize::<u32>(), Err(42));
    assert_eq!("abc".try_specialize::<u32>(), Err("abc"));
    assert_eq!(
        String::from("abc").try_specialize::<String>(),
        Err(String::from("abc"))
    );
    assert_eq!(
        PathBuf::from("abc").try_specialize::<PathBuf>(),
        Ok(PathBuf::from("abc"))
    );
}
