//! meld#427 fixture — the tenant half. Obtains a handle from the provider and
//! uses it, so the boundary carries own<task> + borrow<task> + a scalar call.
#![no_std]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }

use core::alloc::{GlobalAlloc, Layout};
struct NoAlloc;
unsafe impl GlobalAlloc for NoAlloc {
    unsafe fn alloc(&self, _: Layout) -> *mut u8 { core::ptr::null_mut() }
    unsafe fn dealloc(&self, _: *mut u8, _: Layout) {}
}
#[global_allocator]
static ALLOC: NoAlloc = NoAlloc;

wit_bindgen::generate!({ world: "consumer2", path: "wit", generate_all });

struct C;

impl Guest for C {
    fn run2() -> u32 {
        let t = gale::capfix::caps::Task::new(7);
        let a = t.tick(5);          // method on an owned handle
        let b = t.peek();           // borrow
        let n = gale::capfix::caps::now();  // scalar op on the same boundary
        a ^ b ^ n
    }
}

export!(C);
