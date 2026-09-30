//! meld#427 fixture — the provider half. Its interface carries a `resource`,
//! so the fused artifact exercises meld's per-resource handle tables rather
//! than scalars only.
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

wit_bindgen::generate!({ world: "provider", path: "wit", generate_all });

struct P;

/// Handle state lives in the PROVIDER's memory — the thing that must not become
/// reachable from the consumer's memory when the two share a fusion domain.
pub struct Task { entry: u32, ticks: u32 }

impl exports::gale::capfix::caps::GuestTask for Task {
    fn new(entry: u32) -> Self { Task { entry, ticks: 0 } }
    fn tick(&self, ticks: u32) -> u32 { self.entry.wrapping_add(ticks) }
    fn peek(&self) -> u32 { self.entry ^ 0x5EED_0000 }
}

impl exports::gale::capfix::caps::Guest for P {
    type Task = Task;
    fn now() -> u32 { 0x0000_1234 }
}

export!(P);
