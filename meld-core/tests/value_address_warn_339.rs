//! #339 Part 2 (SR-59) — loud-not-silent acceptance of a no-reloc value-address
//! module under `--memory shared --address-rebase`.
//!
//! The path-F gate hard-fails a non-zero-base, no-reloc module only when it does
//! a direct load/store. A module that uses an absolute address purely as a VALUE
//! (`i32.const <abs>; return` / passed to a call) has no load/store, so it is
//! ACCEPTED with an empty rebase plan — and its address const is emitted
//! un-rebased. A sound "is this const an address" detector is undecidable without
//! relocs (a broadened gate was built, reviewed, and REVERTED), so meld does not
//! reject; it must instead WARN loudly and name the remedy (`--emit-relocs`).
//!
//! This test pins the observability contract: the acceptance warning fires and
//! names the module, AND the output still validates (non-regression for the
//! accepted-no-reloc class, #298 / #304).

use std::sync::{Mutex, Once};

use meld_core::{Fuser, FuserConfig, MemoryStrategy};
use wasm_encoder::{
    CodeSection, Component, ExportKind, ExportSection, Function, FunctionSection, Instruction,
    MemorySection, MemoryType, Module, ModuleSection, TypeSection, ValType,
};

// ── minimal log capture (this test file is its own test binary, so it owns the
//    process-global logger here without contending with other test files) ──────

static CAPTURED: Mutex<Vec<String>> = Mutex::new(Vec::new());
static INIT: Once = Once::new();

static LOGGER: CaptureLogger = CaptureLogger;

struct CaptureLogger;

impl log::Log for CaptureLogger {
    fn enabled(&self, _: &log::Metadata<'_>) -> bool {
        true
    }
    fn log(&self, record: &log::Record<'_>) {
        if record.level() == log::Level::Warn {
            CAPTURED.lock().unwrap().push(format!("{}", record.args()));
        }
    }
    fn flush(&self) {}
}

fn install_capture() {
    INIT.call_once(|| {
        log::set_logger(&LOGGER).expect("install capture logger");
        log::set_max_level(log::LevelFilter::Warn);
    });
}

fn shared_memory_section() -> MemorySection {
    let mut memory = MemorySection::new();
    memory.memory(MemoryType {
        minimum: 1,
        maximum: Some(2),
        memory64: false,
        shared: true,
        page_size_log2: None,
    });
    memory
}

fn build_component(module: Module) -> Vec<u8> {
    let mut component = Component::new();
    component.section(&ModuleSection(&module));
    component.finish()
}

/// component-a: a 1-page shared memory occupying window `[0, 64KiB)`. No code, so
/// the value-address module below is placed at a non-zero base.
fn build_base_module() -> Module {
    let mut exports = ExportSection::new();
    exports.export("memory", ExportKind::Memory, 0);
    let mut module = Module::new();
    module.section(&shared_memory_section()).section(&exports);
    module
}

/// component-b: a shared memory + a function that RETURNS an absolute address
/// literal as a value (`i32.const 0x1234; end`). No load/store ⟹ path-F accepts
/// it; no reloc metadata ⟹ the const cannot be rebased. This is exactly the
/// accepted-but-un-rebased class the warning must announce.
fn build_value_address_module() -> Module {
    let mut types = TypeSection::new();
    types.ty().function([], [ValType::I32]);

    let mut functions = FunctionSection::new();
    functions.function(0);

    let mut exports = ExportSection::new();
    exports.export("get_addr", ExportKind::Func, 0);

    let mut code = CodeSection::new();
    let mut f = Function::new([]);
    f.instruction(&Instruction::I32Const(0x1234)); // absolute address used as a VALUE
    f.instruction(&Instruction::End);
    code.function(&f);

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&shared_memory_section())
        .section(&exports)
        .section(&code);
    module
}

#[test]
fn value_address_no_reloc_accept_warns_and_validates_339() {
    install_capture();
    CAPTURED.lock().unwrap().clear();

    let component_a = build_component(build_base_module());
    let component_b = build_component(build_value_address_module());

    let config = FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        address_rebasing: true,
        pack_rebase: false,
        share_stack: false,
        profile: meld_core::Profile::Ecosystem,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&component_a, Some("component-a"))
        .unwrap();
    fuser
        .add_component_named(&component_b, Some("value-addr-mod"))
        .unwrap();

    // Non-regression (#298/#304): the accepted-no-reloc class must still fuse and
    // the output must validate — the warning is observability, not a reject.
    let fused = fuser
        .fuse()
        .expect("a no-reloc value-address module must be ACCEPTED (warn, not fail)");
    assert!(
        wasmparser::Validator::new().validate_all(&fused).is_ok(),
        "fused output must still validate"
    );

    // The acceptance warning must fire, naming the module and the remedy.
    let warnings = CAPTURED.lock().unwrap().clone();
    let hit = warnings.iter().find(|w| w.contains("value-addr-mod"));
    let hit = hit.unwrap_or_else(|| {
        panic!("expected an acceptance warning naming the module; captured: {warnings:?}")
    });
    assert!(
        hit.contains("UN-REBASED") && hit.contains("--emit-relocs"),
        "warning must name the risk (un-rebased value) and the remedy \
         (--emit-relocs); got: {hit}"
    );
}
