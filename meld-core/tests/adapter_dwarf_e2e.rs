//! End-to-end oracle for #144 inc 3: a fusion that GENERATES code gets a
//! synthetic `<meld-adapter>` DWARF unit in the fused output under
//! `DwarfHandling::Remap` — even when no input carries DWARF at all, so
//! adapter attribution never depends on the inputs being debug builds.
//!
//! The deterministic generated-code trigger: two components whose modules
//! each declare a `start` function. The merger must synthesise a start
//! wrapper (origin sentinel `(usize::MAX, usize::MAX, 0)`) that calls
//! both — meld-generated code with no original source. The fused output's
//! `.debug_line` must attribute that wrapper's body to `<meld-adapter>:1`,
//! and the attributed range must be a real function body in the output.

use meld_core::{DwarfHandling, Fuser, FuserConfig, MemoryStrategy};
use wasm_encoder::{
    CodeSection, Component, ExportKind, ExportSection, Function, FunctionSection, GlobalSection,
    GlobalType, Instruction, Module, ModuleSection, StartSection, TypeSection, ValType,
};
use wasmtime::{Engine, Instance, Module as RuntimeModule, Store};

/// One module: a mutable global, a `start` function setting it to `marker`,
/// and an exported getter so the runtime check can observe that start ran.
fn build_module_with_start(getter_name: &str, marker: i32) -> Module {
    let mut types = TypeSection::new();
    types.ty().function([], []); // type 0: start
    types.ty().function([], [ValType::I32]); // type 1: getter

    let mut functions = FunctionSection::new();
    functions.function(0); // func 0: start
    functions.function(1); // func 1: getter

    let mut globals = GlobalSection::new();
    globals.global(
        GlobalType {
            val_type: ValType::I32,
            mutable: true,
            shared: false,
        },
        &wasm_encoder::ConstExpr::i32_const(0),
    );

    let mut exports = ExportSection::new();
    exports.export(getter_name, ExportKind::Func, 1);

    let mut code = CodeSection::new();
    let mut start = Function::new([]);
    start.instruction(&Instruction::I32Const(marker));
    start.instruction(&Instruction::GlobalSet(0));
    start.instruction(&Instruction::End);
    code.function(&start);
    let mut getter = Function::new([]);
    getter.instruction(&Instruction::GlobalGet(0));
    getter.instruction(&Instruction::End);
    code.function(&getter);

    let mut module = Module::new();
    module
        .section(&types)
        .section(&functions)
        .section(&globals)
        .section(&exports)
        .section(&StartSection { function_index: 0 })
        .section(&code);
    module
}

fn component(module: Module) -> Vec<u8> {
    let mut c = Component::new();
    c.section(&ModuleSection(&module));
    c.finish()
}

fn fuse_remap() -> Vec<u8> {
    let a = component(build_module_with_start("get_a", 11));
    let b = component(build_module_with_start("get_b", 22));
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        dwarf_handling: DwarfHandling::Remap,
        attestation: false,
        ..Default::default()
    });
    fuser.add_component_named(&a, Some("a")).unwrap();
    fuser.add_component_named(&b, Some("b")).unwrap();
    fuser.fuse().unwrap()
}

/// `(body_start, body_end)` code-section-relative ranges of every defined
/// function, independently derived with wasmparser.
fn function_body_ranges(wasm: &[u8]) -> Vec<(u64, u64)> {
    let mut code_section_start = None;
    let mut ranges = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(wasm) {
        match payload.unwrap() {
            wasmparser::Payload::CodeSectionStart { range, .. } => {
                code_section_start = Some(range.start as u64);
            }
            wasmparser::Payload::CodeSectionEntry(body) => {
                let base = code_section_start.expect("code section started");
                let r = body.range();
                ranges.push((r.start as u64 - base, r.end as u64 - base));
            }
            _ => {}
        }
    }
    ranges
}

/// All non-end-sequence `.debug_line` rows as `(address, file, line)`.
fn debug_line_rows(wasm: &[u8]) -> Vec<(u64, String, u64)> {
    use gimli::{EndianSlice, LittleEndian};

    let mut sections: Vec<(String, Vec<u8>)> = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(wasm) {
        if let wasmparser::Payload::CustomSection(r) = payload.unwrap()
            && r.name().starts_with(".debug_")
        {
            sections.push((r.name().to_string(), r.data().to_vec()));
        }
    }
    let section_data = |name: &str| -> &[u8] {
        sections
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, d)| d.as_slice())
            .unwrap_or(&[])
    };
    let load = |id: gimli::SectionId| -> Result<EndianSlice<'_, LittleEndian>, gimli::Error> {
        Ok(EndianSlice::new(section_data(id.name()), LittleEndian))
    };
    let dwarf = gimli::Dwarf::load(load).expect("load output dwarf");

    let mut rows_out = Vec::new();
    let mut units = dwarf.units();
    while let Some(header) = units.next().expect("units") {
        let unit = dwarf.unit(header).expect("unit");
        let Some(program) = unit.line_program.clone() else {
            continue;
        };
        let mut rows = program.rows();
        while let Some((hdr, row)) = rows.next_row().expect("row") {
            if row.end_sequence() {
                continue;
            }
            let fname = row
                .file(hdr)
                .map(|f| match f.path_name() {
                    gimli::AttributeValue::String(s) => {
                        String::from_utf8_lossy(s.slice()).into_owned()
                    }
                    _ => String::new(),
                })
                .unwrap_or_default();
            rows_out.push((row.address(), fname, row.line().map_or(0, |l| l.get())));
        }
    }
    rows_out
}

/// The pipeline contract: dwarf-less inputs whose fusion generates code
/// produce a fused output whose `.debug_line` attributes the generated
/// range to `<meld-adapter>:<class-line>`, at an address that is a real
/// function body start (independently derived). Since #144 inc 4 the
/// line encodes the adapter CLASS — the only generated function in this
/// fixture is the merger's multi-`start` wrapper, so every adapter row
/// must carry [`AdapterRole::StartWrapper`]'s line. (`ls_d_2_` prefix:
/// LS-D-2 regression, run by the LS-N verification gate.)
#[test]
fn ls_d_2_generated_start_wrapper_is_attributed_to_meld_adapter() {
    let fused = fuse_remap();

    let rows = debug_line_rows(&fused);
    let adapter_rows: Vec<&(u64, String, u64)> = rows
        .iter()
        .filter(|(_, f, _)| f == "<meld-adapter>")
        .collect();
    assert!(
        !adapter_rows.is_empty(),
        "fusion generated a start wrapper; output .debug_line must carry \
         <meld-adapter> attribution (rows: {rows:?})"
    );
    let start_wrapper_line = u64::from(meld_core::dwarf::AdapterRole::StartWrapper.adapter_line());
    assert!(start_wrapper_line > 0, "line 0 means 'no line' in DWARF");
    for (_, _, line) in &adapter_rows {
        assert_eq!(
            *line, start_wrapper_line,
            "the start wrapper must attribute to its CLASS line (#144 inc 4)"
        );
    }

    let ranges = function_body_ranges(&fused);
    for (addr, _, _) in &adapter_rows {
        assert!(
            ranges.iter().any(|(s, e)| addr >= s && addr < e),
            "adapter row address {addr:#x} must fall inside a real \
             function body; ranges = {ranges:?}"
        );
    }

    // No source DWARF existed, so NOTHING may be attributed to anything
    // other than the synthetic file.
    assert!(
        rows.iter().all(|(_, f, _)| f == "<meld-adapter>"),
        "dwarf-less inputs must yield only synthetic attribution"
    );
}

/// Behaviour guard: the synthetic DWARF emission must not perturb the
/// fused module — both start functions still run via the generated
/// wrapper.
#[test]
fn fused_module_with_synthetic_dwarf_still_runs() {
    let fused = fuse_remap();

    let engine = Engine::default();
    let module = RuntimeModule::new(&engine, &fused).unwrap();
    let mut store = Store::new(&engine, ());
    let instance = Instance::new(&mut store, &module, &[]).unwrap();

    let get_a = instance
        .get_typed_func::<(), i32>(&mut store, "get_a")
        .unwrap();
    let get_b = instance
        .get_typed_func::<(), i32>(&mut store, "get_b")
        .unwrap();
    assert_eq!(get_a.call(&mut store, ()).unwrap(), 11, "a's start ran");
    assert_eq!(get_b.call(&mut store, ()).unwrap(), 22, "b's start ran");
}
