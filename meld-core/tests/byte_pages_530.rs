//! SR-107 (#530) — declare each packed memory at its byte extent with
//! `(pagesize 1)` instead of rounding it up to whole 64 KiB pages.
//!
//! gale's two-domain image needs about 7.4 KiB; declared in pages it needs at
//! least 128 KiB, which no part gale targets can provide. `--pack-rebase`
//! already computes the byte extent; this requirement makes the module DECLARE
//! it, so a downstream tool (synth v0.89) need not re-derive it.
//!
//! The fixture is the three-component `domains_427` set (two tenants and a
//! provider), grouped `{consumer, provider}` + `{consumer2}` so the output has
//! two memories and a per-domain total to check.

use meld_core::{Fuser, FuserConfig, FusionStats, MemoryPageSize, MemoryStrategy};

const FIXTURES: &str = "../tests/wit_bindgen/fixtures/domains_427";

/// Component indices as added by `load`.
const CONSUMER: usize = 0;
const CONSUMER2: usize = 1;
const PROVIDER: usize = 2;

fn fixture(name: &str) -> Vec<u8> {
    let path = format!("{FIXTURES}/{name}.comp.wasm");
    std::fs::read(&path).unwrap_or_else(|e| {
        panic!("fixture not readable at {path} ({e}) — fixtures are tracked (SR-85)")
    })
}

fn config(pack: bool, page: MemoryPageSize) -> FuserConfig {
    FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        address_rebasing: true,
        pack_rebase: pack,
        domains: vec![vec![CONSUMER, PROVIDER], vec![CONSUMER2]],
        memory_page_size: page,
        // Two fuses of one input must be comparable byte for byte.
        reproducible: true,
        attestation: false,
        ..Default::default()
    }
}

fn fuse(pack: bool, page: MemoryPageSize) -> Result<(Vec<u8>, FusionStats), meld_core::Error> {
    let mut fuser = Fuser::new(config(pack, page));
    for name in ["consumer", "consumer2", "provider"] {
        fuser
            .add_component_named(&fixture(name), Some(name))
            .expect("component accepted");
    }
    fuser.fuse_with_stats()
}

/// `(initial, maximum, page_size_log2)` of every DEFINED memory.
fn memories(bytes: &[u8]) -> Vec<(u64, Option<u64>, Option<u32>)> {
    let mut out = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let wasmparser::Payload::MemorySection(reader) = payload.expect("payload") {
            for m in reader {
                let m = m.expect("memory");
                out.push((m.initial, m.maximum, m.page_size_log2));
            }
        }
    }
    out
}

/// Highest end of any active data segment, per memory index.
fn max_data_end(bytes: &[u8], mem: u32) -> u64 {
    let mut end = 0u64;
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let wasmparser::Payload::DataSection(reader) = payload.expect("payload") {
            for d in reader {
                let d = d.expect("data");
                if let wasmparser::DataKind::Active {
                    memory_index,
                    offset_expr,
                } = d.kind
                    && memory_index == mem
                {
                    let mut ops = offset_expr.get_operators_reader();
                    if let wasmparser::Operator::I32Const { value } = ops.read().expect("op") {
                        end = end.max(value as u32 as u64 + d.data.len() as u64);
                    }
                }
            }
        }
    }
    end
}

/// The packed total of one domain, DERIVED from the placements the planner
/// reported (never hardcoded): the sum of the strides of its members.
fn domain_total(stats: &FusionStats, members: &[usize]) -> u64 {
    stats
        .placements
        .iter()
        .filter(|p| members.contains(&p.component))
        .map(|p| p.reserved)
        .sum()
}

// rivet: verifies SWV-119
#[test]
fn each_domain_memory_is_declared_at_its_packed_byte_extent() {
    let (bytes, stats) = fuse(true, MemoryPageSize::Byte).expect("byte-paged fusion succeeds");
    let mems = memories(&bytes);
    assert_eq!(mems.len(), 2, "one memory per domain");

    let totals = [
        domain_total(&stats, &[CONSUMER, PROVIDER]),
        domain_total(&stats, &[CONSUMER2]),
    ];
    for (i, &(initial, maximum, log2)) in mems.iter().enumerate() {
        assert_eq!(log2, Some(0), "memory {i} must declare (pagesize 1)");
        assert_eq!(
            Some(initial),
            maximum,
            "memory {i}: byte-paged memories are fixed-size (min == max)"
        );
        assert!(totals[i] > 0, "guard: the placements must be non-empty");
        assert_eq!(
            initial, totals[i],
            "memory {i}: declared bytes must equal the sum of its placements' strides"
        );
        assert!(
            initial >= max_data_end(&bytes, i as u32),
            "memory {i}: every data segment must fit the byte extent"
        );
        // The pre-flag value rounded this up to pages; the byte value is
        // strictly the tighter of the two for a non-page-multiple total.
        assert_eq!(initial % 16, 0, "extent keeps the 16-byte pack alignment");
    }

    // --explain's source: the stats report the byte-sized memory.
    assert_eq!(stats.memories.len(), 2);
    assert!(stats.memories.iter().all(|m| m.page_size == 1));
}

// rivet: verifies SWV-119
#[test]
fn without_the_flag_memories_are_page_sized_as_before() {
    let (bytes, _) = fuse(true, MemoryPageSize::Page).expect("fusion succeeds");
    for (i, &(initial, _max, log2)) in memories(&bytes).iter().enumerate() {
        assert_eq!(
            log2, None,
            "memory {i}: default output declares no pagesize"
        );
        assert!(initial >= 1);
    }
    // The default config value is `Page`: not passing the flag is the same as
    // passing 65536, byte for byte.
    let mut a = Fuser::new(FuserConfig {
        memory_page_size: MemoryPageSize::default(),
        ..config(true, MemoryPageSize::Page)
    });
    let mut b = Fuser::new(config(true, MemoryPageSize::Page));
    for name in ["consumer", "consumer2", "provider"] {
        a.add_component_named(&fixture(name), Some(name)).unwrap();
        b.add_component_named(&fixture(name), Some(name)).unwrap();
    }
    assert_eq!(a.fuse().unwrap(), b.fuse().unwrap());
}

/// The byte-paged memory must be a pure re-declaration: every exported call
/// returns what it returns with page-sized memories. Runs both under wasmtime
/// (custom-page-sizes enabled for the byte-paged one only).
// rivet: verifies SWV-119
#[test]
fn byte_paged_output_runs_identically_under_wasmtime() {
    use wasmtime::{Config, Engine, Linker, Module, Store, Val};

    /// Every function export called with zero arguments, in export order: the
    /// results (or the trap kind -- a trap's message carries code offsets that
    /// legitimately differ between the two layouts), and the final image of the
    /// exported memory 0.
    type Run = (Vec<(String, Result<Vec<i64>, String>)>, Vec<u8>);

    fn run(bytes: &[u8], custom_page_sizes: bool) -> Run {
        let mut cfg = Config::new();
        cfg.wasm_custom_page_sizes(custom_page_sizes);
        // Fuel bounds every call: a runaway export traps instead of hanging.
        cfg.consume_fuel(true);
        let engine = Engine::new(&cfg).unwrap();
        let module = Module::new(&engine, bytes).expect("module loads");
        let mut store = Store::new(&engine, ());
        store.set_fuel(100_000_000).unwrap();
        let mut linker = Linker::new(&engine);
        linker
            .define_unknown_imports_as_default_values(&mut store, &module)
            .unwrap();
        let instance = linker
            .instantiate(&mut store, &module)
            .expect("instantiates");
        let names: Vec<String> = module
            .exports()
            .filter(|e| e.ty().func().is_some())
            .map(|e| e.name().to_string())
            .collect();
        let mut results = Vec::new();
        for name in names {
            let f = instance.get_func(&mut store, &name).expect("export");
            let ty = f.ty(&store);
            let params: Vec<Val> = ty.params().map(|_| Val::I32(0)).collect();
            let mut out: Vec<Val> = ty.results().map(|_| Val::I32(0)).collect();
            store.set_fuel(2_000_000).unwrap();
            let r = f
                .call(&mut store, &params, &mut out)
                .map(|()| {
                    out.iter()
                        .map(|v| match v {
                            Val::I32(x) => i64::from(*x),
                            Val::I64(x) => *x,
                            other => panic!("unexpected result {other:?}"),
                        })
                        .collect::<Vec<_>>()
                })
                .map_err(|e| format!("{:?}", e.downcast_ref::<wasmtime::Trap>()));
            results.push((name, r));
        }
        let mem = instance
            .get_memory(&mut store, "memory")
            .expect("memory export")
            .data(&store)
            .to_vec();
        (results, mem)
    }

    let (paged, _) = fuse(true, MemoryPageSize::Page).unwrap();
    let (bytes, _) = fuse(true, MemoryPageSize::Byte).unwrap();

    // Negative control for the harness: a default wasmtime refuses the byte-paged
    // module, so the custom-page-sizes switch below is load-bearing, not decor.
    {
        let engine = Engine::new(&Config::new()).unwrap();
        assert!(
            Module::new(&engine, &bytes).is_err(),
            "a wasmtime without custom-page-sizes must reject (pagesize 1)"
        );
    }

    let (expected, paged_mem) = run(&paged, false);
    let (actual, byte_mem) = run(&bytes, true);
    assert_eq!(
        expected, actual,
        "byte-paged output must behave identically"
    );
    // The fixture's own entry points (`run`, `run2`, the constructor and the
    // methods) need a host and trap identically in every strategy, `--memory
    // multi` included, so they only compare trap to trap here. What does
    // complete is `now` (a real call into the provider's memory: 0x1234), the
    // deallocator and the allocators, and the memory image below carries the
    // rest. The cross-domain copy that DOES complete is in
    // `byte_pages_guard_530.rs`.
    assert!(
        expected
            .iter()
            .any(|(n, r)| n.ends_with("#now") && *r == Ok(vec![0x1234])),
        "guard: `now` must complete with 0x1234, or the comparison is vacuous: {expected:?}"
    );
    // The byte-sized memory is exactly its declared extent, and after running
    // every export it holds the same bytes as the page-sized one over that range.
    assert_eq!(byte_mem.len() as u64, memories(&bytes)[0].0);
    assert!(paged_mem.len() >= byte_mem.len());
    assert!(
        paged_mem[..byte_mem.len()] == byte_mem[..],
        "memory image over the declared extent must match"
    );
    assert!(
        byte_mem.iter().any(|&b| b != 0),
        "guard: the image must not be all zeros"
    );
}

// rivet: verifies SWV-119
#[test]
fn byte_pages_are_refused_without_pack_rebase() {
    let err = fuse(false, MemoryPageSize::Byte).unwrap_err().to_string();
    assert!(err.contains("requires --pack-rebase"), "{err}");
}

// rivet: verifies SWV-119
#[test]
fn byte_pages_are_refused_with_the_component_wrapper() {
    let mut cfg = config(true, MemoryPageSize::Byte);
    cfg.output_format = meld_core::OutputFormat::Component;
    let mut fuser = Fuser::new(cfg);
    for name in ["consumer", "consumer2", "provider"] {
        fuser
            .add_component_named(&fixture(name), Some(name))
            .unwrap();
    }
    let err = fuser.fuse().unwrap_err().to_string();
    assert!(err.contains("--component"), "{err}");
}

/// The page size is a parameter of the artifact, so it is attested whenever it
/// is not the default, in EVERY build configuration -- and absent otherwise
/// (default records byte-identical). The record's layout differs between the
/// shipped build and `--features attestation`, so this searches the emitted
/// bytes for the compact JSON, as the #463 test does.
// rivet: verifies SWV-119
#[test]
fn the_page_size_is_attested_only_when_not_the_default() {
    fn attested(page: MemoryPageSize) -> (bool, bool) {
        let mut cfg = config(true, page);
        cfg.attestation = true;
        let mut fuser = Fuser::new(cfg);
        for name in ["consumer", "consumer2", "provider"] {
            fuser
                .add_component_named(&fixture(name), Some(name))
                .unwrap();
        }
        let bytes = fuser.fuse().unwrap();
        let has = |needle: &[u8]| bytes.windows(needle.len()).any(|w| w == needle);
        // Control: the record exists at all (it names a parameter that is
        // always recorded).
        (
            has(br#""memory_strategy":"shared""#),
            has(br#""memory_page_size":1"#),
        )
    }
    let (record_byte, byte) = attested(MemoryPageSize::Byte);
    assert!(record_byte, "control: the attestation record is present");
    assert!(byte, "byte pages must be recorded");
    let (record_page, page) = attested(MemoryPageSize::Page);
    assert!(record_page, "control: the attestation record is present");
    assert!(!page, "the default is not recorded");
}
