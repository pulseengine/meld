//! Criterion benchmarks for the meld fusion pipeline.
//!
//! meld is on the hot path of every pulseengine toolchain build (fuse runs
//! before loom/kiln/synth), so a silent slowdown in the parser, merger, or
//! resolver translates directly into longer build times across the estate.
//!
//! These benchmarks exercise the four observable stages of the pipeline so
//! regressions are pinpoint-able rather than only visible at the end-to-end
//! level:
//!
//! 1. [`bench_parser`] — `ComponentParser::parse` on real wit-bindgen
//!    fixtures, with throughput reported per input byte.
//! 2. [`bench_merger`] — `Merger::merge` against pre-parsed components and
//!    a pre-built dependency graph, throughput per component count.
//! 3. [`bench_resolver`] — `Resolver::resolve_with_hints` against pre-parsed
//!    components, throughput per resolved-import (symbol) count.
//! 4. [`bench_end_to_end`] — `Fuser::fuse_with_stats` for small (1 fixture),
//!    medium (5 fixtures), and large (12 fixtures) component graphs.
//!
//! Run with:
//!     cargo bench -p meld-core
//! Or compile-only sanity (used in CI):
//!     cargo bench -p meld-core --no-run
//!
//! Fixtures live at `meld/tests/wit_bindgen/fixtures/`. If the fixture
//! directory is unavailable the bench gracefully skips groups instead of
//! panicking.

use std::path::Path;
use std::time::Duration;

use criterion::{BenchmarkId, Criterion, Throughput, black_box, criterion_group, criterion_main};
use meld_core::{
    ComponentParser, CustomSectionHandling, Fuser, FuserConfig, MemoryStrategy, OutputFormat,
    ParsedComponent, WiringHints, merger::Merger, resolver::Resolver,
};

const FIXTURES_DIR: &str = "../tests/wit_bindgen/fixtures";

/// Fixtures known to fuse cleanly; chosen to span small / medium / large
/// payload sizes without exceeding what is checked into the repo.
const FIXTURES: &[&str] = &[
    "numbers",
    "strings",
    "strings-simple",
    "lists",
    "lists-alias",
    "records",
    "variants",
    "options",
    "results",
    "many-arguments",
    "fixed-length-lists",
    "flavorful",
];

/// Read a fixture file, returning `None` if it is missing so callers can
/// skip rather than panic. The tracked corpus is small (~7-12 MB per file)
/// but absence is tolerated for partial checkouts.
fn read_fixture(name: &str) -> Option<Vec<u8>> {
    let path = format!("{FIXTURES_DIR}/{name}.wasm");
    if !Path::new(&path).is_file() {
        eprintln!("skipping {name}: fixture not found at {path}");
        return None;
    }
    std::fs::read(&path).ok()
}

/// Default fuser config for benches: deterministic, no attestation overhead,
/// drop custom sections so we measure pipeline cost (not section copy cost).
fn bench_config() -> FuserConfig {
    FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        attestation: false,
        address_rebasing: false,
        preserve_names: false,
        custom_sections: CustomSectionHandling::Drop,
        output_format: OutputFormat::CoreModule,
        opaque_resources: Vec::new(),
    }
}

/// Drive `Fuser::add_component_named` so we get the same flattened slice the
/// fusion pipeline uses internally, then surface `(components, wiring_hints)`
/// for the merger/resolver benches.
fn flatten_fixture(name: &str, bytes: &[u8]) -> Option<(Vec<ParsedComponent>, WiringHints)> {
    let mut fuser = Fuser::new(bench_config());
    fuser.add_component_named(bytes, Some(name)).ok()?;
    Some((fuser.components().to_vec(), fuser.wiring_hints().clone()))
}

// ---------------------------------------------------------------------------
// Group 1: Parser throughput (per input byte)
// ---------------------------------------------------------------------------

fn bench_parser(c: &mut Criterion) {
    let mut group = c.benchmark_group("parser");
    group.measurement_time(Duration::from_secs(5));

    for &name in FIXTURES {
        let Some(bytes) = read_fixture(name) else {
            continue;
        };
        group.throughput(Throughput::Bytes(bytes.len() as u64));
        group.bench_with_input(BenchmarkId::from_parameter(name), &bytes, |b, bytes| {
            b.iter(|| {
                let parser = ComponentParser::new();
                let parsed = parser.parse(black_box(bytes)).unwrap();
                black_box(parsed);
            });
        });
    }

    group.finish();
}

// ---------------------------------------------------------------------------
// Group 2: Merger throughput (per component count)
// ---------------------------------------------------------------------------

fn bench_merger(c: &mut Criterion) {
    let mut group = c.benchmark_group("merger");
    group.measurement_time(Duration::from_secs(5));

    for &name in FIXTURES {
        let Some(bytes) = read_fixture(name) else {
            continue;
        };
        let Some((components, hints)) = flatten_fixture(name, &bytes) else {
            continue;
        };

        // Pre-build the dependency graph once; we only want to measure
        // merge() cost in this group.
        let resolver = Resolver::with_strategy(MemoryStrategy::MultiMemory);
        let Ok(graph) = resolver.resolve_with_hints(&components, &hints) else {
            eprintln!("skipping {name}: resolver failed");
            continue;
        };

        group.throughput(Throughput::Elements(components.len() as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(name),
            &(components, graph),
            |b, (components, graph)| {
                b.iter(|| {
                    let merger = Merger::new(MemoryStrategy::MultiMemory, false);
                    let merged = merger
                        .merge(black_box(components), black_box(graph))
                        .unwrap();
                    black_box(merged);
                });
            },
        );
    }

    group.finish();
}

// ---------------------------------------------------------------------------
// Group 3: Resolver throughput (per resolved-symbol count)
// ---------------------------------------------------------------------------

fn bench_resolver(c: &mut Criterion) {
    let mut group = c.benchmark_group("resolver");
    group.measurement_time(Duration::from_secs(5));

    for &name in FIXTURES {
        let Some(bytes) = read_fixture(name) else {
            continue;
        };
        let Some((components, hints)) = flatten_fixture(name, &bytes) else {
            continue;
        };

        // Run once to learn the symbol (resolved-import) count for the
        // throughput axis. Resolution is deterministic so this is stable.
        let resolver = Resolver::with_strategy(MemoryStrategy::MultiMemory);
        let symbol_count = match resolver.resolve_with_hints(&components, &hints) {
            Ok(graph) => graph.resolved_imports.len().max(1) as u64,
            Err(_) => {
                eprintln!("skipping {name}: resolver failed during probe");
                continue;
            }
        };

        group.throughput(Throughput::Elements(symbol_count));
        group.bench_with_input(
            BenchmarkId::from_parameter(name),
            &(components, hints),
            |b, (components, hints)| {
                b.iter(|| {
                    let resolver = Resolver::with_strategy(MemoryStrategy::MultiMemory);
                    let graph = resolver
                        .resolve_with_hints(black_box(components), black_box(hints))
                        .unwrap();
                    black_box(graph);
                });
            },
        );
    }

    group.finish();
}

// ---------------------------------------------------------------------------
// Group 4: End-to-end fusion throughput
// ---------------------------------------------------------------------------

/// Build a `Fuser` populated with the requested fixtures. Each fixture is a
/// self-contained P2 component (host + guest); adding several into one fuser
/// exercises the parse/resolve/merge passes on a multi-fixture graph even
/// though the fixtures don't share imports.
fn build_fuser(names: &[&str]) -> Option<Fuser> {
    let mut fuser = Fuser::new(bench_config());
    for &name in names {
        let bytes = read_fixture(name)?;
        fuser.add_component_named(&bytes, Some(name)).ok()?;
    }
    Some(fuser)
}

fn bench_end_to_end(c: &mut Criterion) {
    let mut group = c.benchmark_group("end_to_end");
    // Full pipeline runs are slower; allow more time per iteration.
    group.measurement_time(Duration::from_secs(8));
    group.sample_size(20);

    // Small graph: one fixture (still flattens to several sub-components).
    let small: &[&str] = &["numbers"];
    // Medium graph: 5 fixtures.
    let medium: &[&str] = &["numbers", "strings", "lists", "records", "variants"];
    // Large graph: 12 fixtures (the whole curated corpus).
    let large: &[&str] = FIXTURES;

    for (label, fixtures) in [("small", small), ("medium", medium), ("large", large)] {
        let Some(fuser) = build_fuser(fixtures) else {
            eprintln!("skipping end_to_end/{label}: missing fixtures");
            continue;
        };
        let component_count = fuser.component_count() as u64;
        group.throughput(Throughput::Elements(component_count));
        group.bench_with_input(
            BenchmarkId::from_parameter(label),
            fixtures,
            |b, fixtures| {
                b.iter_batched(
                    || build_fuser(fixtures).expect("fixtures present"),
                    |fuser| {
                        let (bytes, stats) = fuser.fuse_with_stats().unwrap();
                        black_box((bytes, stats));
                    },
                    criterion::BatchSize::SmallInput,
                );
            },
        );
    }

    group.finish();
}

criterion_group!(
    fusion_benches,
    bench_parser,
    bench_merger,
    bench_resolver,
    bench_end_to_end,
);
criterion_main!(fusion_benches);
