//! Resolver termination fuzz target.
//!
//! Property: `Resolver::resolve(components)` must always terminate with
//! either `Ok(graph)` or `Err`, never panic, never loop indefinitely, and
//! never consume unbounded memory.
//!
//! libfuzzer enforces a default timeout (1200s by default; tunable via
//! `-timeout=N`). A resolver that fails to terminate on a pathological
//! import graph will be detected as a libfuzzer-side timeout — no manual
//! deadline plumbing needed.
//!
//! Specific cases this exercises:
//!   * Cyclic component-level imports (cycle detection MUST reject, not loop)
//!   * Self-referential imports
//!   * Deeply nested sub-component trees
//!   * Imports that name nonexistent exports
//!   * Components with zero modules and zero imports (degenerate case)
#![no_main]

use libfuzzer_sys::fuzz_target;
use meld_core::{ComponentParser, MemoryStrategy, Resolver};

fuzz_target!(|data: &[u8]| {
    // Single-component path: parse the bytes and feed the resolver one
    // component. The resolver still has to walk module-level imports and
    // resource graphs, both of which contain cycle-prone code paths.
    let parser = ComponentParser::without_validation();
    let parsed = match parser.parse(data) {
        Ok(p) => p,
        Err(_) => return,
    };

    // Strict resolver — fails on unresolved imports rather than logging
    // them. Drives more of the error-handling code than the lenient
    // default. We do not assert success: malformed-but-parseable input
    // is allowed to fail resolution. We only assert termination, which
    // libfuzzer enforces by timeout.
    let strict = Resolver::strict();
    let _ = strict.resolve(std::slice::from_ref(&parsed));

    // Lenient resolver to exercise the unresolved-import bookkeeping path.
    let lenient = Resolver::with_strategy(MemoryStrategy::MultiMemory);
    let _ = lenient.resolve(std::slice::from_ref(&parsed));

    // Multi-component path: feed two copies of the same parsed component.
    // This stresses cross-component import resolution, which is where
    // most cycle-prone code lives. Cloning the parsed component is cheap
    // and meaningful — duplicated exports must not crash the resolver.
    let pair = vec![parsed.clone(), parsed];
    let _ = lenient.resolve(&pair);
});
