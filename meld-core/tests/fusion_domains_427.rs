//! SR-86 (#427) — fusing within a domain, keeping the Canonical ABI between.
//!
//! `fuse` took one global `--memory`, so fusion was all-or-nothing: every
//! component in one memory, or every component in its own. gale/fathom needs a
//! third shape for an MCU privilege boundary (gale#408) — tenants fused with
//! each other for size, and the copy kept between a tenant and its supervisor,
//! because the copy meld elides under shared memory *is* the boundary.
//!
//! The fixture is three components: two tenants (`consumer`, `consumer2`)
//! calling one `provider` across an interface carrying `own<task>`,
//! `borrow<task>` and a scalar. Two callers of one provider is the point — the
//! only difference between the two call sites is which domain they land in, so
//! an identical call's lowering becomes a function of the grouping alone.
//!
//! Measured on 0.58.3 before this requirement:
//!
//! | invocation | boundaries | memories |
//! |---|---|---|
//! | `--memory multi` | 8 memory-copy | 3 (isolated, unfittable) |
//! | `--memory shared --address-rebase` | 8 direct | 1 (fits, unisolated) |
//! | **with domains** | **4 direct + 4 memory-copy** | **2** |

use meld_core::{Fuser, FuserConfig, MemoryStrategy};

const FIXTURES: &str = "../tests/wit_bindgen/fixtures/domains_427";

/// Component indices as added below.
const CONSUMER: usize = 0;
const CONSUMER2: usize = 1;
const PROVIDER: usize = 2;

fn fixture(name: &str) -> Vec<u8> {
    let path = format!("{FIXTURES}/{name}.comp.wasm");
    std::fs::read(&path).unwrap_or_else(|e| {
        panic!(
            "fixture not readable at {path} ({e}) — every fixture a test reads is tracked in the \
             repository (SR-85); a missing one is a repository error, not a reason to report success"
        )
    })
}

fn config(domains: Vec<Vec<usize>>) -> FuserConfig {
    FuserConfig {
        memory_strategy: MemoryStrategy::SharedMemory,
        address_rebasing: true,
        domains,
        ..Default::default()
    }
}

fn load(fuser: &mut Fuser) {
    for name in ["consumer", "consumer2", "provider"] {
        fuser
            .add_component_named(&fixture(name), Some(name))
            .expect("component accepted");
    }
}

fn fuse(domains: Vec<Vec<usize>>) -> meld_core::FusionStats {
    let mut fuser = Fuser::new(config(domains));
    load(&mut fuser);
    fuser.fuse_with_stats().expect("fusion succeeds").1
}

/// The requirement, stated as the thing that must be observable: two identical
/// calls, differing only in grouping, must lower differently.
// rivet: verifies SR-86
#[test]
fn grouping_decides_the_lowering_of_an_identical_call() {
    // consumer shares a domain with provider; consumer2 does not.
    let stats = fuse(vec![vec![CONSUMER, PROVIDER], vec![CONSUMER2]]);

    let intra: Vec<_> = stats
        .boundaries
        .iter()
        .filter(|b| b.from_component == CONSUMER && b.to_component == PROVIDER)
        .collect();
    let cross: Vec<_> = stats
        .boundaries
        .iter()
        .filter(|b| b.from_component == CONSUMER2 && b.to_component == PROVIDER)
        .collect();

    assert_eq!(
        intra.len(),
        4,
        "guard: the fixture's interface carries four boundaries per tenant — \
         own<task>, borrow<task>, the constructor and a scalar"
    );
    assert_eq!(
        cross.len(),
        4,
        "guard: the second tenant calls the same four"
    );

    for b in &intra {
        assert_eq!(
            b.lowering, "direct",
            "SR-86: {} is inside a domain and must fuse — a copy here is the \
             isolation meld was not asked for",
            b.function
        );
        assert!(
            !b.crosses_memory,
            "SR-86: {} is inside a domain and must not cross a memory",
            b.function
        );
    }
    for b in &cross {
        assert_eq!(
            b.lowering, "memory-copy",
            "SR-86: {} crosses a domain boundary and must keep the Canonical ABI — \
             the elided copy IS the privilege boundary (gale#408)",
            b.function
        );
        assert!(
            b.crosses_memory,
            "SR-86: {} crosses a domain boundary and must cross a memory",
            b.function
        );
    }
}

/// A grouping is a trust decision, so it must be visible in the record rather
/// than inferable only from which lowering happened to be chosen.
// rivet: verifies SR-86
#[test]
fn each_boundary_states_the_domains_it_runs_between() {
    let stats = fuse(vec![vec![CONSUMER, PROVIDER], vec![CONSUMER2]]);

    for b in &stats.boundaries {
        let same_domain = b.from_domain == b.to_domain;
        assert_eq!(
            same_domain, !b.crosses_memory,
            "SR-86: boundary {} reports domains {} -> {} but crosses_memory={}; the record \
             and the lowering must not disagree about whether this call left its domain",
            b.function, b.from_domain, b.to_domain, b.crosses_memory
        );
    }
    assert!(
        stats
            .boundaries
            .iter()
            .any(|b| b.from_domain != b.to_domain),
        "guard: this grouping has a cross-domain call, so at least one boundary must say so"
    );
}

/// Without a grouping the LAYOUT is exactly today's. This is what makes the
/// feature safe to land: a user who does not ask for domains cannot be given
/// different bytes.
///
/// Compared with the attestation off, because the record legitimately differs
/// — see the next test. The layout claim and the record claim are separate,
/// and conflating them would let a real layout change hide behind "well, the
/// attestation changed too".
// rivet: verifies SR-86
#[test]
fn absent_a_grouping_the_layout_is_unchanged() {
    let build = |domains: Vec<Vec<usize>>| {
        let mut fuser = Fuser::new(FuserConfig {
            attestation: false,
            ..config(domains)
        });
        load(&mut fuser);
        fuser.fuse().expect("fusion succeeds")
    };

    // One domain holding every input is the same LAYOUT as "no domains".
    assert_eq!(
        build(vec![]),
        build(vec![vec![CONSUMER, CONSUMER2, PROVIDER]]),
        "SR-86: an explicit single domain covering every input must lay memory out exactly as \
         no grouping does — otherwise the feature changes bytes for users who did not ask for it"
    );
}

/// ...and the record does not pretend they were the same statement. Under
/// ADR-4 ("explicit, not auto") a caller who *stated* the grouping said
/// something a caller who stayed silent did not, and the attestation is where
/// that difference has to survive.
// rivet: verifies SR-86
#[test]
fn stating_the_grouping_is_recorded_even_when_it_changes_nothing() {
    let build = |domains: Vec<Vec<usize>>| {
        let mut fuser = Fuser::new(config(domains));
        load(&mut fuser);
        fuser.fuse().expect("fusion succeeds")
    };

    assert_ne!(
        build(vec![]),
        build(vec![vec![CONSUMER, CONSUMER2, PROVIDER]]),
        "SR-86: the attestation must distinguish a grouping the caller stated from one meld \
         assumed, even when both describe the same layout — a privilege boundary that was \
         declared is different evidence from one that was defaulted into"
    );
}

/// `Default` is not a licence to guess: a component named in no domain, or in
/// two, is a grouping the user did not mean, and the trust boundary is exactly
/// the thing not to infer.
// rivet: verifies SR-86
#[test]
fn a_grouping_that_does_not_partition_the_inputs_is_refused() {
    let build = |domains: Vec<Vec<usize>>| {
        let mut fuser = Fuser::new(config(domains));
        load(&mut fuser);
        fuser.fuse()
    };

    assert!(
        build(vec![vec![CONSUMER, PROVIDER]]).is_err(),
        "SR-86: consumer2 is in no domain — meld must refuse rather than place it somewhere"
    );
    assert!(
        build(vec![vec![CONSUMER, PROVIDER], vec![CONSUMER, CONSUMER2]]).is_err(),
        "SR-86: consumer is in two domains — meld must refuse rather than pick one"
    );
    assert!(
        build(vec![vec![CONSUMER, PROVIDER], vec![CONSUMER2, 99]]).is_err(),
        "SR-86: component 99 does not exist — a typo in a trust boundary must be loud"
    );
}

/// Domains are a memory-axis grouping, so they only mean something where the
/// memory axis is in play. Accepting them under `multi` would imply the
/// grouping did something when every component already has its own memory.
// rivet: verifies SR-86
#[test]
fn domains_under_multi_memory_are_refused_rather_than_ignored() {
    let mut fuser = Fuser::new(FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        domains: vec![vec![CONSUMER, PROVIDER], vec![CONSUMER2]],
        ..Default::default()
    });
    load(&mut fuser);
    assert!(
        fuser.fuse().is_err(),
        "SR-86: under --memory multi every component already has its own memory, so a grouping \
         would silently do nothing — refuse it instead of accepting a no-op trust decision"
    );
}

/// Count the linear memories the fused core module declares.
fn memory_count(bytes: &[u8]) -> usize {
    use wasmparser::{Parser, Payload};
    let mut n = 0;
    for payload in Parser::new(0).parse_all(bytes) {
        if let Ok(Payload::MemorySection(reader)) = payload {
            n += reader.count() as usize;
        }
    }
    n
}

/// The fit half of #427: a grouping must produce one memory per domain, not
/// one for everything (which erases the boundary) and not one per component
/// (which is what `--memory multi` already does).
// rivet: verifies SR-86
#[test]
fn a_grouping_produces_one_memory_per_domain() {
    let build = |domains: Vec<Vec<usize>>| {
        let mut fuser = Fuser::new(FuserConfig {
            attestation: false,
            ..config(domains)
        });
        load(&mut fuser);
        fuser.fuse().expect("fusion succeeds")
    };

    assert_eq!(
        memory_count(&build(vec![])),
        1,
        "guard: with no grouping, shared memory means exactly one memory"
    );
    assert_eq!(
        memory_count(&build(vec![vec![CONSUMER, PROVIDER], vec![CONSUMER2]])),
        2,
        "SR-86: two domains must land in two memories — one memory would mean the tenants \
         can address each other after all, and three would mean the grouping did nothing that \
         --memory multi does not already do"
    );
    assert_eq!(
        memory_count(&build(vec![
            vec![CONSUMER],
            vec![CONSUMER2],
            vec![PROVIDER]
        ])),
        3,
        "SR-86: a domain per component is a legitimate grouping and must produce three memories"
    );
}

/// A wrapped component names one memory in its lift options, so it cannot yet
/// describe a multi-domain fusion. Refuse it rather than emit a component that
/// validates and hands every export the wrong domain's memory.
// rivet: verifies SR-86
#[test]
fn component_output_with_domains_is_refused_rather_than_silently_wrong() {
    let mut fuser = Fuser::new(FuserConfig {
        output_format: meld_core::OutputFormat::Component,
        ..config(vec![vec![CONSUMER, PROVIDER], vec![CONSUMER2]])
    });
    load(&mut fuser);
    let err = fuser.fuse().expect_err(
        "SR-86: --component with domains must be refused; the wrapper cannot name more than \
         one memory in its lift options",
    );
    assert!(
        err.to_string().contains("lift options"),
        "the refusal must say WHY, so a caller knows to emit a core module: {err}"
    );
}
