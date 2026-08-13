//! Embedded, queryable documentation (SR-64) — modelled on `rivet docs` (and
//! mirroring varve's REQ-DOCS-001).
//!
//! Topics are compiled INTO the binary (`include_str!`), so `meld docs` works
//! with no files and no network — air-gapped by construction. `--format json`
//! makes the same content machine-queryable (modelled on `rivet docs`).
//! Coverage is a mechanical invariant: `meld docs check --coverage` enumerates
//! the CLI's top-level subcommands and reports any without a topic; `--strict`
//! exits non-zero, so an undocumented subcommand cannot ship (a gate, not
//! review discipline).

/// One documentation topic: a stable slug, a title, and a markdown body.
pub struct Topic {
    pub slug: &'static str,
    pub title: &'static str,
    pub body: &'static str,
}

macro_rules! topic {
    ($slug:literal, $title:literal, $file:literal) => {
        Topic {
            slug: $slug,
            title: $title,
            body: include_str!(concat!("../docs/", $file)),
        }
    };
}

/// The embedded topic registry. Command topics use the exact clap subcommand
/// name so the coverage check can match them mechanically.
pub const TOPICS: &[Topic] = &[
    // ── concepts ──────────────────────────────────────────────────────
    topic!(
        "fusion",
        "Static fusion — what meld does",
        "concept-fusion.md"
    ),
    topic!(
        "memory-strategies",
        "Memory strategies — auto, multi, shared",
        "concept-memory-strategies.md"
    ),
    topic!(
        "address-rebasing",
        "Address rebasing — one memory, no collisions",
        "concept-address-rebasing.md"
    ),
    topic!(
        "pack-rebase",
        "Pack-rebase — the compact used-extent envelope",
        "concept-pack-rebase.md"
    ),
    topic!(
        "adapters",
        "Adapters — Canonical-ABI cross-component seams",
        "concept-adapters.md"
    ),
    topic!(
        "attestation",
        "Attestation — a signed record of how the artifact was fused",
        "concept-attestation.md"
    ),
    topic!(
        "provenance",
        "Provenance — mapping fused functions back to their component",
        "concept-provenance.md"
    ),
    // ── one per CLI subcommand (slug == clap name) ────────────────────
    topic!(
        "fuse",
        "fuse — fuse components into one core module",
        "cmd-fuse.md"
    ),
    topic!(
        "inspect",
        "inspect — examine a WebAssembly component",
        "cmd-inspect.md"
    ),
    topic!(
        "version",
        "version — show version and toolchain context",
        "cmd-version.md"
    ),
    topic!("docs", "docs — this documentation", "cmd-docs.md"),
];

pub fn find(slug: &str) -> Option<&'static Topic> {
    TOPICS.iter().find(|t| t.slug == slug)
}

/// Command names (clap subcommands) that have NO topic — the coverage gap.
pub fn coverage_gaps(cmd: &clap::Command) -> Vec<String> {
    cmd.get_subcommands()
        .map(|c| c.get_name().to_string())
        .filter(|name| find(name).is_none())
        .collect()
}

/// Render the topic list (slug + title).
pub fn render_list() -> String {
    let mut out = String::from("meld docs — topics (meld docs <topic>):\n\n");
    for t in TOPICS {
        out.push_str(&format!("  {:<20} {}\n", t.slug, t.title));
    }
    out
}

/// Machine-readable JSON, modelled on `rivet docs --format json` so the docs
/// can be queried by tooling, not just read. `None` → the topic list (slug +
/// title per entry, no bodies); `Some(slug)` → that one topic with its full
/// body (an empty `{}` if the slug is unknown, mirroring the human path).
pub fn render_json(slug: Option<&str>) -> String {
    match slug {
        None => {
            let list: Vec<_> = TOPICS
                .iter()
                .map(|t| serde_json::json!({"slug": t.slug, "title": t.title}))
                .collect();
            serde_json::to_string_pretty(&list).expect("topic list serialises")
        }
        Some(s) => match find(s) {
            Some(t) => serde_json::to_string_pretty(
                &serde_json::json!({"slug": t.slug, "title": t.title, "body": t.body}),
            )
            .expect("topic serialises"),
            None => "{}".to_string(),
        },
    }
}

/// grep across all topic bodies + titles; returns (slug, matching line).
pub fn grep(query: &str) -> Vec<(&'static str, String)> {
    let q = query.to_lowercase();
    let mut hits = Vec::new();
    for t in TOPICS {
        if t.title.to_lowercase().contains(&q) {
            hits.push((t.slug, t.title.to_string()));
        }
        for line in t.body.lines() {
            if line.to_lowercase().contains(&q) {
                hits.push((t.slug, line.trim().to_string()));
            }
        }
    }
    hits
}

#[cfg(test)]
mod tests {
    use super::*;

    // rivet: verifies SR-64
    #[test]
    fn every_cli_subcommand_has_a_documented_topic() {
        use clap::CommandFactory;
        let cmd = crate::Cli::command();
        let gaps = coverage_gaps(&cmd);
        assert!(
            gaps.is_empty(),
            "these subcommands have no `meld docs` topic (SR-64): {gaps:?}"
        );
    }

    // rivet: verifies SR-64
    #[test]
    fn topics_are_findable_and_greppable() {
        assert!(find("fusion").is_some());
        assert!(find("fuse").is_some());
        assert!(find("nonexistent").is_none());
        // A concept every topic set should mention.
        assert!(
            !grep("memory").is_empty(),
            "grep should find 'memory' somewhere"
        );
    }

    // rivet: verifies SR-64
    #[test]
    fn topic_list_renders_as_machine_readable_json() {
        let v: serde_json::Value = serde_json::from_str(&render_json(None)).unwrap();
        let arr = v.as_array().expect("--format json list is a JSON array");
        assert_eq!(arr.len(), TOPICS.len());
        // Every entry carries slug + title; the list form omits the body.
        let first = &arr[0];
        assert!(first.get("slug").and_then(|s| s.as_str()).is_some());
        assert!(first.get("title").and_then(|s| s.as_str()).is_some());
        assert!(first.get("body").is_none(), "list form omits bodies");
    }

    // rivet: verifies SR-64
    #[test]
    fn single_topic_renders_as_json_with_body() {
        let v: serde_json::Value = serde_json::from_str(&render_json(Some("fusion"))).unwrap();
        assert_eq!(v.get("slug").and_then(|s| s.as_str()), Some("fusion"));
        assert!(
            v.get("body").and_then(|s| s.as_str()).unwrap().len() > 40,
            "single-topic JSON carries the full body"
        );
    }

    // rivet: verifies SR-64
    #[test]
    fn unknown_topic_json_is_empty_object() {
        assert_eq!(render_json(Some("nonexistent")), "{}");
    }

    // rivet: verifies SR-64
    #[test]
    fn no_topic_body_is_empty() {
        for t in TOPICS {
            assert!(
                t.body.trim().len() > 40,
                "topic {} is too short to be real documentation",
                t.slug
            );
        }
    }
}
