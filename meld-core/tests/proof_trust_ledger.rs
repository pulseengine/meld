//! Every place a proof is trusted rather than checked is listed in a
//! committed ledger, and a new one fails CI until the ledger names it.
//!
//! Escapes counted:
//! - Rocq (`proofs/**/*.v`): `Admitted.`, and top-level `Axiom`, `Axioms`,
//!   `Parameter`, `Parameters`, `Conjecture`, and the checker bypasses
//!   `#[bypass_check(...)]` and `Unset Positivity/Guard/Universe Checking`.
//!   These are what the kernel takes on faith. The proof census in proofs.yml counts only the text
//!   `Admitted.`, so an `Axiom` passed it.
//! - Verus (any `.rs` file containing `verus!`): `#[verifier::external_body]`,
//!   `#[verifier::external]`, `assume(`, `admit(`, `assume_specification`.
//!   Nothing in CI counted these.
//!
//! Not counted: `kani::assume`, which bounds a harness's inputs (a vacuity
//! question, not a trust escape), and `Variable` / `Hypothesis` inside a
//! `Section`, which the section discharges. The kernel check in proofs.yml
//! (`coqchk -o`) catches what this text scan cannot: an axiom reached through
//! a dependency, or one declared in a form this scan does not recognise.
//!
//! The ledger is `proofs/trust-escapes.tsv` and must equal what the scan
//! finds. A new escape fails until it is added (the reviewable decision); a
//! removed one fails until its line is deleted, so the ledger stays exact and
//! a later reintroduction is not silently pre-approved. `MELD_BLESS=1`
//! rewrites the file.
//!
//! This runs in Test (ci.yml), not in proofs.yml: proofs.yml runs only on
//! `proofs/**`, so it would never see a change to `verification/`.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

const LEDGER: &str = "proofs/trust-escapes.tsv";

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("workspace root")
        .to_path_buf()
}

type Entry = (String, String, String); // (path, kind, name)

/// Remove Rocq comments, which nest: `(* a (* b *) c *)`.
fn strip_rocq_comments(src: &str) -> String {
    let b = src.as_bytes();
    let (mut out, mut depth, mut i) = (String::with_capacity(src.len()), 0usize, 0usize);
    while i < b.len() {
        if b[i..].starts_with(b"(*") {
            depth += 1;
            i += 2;
        } else if depth > 0 && b[i..].starts_with(b"*)") {
            depth -= 1;
            i += 2;
        } else {
            if depth == 0 {
                out.push(b[i] as char);
            } else if b[i] == b'\n' {
                out.push('\n');
            }
            i += 1;
        }
    }
    out
}

fn ident_after<'a>(s: &'a str, kw: &str) -> Option<&'a str> {
    let rest = s.strip_prefix(kw)?;
    if !rest.starts_with(char::is_whitespace) {
        return None;
    }
    let rest = rest.trim_start().trim_start_matches('(');
    let end = rest
        .find(|c: char| !(c.is_alphanumeric() || c == '_' || c == '\''))
        .unwrap_or(rest.len());
    (end > 0).then(|| &rest[..end])
}

const ROCQ_DECLS: [&str; 5] = ["Axioms", "Axiom", "Parameters", "Parameter", "Conjecture"];
const ROCQ_PROOF_HEADS: [&str; 9] = [
    "Theorem",
    "Lemma",
    "Corollary",
    "Proposition",
    "Fact",
    "Remark",
    "Example",
    "Definition",
    "Instance",
];

fn scan_rocq(path: &str, src: &str) -> Vec<Entry> {
    let text = strip_rocq_comments(src);
    let mut out = Vec::new();
    let mut current = String::from("?");
    for line in text.lines() {
        let t = line.trim_start();
        for head in ROCQ_PROOF_HEADS {
            if let Some(name) = ident_after(t, head) {
                current = name.to_string();
            }
        }
        for kw in ROCQ_DECLS {
            if let Some(name) = ident_after(t, kw) {
                out.push((
                    path.to_string(),
                    kw.trim_end_matches('s').to_string(),
                    name.to_string(),
                ));
                break;
            }
        }
        if let Some(i) = t.find("#[bypass_check(") {
            let what: String = t[i + 15..].chars().take_while(|c| *c != ')').collect();
            out.push((path.to_string(), "bypass_check".into(), what));
        }
        for check in ["Positivity", "Guard", "Universe"] {
            if t.starts_with(&format!("Unset {check} Checking")) {
                out.push((path.to_string(), "Unset Checking".into(), check.to_string()));
            }
        }
        for _ in t.matches("Admitted.") {
            out.push((path.to_string(), "Admitted".into(), current.clone()));
        }
    }
    out
}

fn scan_verus(path: &str, src: &str) -> Vec<Entry> {
    let mut out = Vec::new();
    let mut current = String::from("?");
    let mut pending_attr: Option<&str> = None;
    for line in src.lines() {
        let t = line.trim_start();
        if t.starts_with("//") {
            continue;
        }
        if t.contains("#[verifier::external_body]") {
            pending_attr = Some("external_body");
        } else if t.contains("#[verifier::external]") {
            pending_attr = Some("external");
        }
        if let Some(pos) = t.find("fn ") {
            let name: String = t[pos + 3..]
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_')
                .collect();
            if !name.is_empty() {
                current = name;
                if let Some(kind) = pending_attr.take() {
                    out.push((path.to_string(), kind.into(), current.clone()));
                }
            }
        }
        for (pat, kind) in [
            ("assume_specification", "assume_specification"),
            ("assume(", "assume"),
            ("admit(", "admit"),
        ] {
            for (i, _) in t.match_indices(pat) {
                // `kani::assume(` and `foo_assume(` are not Verus's `assume`.
                let before = &t[..i];
                if before.ends_with("::")
                    || before.ends_with(|c: char| c.is_alphanumeric() || c == '_')
                {
                    continue;
                }
                out.push((path.to_string(), kind.into(), current.clone()));
            }
        }
    }
    out
}

fn walk(dir: &Path, files: &mut Vec<PathBuf>) {
    let Ok(rd) = std::fs::read_dir(dir) else {
        return;
    };
    for e in rd.flatten() {
        let p = e.path();
        let name = e.file_name().to_string_lossy().to_string();
        if p.is_dir() {
            if name == "target" || name.starts_with('.') || name.starts_with("bazel-") {
                continue;
            }
            walk(&p, files);
        } else if name.ends_with(".v") || name.ends_with(".rs") {
            files.push(p);
        }
    }
}

fn scan_tree(root: &Path) -> BTreeSet<Entry> {
    let mut files = Vec::new();
    walk(root, &mut files);
    let mut found = BTreeSet::new();
    let mut verus_files = 0;
    for p in files {
        let rel = p
            .strip_prefix(root)
            .unwrap()
            .to_string_lossy()
            .replace('\\', "/");
        let Ok(src) = std::fs::read_to_string(&p) else {
            continue;
        };
        if rel.ends_with(".v") && rel.starts_with("proofs/") {
            found.extend(scan_rocq(&rel, &src));
        } else if rel.ends_with(".rs")
            && src.contains("verus!")
            && rel != "meld-core/tests/proof_trust_ledger.rs"
        {
            verus_files += 1;
            found.extend(scan_verus(&rel, &src));
        }
    }
    // Potency floor: the scan must reach the Verus pilot, or "no escapes"
    // would only mean "looked nowhere".
    assert!(
        verus_files >= 1,
        "found no verus! file; the Verus half of the scan is vacuous"
    );
    found
}

fn read_ledger(text: &str) -> BTreeSet<Entry> {
    text.lines()
        .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
        .map(|l| {
            let c: Vec<&str> = l.split('\t').collect();
            assert_eq!(c.len(), 3, "{LEDGER}: want path<TAB>kind<TAB>name: {l:?}");
            (c[0].into(), c[1].into(), c[2].into())
        })
        .collect()
}

#[test]
fn trust_escapes_match_the_ledger() {
    let root = repo_root();
    let path = root.join(LEDGER);
    let text = std::fs::read_to_string(&path).expect("ledger");
    let ledger = read_ledger(&text);
    let found = scan_tree(&root);
    // The proofs/ half must have looked at files too.
    assert!(
        std::fs::read_dir(root.join("proofs")).is_ok(),
        "no proofs/ directory; the Rocq half of the scan is vacuous"
    );

    if std::env::var_os("MELD_BLESS").is_some() {
        let header: String = text
            .lines()
            .filter(|l| l.starts_with('#'))
            .map(|l| format!("{l}\n"))
            .collect();
        let body: String = found
            .iter()
            .map(|(p, k, n)| format!("{p}\t{k}\t{n}\n"))
            .collect();
        std::fs::write(&path, header + &body).expect("write ledger");
        return;
    }
    let new: Vec<_> = found.difference(&ledger).collect();
    let gone: Vec<_> = ledger.difference(&found).collect();
    assert!(
        new.is_empty(),
        "new trust escapes not in {LEDGER}: {new:?}\nEach is a claim taken on faith. \
         Prove it, or add it to the ledger in the same change so the decision is reviewed."
    );
    assert!(
        gone.is_empty(),
        "{LEDGER} lists escapes that no longer exist: {gone:?}\nDelete those lines \
         (removing an escape is always fine; the ledger just has to stay exact)."
    );
}

#[test]
fn the_scan_can_fail() {
    // Negative controls on inline text, for each kind the scan claims to see.
    let v = "(* Axiom hidden : False. *)\nAxiom ax : False.\nParameter p : nat.\n\
             Lemma l : True.\nProof. Admitted.\nConjecture c : True.\n\
             #[bypass_check(positivity)]\nUnset Guard Checking.\n";
    let got: Vec<_> = scan_rocq("x.v", v)
        .into_iter()
        .map(|(_, k, n)| (k, n))
        .collect();
    assert_eq!(
        got,
        [
            ("Axiom".to_string(), "ax".to_string()),
            ("Parameter".into(), "p".into()),
            ("Admitted".into(), "l".into()),
            ("Conjecture".into(), "c".into()),
            ("bypass_check".into(), "positivity".into()),
            ("Unset Checking".into(), "Guard".into()),
        ]
    );
    let r = "verus! {\n#[verifier::external_body]\nfn f() {}\nfn g() { assume(x); admit(); }\n\
             fn h() { kani::assume(y); my_assume(z); }\n// assume(commented)\n}\n";
    let got: Vec<_> = scan_verus("x.rs", r)
        .into_iter()
        .map(|(_, k, n)| (k, n))
        .collect();
    assert_eq!(
        got,
        [
            ("external_body".to_string(), "f".to_string()),
            ("assume".into(), "g".into()),
            ("admit".into(), "g".into()),
        ]
    );
}
