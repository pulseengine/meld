//! The README and `proofs/STATUS.md` state how many closed Rocq proofs
//! (`Qed.`) meld carries. The number is written by hand, so it is pinned to
//! the floor the proofs workflow enforces (`[ "$qed" -ge N ]` in
//! `.github/workflows/proofs.yml`): changing either side alone fails here.
//! The tree's own count must also reach the floor, the same census the
//! workflow takes (`grep -ho 'Qed\.'` over every `.v` under `proofs/`).

use std::path::{Path, PathBuf};

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..")
}

fn read(rel: &str) -> String {
    std::fs::read_to_string(repo().join(rel)).unwrap_or_else(|e| panic!("{rel}: {e}"))
}

/// The number right after `prefix` in `text`, which must occur exactly once.
fn number_after(text: &str, prefix: &str, file: &str) -> u64 {
    let hits: Vec<_> = text.match_indices(prefix).collect();
    assert_eq!(
        hits.len(),
        1,
        "{file}: expected one `{prefix}`, found {}",
        hits.len()
    );
    let rest = &text[hits[0].0 + prefix.len()..];
    let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
    digits
        .parse()
        .unwrap_or_else(|_| panic!("{file}: no number after `{prefix}`"))
}

fn qed_floor() -> u64 {
    number_after(
        &read(".github/workflows/proofs.yml"),
        "[ \"$qed\"      -ge ",
        "proofs.yml",
    )
}

fn count_qed(dir: &Path) -> u64 {
    let mut n = 0;
    for entry in std::fs::read_dir(dir).unwrap().flatten() {
        let path = entry.path();
        if path.is_dir() {
            n += count_qed(&path);
        } else if path.extension().is_some_and(|x| x == "v") {
            n += std::fs::read_to_string(&path)
                .unwrap()
                .matches("Qed.")
                .count() as u64;
        }
    }
    n
}

#[test]
fn the_readme_states_the_qed_floor() {
    let readme = number_after(&read("README.md"), "Rocq proofs — at least ", "README.md");
    assert_eq!(
        readme,
        qed_floor(),
        "README.md says at least {readme} closed proofs; proofs.yml enforces {}. \
         Change both together.",
        qed_floor()
    );
}

#[test]
fn status_md_states_the_qed_floor() {
    let status = number_after(
        &read("proofs/STATUS.md"),
        "| Closed proofs (Qed) | at least ",
        "proofs/STATUS.md",
    );
    assert_eq!(
        status,
        qed_floor(),
        "proofs/STATUS.md says at least {status}; proofs.yml enforces {}. \
         Change both together.",
        qed_floor()
    );
}

#[test]
fn the_tree_reaches_the_qed_floor() {
    let counted = count_qed(&repo().join("proofs"));
    assert!(
        counted >= qed_floor(),
        "proofs/ has {counted} `Qed.`, below the floor {}",
        qed_floor()
    );
}
