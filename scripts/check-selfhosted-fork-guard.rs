//! check-selfhosted-fork-guard — no fork pull request reaches a self-hosted runner.
//!
//! Every line in .github/workflows/*.yml that names `self-hosted` must be one of:
//!
//!   1. a `runs-on:` in exactly the fail-closed same-repo form
//!        ${{ (github.event_name != 'pull_request' || github.event.pull_request.head.repo.full_name == github.repository) && fromJSON('[..."self-hosted"...]') || 'ubuntu-24.04' }}
//!      so the self-hosted labels are chosen only for a non-PR event or a PR
//!      whose head repository is this one. A fork, or a DELETED fork whose
//!      `head.repo` is null, falls to the hosted runner;
//!   2. a matrix `runner:` value inside a job whose `runs-on:` is exactly the
//!      matrix variant of that form (MATRIX_FORM below), which also sends a
//!      self-hosted matrix leg to the hosted runner for a foreign head.
//!
//! Every `runs-on:` is ALLOWLISTED: a hosted image (ubuntu-*, macos-*,
//! windows-*), the fail-closed form, the matrix form, or a plain
//! `${{ matrix.<id> }}` whose every literal value is a hosted image. GitHub
//! matches labels, so `light` or `[linux, light]` reach the self-hosted pool
//! without the word self-hosted. A runner taken from
//! needs.*.outputs, inputs, vars or github.* is rejected, because a step can
//! compute a self-hosted label into a job output and no label appears here.
//! A block-list or map runs-on (a runner group) is rejected too.
//!
//! Rejected: a plain self-hosted label list; the fail-open form
//! `head.repo.fork && 'ubuntu-24.04' || [...]`, which picks self-hosted whenever
//! `.fork` is not true, including a null `head.repo`; and any self-hosted job in
//! a workflow with a trigger outside TRUSTED. The form trusts every event that is
//! not `pull_request`, so a trigger a fork can cause under another name
//! (pull_request_target, workflow_run, issue_comment, ...) would reach the
//! runner. A run that finds no self-hosted line at all fails: it compared
//! nothing.
//!
//! Copied from pulseengine/relay (scripts/check-selfhosted-fork-guard.rs) with the hosted fallback set to
//! ubuntu-24.04 (meld#627). Relay ported it from pulseengine/ordeal#322,
//! extended to cover matrix runners, which that check cannot see because the
//! label sits in `strategy.matrix`, not in `runs-on`.
//!
//! The parse is line-based (no YAML crate, so it builds with plain rustc like
//! scripts/check-verus-trust.rs). It is fail-closed by construction: any
//! non-comment line containing `self-hosted` that is not one of the two
//! accepted shapes is a violation, so a construct this parser does not
//! understand fails rather than passes.
//!
//! Build and run:  rustc --edition 2021 -O scripts/check-selfhosted-fork-guard.rs -o cfg && ./cfg
//! Tests:          rustc --edition 2021 --test scripts/check-selfhosted-fork-guard.rs -o cfg-test && ./cfg-test
//! Exit: 0 ok, 1 violation or nothing compared, 2 could not read the workflows.

use std::fs;
use std::path::Path;
use std::process::ExitCode;

const GUARD: &str = "(github.event_name != 'pull_request' || github.event.pull_request.head.repo.full_name == github.repository)";
const MATRIX_FORM: &str = "${{ (github.event_name != 'pull_request' || github.event.pull_request.head.repo.full_name == github.repository || !contains(matrix.runner, 'self-hosted')) && matrix.runner || 'ubuntu-24.04' }}";
const TRUSTED: &[&str] = &["push", "pull_request", "schedule", "workflow_dispatch", "merge_group"];

/// True when `v` (a runs-on value) is the fail-closed single-label form.
fn is_runs_on_form(v: &str) -> bool {
    let Some(rest) = v.strip_prefix("${{ ") else { return false };
    let Some(rest) = rest.strip_prefix(GUARD) else { return false };
    let Some(rest) = rest.strip_prefix(" && fromJSON('[") else { return false };
    let Some(end) = rest.find("]')") else { return false };
    let labels = &rest[..end];
    labels.contains("\"self-hosted\"")
        && !labels.contains('\'')
        && &rest[end..] == "]') || 'ubuntu-24.04' }}"
}

/// Strips a trailing YAML comment that is outside quotes.
fn strip_comment(line: &str) -> &str {
    let (mut sq, mut dq) = (false, false);
    for (i, c) in line.char_indices() {
        match c {
            '\'' if !dq => sq = !sq,
            '"' if !sq => dq = !dq,
            '#' if !sq && !dq && (i == 0 || line[..i].ends_with(char::is_whitespace)) => {
                return &line[..i];
            }
            _ => {}
        }
    }
    line
}

/// The key of `${{ matrix.<ident> }}` exactly, else None.
fn plain_matrix_key(v: &str) -> Option<&str> {
    v.strip_prefix("${{ matrix.")
        .and_then(|r| r.strip_suffix(" }}"))
        .filter(|id| !id.is_empty() && id.chars().all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-'))
}

/// A GitHub-hosted image name: ubuntu-*, macos-* or windows-*.
fn is_hosted(v: &str) -> bool {
    let v = v.trim().trim_matches(|c| c == '\'' || c == '"');
    ["ubuntu-", "macos-", "windows-"].iter().any(|p| {
        v.strip_prefix(p)
            .is_some_and(|r| !r.is_empty() && r.chars().all(|c| c.is_ascii_alphanumeric() || c == '.' || c == '-'))
    })
}

/// Items of a YAML flow list `[a, "b"]`, else None.
fn flow_items(v: &str) -> Option<Vec<String>> {
    let inner = v.trim().strip_prefix('[')?.strip_suffix(']')?;
    Some(
        inner
            .split(',')
            .map(|i| i.trim().trim_matches(|c| c == '\'' || c == '"').to_string())
            .filter(|i| !i.is_empty())
            .collect(),
    )
}

/// Every literal value written for matrix key `key` in a job's lines: inline
/// (`key: v`, `- key: v`, `key: [a, b]`) or as a block list under `key:`.
fn matrix_values(job_lines: &[&str], key: &str) -> Vec<String> {
    let mut out = Vec::new();
    let head = format!("{key}:");
    for (i, raw) in job_lines.iter().enumerate() {
        let t = strip_comment(raw).trim();
        let t = t.strip_prefix("- ").unwrap_or(t);
        // A flow mapping `{ name: a, runner: ubuntu-24.04 }` (an `include` entry).
        // A value split wrongly by a quoted comma is not a hosted image, so it fails.
        if let Some(inner) = t.strip_prefix('{').and_then(|r| r.strip_suffix('}')) {
            for pair in inner.split(',') {
                if let Some(v) = pair.trim().strip_prefix(&head) {
                    out.push(v.trim().to_string());
                }
            }
            continue;
        }
        let Some(rest) = t.strip_prefix(&head) else { continue };
        let rest = rest.trim();
        if !rest.is_empty() {
            out.push(rest.to_string());
            continue;
        }
        let ind = indent(raw);
        for l in &job_lines[i + 1..] {
            let lt = strip_comment(l).trim();
            if lt.is_empty() {
                continue;
            }
            if indent(l) <= ind && !lt.starts_with("- ") || indent(l) < ind {
                break;
            }
            match lt.strip_prefix("- ") {
                Some(item) if !item.contains(':') => out.push(item.trim().to_string()),
                _ => break,
            }
        }
    }
    out
}

/// A `key: |` / `key: >-` style line, whose following deeper lines are text.
fn is_block_scalar_head(t: &str) -> bool {
    let t = t.trim_start_matches("- ");
    match t.split_once(':') {
        Some((_, v)) => {
            let v = v.trim();
            !v.is_empty() && (v.starts_with('|') || v.starts_with('>')) && v.len() <= 3
        }
        None => false,
    }
}

fn indent(line: &str) -> usize {
    line.len() - line.trim_start().len()
}

/// The workflow's trigger names, from a top-level `on:` (block map, flow list
/// or scalar). Returns None when there is no `on:` key.
fn triggers(lines: &[&str]) -> Option<Vec<String>> {
    let i = lines.iter().position(|l| {
        let t = strip_comment(l).trim_end();
        indent(l) == 0 && (t == "on:" || t.starts_with("on: ") || t == "\"on\":" || t == "'on':")
    })?;
    let head = strip_comment(lines[i]).trim_end();
    let inline = head.split_once(':').map(|x| x.1.trim()).unwrap_or("");
    if !inline.is_empty() {
        let inner = inline.trim_start_matches('[').trim_end_matches(']');
        return Some(inner.split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect());
    }
    let mut out = Vec::new();
    let mut child: Option<usize> = None;
    for l in &lines[i + 1..] {
        let t = strip_comment(l).trim_end();
        if t.trim().is_empty() {
            continue;
        }
        let ind = indent(l);
        if ind == 0 {
            break;
        }
        let c = *child.get_or_insert(ind);
        if ind == c {
            let key = t.trim().trim_start_matches("- ");
            let key = key.split(':').next().unwrap_or("").trim();
            out.push(key.to_string());
        }
    }
    Some(out)
}

#[derive(Debug, PartialEq)]
struct Report {
    seen: usize,
    bad: Vec<String>,
}

/// Checks one workflow's text. `seen` counts self-hosted lines compared.
fn check_workflow(name: &str, text: &str) -> Report {
    let lines: Vec<&str> = text.lines().collect();
    let mut bad = Vec::new();
    let mut seen = 0;
    let mut job_matrix_ok = false; // current job's runs-on is MATRIX_FORM
    let mut jobs_indent: Option<usize> = None;
    let mut job_indent: Option<usize> = None;
    let mut job = String::from("?");
    let mut job_span = (0usize, 0usize); // current job's line range
    // Indent of an open block scalar (`run: |`, `body: >-`); its body is shell
    // or prose, not workflow structure, and is skipped.
    let mut block: Option<usize> = None;
    for (n, raw) in lines.iter().enumerate() {
        let code = strip_comment(raw);
        let t = code.trim();
        if t.is_empty() {
            continue;
        }
        let ind = indent(raw);
        if let Some(b) = block {
            if ind > b {
                continue;
            }
            block = None;
        }
        if is_block_scalar_head(t) {
            block = Some(ind);
        }
        if ind == 0 {
            jobs_indent = if t == "jobs:" { Some(0) } else { None };
            job_indent = None;
            continue;
        }
        if jobs_indent.is_some() {
            let ji = *job_indent.get_or_insert(ind);
            if ind == ji && t.ends_with(':') {
                job = t.trim_end_matches(':').to_string();
                let len = lines[n + 1..]
                    .iter()
                    .take_while(|l| strip_comment(l).trim().is_empty() || indent(l) > ji)
                    .count();
                job_span = (n + 1, n + 1 + len);
                // Look ahead for this job's runs-on to decide matrix trust.
                job_matrix_ok = lines[job_span.0..job_span.1]
                    .iter()
                    .any(|l| strip_comment(l).trim() == format!("runs-on: {MATRIX_FORM}"));
                continue;
            }
        }
        // Every runs-on is shape-checked, not only ones that spell
        // `self-hosted`: a runner computed into needs.*.outputs, inputs, vars
        // or github.* names no label here, yet can resolve to self-hosted.
        if let Some(v) = t.strip_prefix("runs-on:") {
            let v = v.trim();
            let at = format!("{name}:{} ({job})", n + 1);
            let job_lines = &lines[job_span.0..job_span.1];
            // ALLOWLIST. GitHub matches labels, so `light` or `[linux, light]`
            // reach the self-hosted pool without the word self-hosted.
            let ok = if is_runs_on_form(v) {
                true
            } else if v == MATRIX_FORM {
                // Each runner is a hosted image or a self-hosted label list
                // (which the form routes away from a foreign head). A custom
                // label list without `self-hosted` would slip past the guard.
                let vals = matrix_values(job_lines, "runner");
                !vals.is_empty()
                    && vals.iter().all(|x| {
                        let items = flow_items(x);
                        match items {
                            Some(it) => it.iter().any(|i| i == "self-hosted") || it.iter().all(|i| is_hosted(i)),
                            None => is_hosted(x),
                        }
                    })
            } else if let Some(key) = plain_matrix_key(v) {
                let vals = matrix_values(job_lines, key);
                !vals.is_empty()
                    && vals.iter().all(|x| match flow_items(x) {
                        Some(it) => !it.is_empty() && it.iter().all(|i| is_hosted(i)),
                        None => is_hosted(x),
                    })
            } else {
                is_hosted(v)
            };
            if !ok {
                bad.push(format!("{at}: runs-on is not a hosted image, the fail-closed form, or a matrix whose every runner is a hosted image"));
            }
        }
        if !t.contains("self-hosted") {
            continue;
        }
        seen += 1;
        let at = format!("{name}:{} ({job})", n + 1);
        if t.starts_with("runs-on:") {
            // Judged by the allowlist above.
        } else if t.starts_with("runner:") || t.starts_with("- runner:") {
            if !job_matrix_ok {
                bad.push(format!("{at}: self-hosted matrix runner in a job whose runs-on is not the fail-closed matrix form"));
            }
        } else {
            bad.push(format!("{at}: self-hosted outside an accepted runs-on/runner shape"));
        }
    }
    if seen > 0 {
        match triggers(&lines) {
            None => bad.push(format!("{name}: has self-hosted jobs but no readable top-level `on:`")),
            Some(ev) => {
                let untrusted: Vec<_> = ev.iter().filter(|e| !TRUSTED.contains(&e.as_str())).cloned().collect();
                if !untrusted.is_empty() {
                    bad.push(format!("{name}: self-hosted jobs under trigger(s) outside the allowlist: {}", untrusted.join(", ")));
                }
            }
        }
    }
    Report { seen, bad }
}

fn main() -> ExitCode {
    let dir = Path::new(".github/workflows");
    let mut entries: Vec<_> = match fs::read_dir(dir) {
        Ok(rd) => rd.filter_map(|e| e.ok().map(|e| e.path())).collect(),
        Err(e) => {
            eprintln!("could not read {}: {e}", dir.display());
            return ExitCode::from(2);
        }
    };
    entries.retain(|p| matches!(p.extension().and_then(|x| x.to_str()), Some("yml" | "yaml")));
    entries.sort();
    let (mut seen, mut bad) = (0, Vec::new());
    for p in &entries {
        let text = match fs::read_to_string(p) {
            Ok(t) => t,
            Err(e) => {
                eprintln!("could not read {}: {e}", p.display());
                return ExitCode::from(2);
            }
        };
        let name = p.file_name().unwrap().to_string_lossy();
        let r = check_workflow(&name, &text);
        seen += r.seen;
        bad.extend(r.bad);
    }
    for b in &bad {
        println!("FAIL  {b}");
    }
    if seen == 0 {
        println!("FAIL  no self-hosted line found in {} workflow(s): this check compared nothing", entries.len());
        return ExitCode::from(1);
    }
    if !bad.is_empty() {
        println!("FAIL  {} violation(s) across {seen} self-hosted line(s)", bad.len());
        return ExitCode::from(1);
    }
    println!("self-hosted fork guard: OK ({seen} self-hosted line(s) in {} workflow(s), all fail-closed)", entries.len());
    ExitCode::SUCCESS
}

#[cfg(test)]
mod tests {
    use super::*;

    fn good(label: &str) -> String {
        format!("${{{{ {GUARD} && fromJSON('[\"self-hosted\",\"linux\",\"x64\",\"{label}\"]') || 'ubuntu-24.04' }}}}")
    }
    fn wf(on: &str, runs_on: &str) -> String {
        format!("name: t\n{on}\njobs:\n  a:\n    runs-on: {runs_on}\n    steps:\n      - run: true\n")
    }

    #[test]
    fn accepts_the_fail_closed_form() {
        let r = check_workflow("t.yml", &wf("on:\n  pull_request:\n  push:", &good("light")));
        assert_eq!(r, Report { seen: 1, bad: vec![] });
    }

    #[test]
    fn rejects_the_fail_open_fork_form() {
        let v = "${{ github.event.pull_request.head.repo.fork && 'ubuntu-24.04' || fromJSON('[\"self-hosted\",\"linux\"]') }}";
        let r = check_workflow("t.yml", &wf("on: [pull_request]", v));
        assert_eq!(r.bad.len(), 1, "{r:?}");
    }

    #[test]
    fn rejects_a_plain_label_list() {
        let r = check_workflow("t.yml", &wf("on:\n  schedule:", "[self-hosted, linux, x64, light]"));
        assert_eq!(r.bad.len(), 1, "{r:?}");
    }

    #[test]
    fn rejects_swapped_branches() {
        // Correct guard, but self-hosted on the FALSE branch: fail-open.
        let v = format!("${{{{ {GUARD} && 'ubuntu-24.04' || fromJSON('[\"self-hosted\"]') }}}}");
        let r = check_workflow("t.yml", &wf("on: [pull_request]", &v));
        assert_eq!(r.bad.len(), 1, "{r:?}");
    }

    #[test]
    fn rejects_untrusted_triggers_even_with_the_form() {
        for on in ["on:\n  pull_request_target:", "on: [workflow_run]", "on:\n  issue_comment:\n    types: [created]"] {
            let r = check_workflow("t.yml", &wf(on, &good("light")));
            assert_eq!(r.bad.len(), 1, "{on}: {r:?}");
        }
    }

    #[test]
    fn trigger_parse_ignores_nested_keys() {
        let on = "on:\n  push:\n    branches: [main]\n  pull_request:\n    paths:\n      - 'x'";
        let r = check_workflow("t.yml", &wf(on, &good("light")));
        assert_eq!(r, Report { seen: 1, bad: vec![] });
    }

    #[test]
    fn matrix_runner_needs_the_matrix_form() {
        let body = |ro: &str| {
            format!(
                "on: [pull_request]\njobs:\n  test:\n    strategy:\n      matrix:\n        include:\n          - label: linux\n            runner: [self-hosted, linux, x64, rust-cpu]\n          - label: macos\n            runner: macos-14\n    runs-on: {ro}\n    steps:\n      - run: true\n"
            )
        };
        assert_eq!(check_workflow("t.yml", &body(MATRIX_FORM)).bad, Vec::<String>::new());
        let fail_open = "${{ github.event.pull_request.head.repo.fork && contains(matrix.runner, 'self-hosted') && 'ubuntu-24.04' || matrix.runner }}";
        // Both the matrix runner and the runs-on line are flagged.
        assert_eq!(check_workflow("t.yml", &body(fail_open)).bad.len(), 2);
    }

    #[test]
    fn self_hosted_in_an_unknown_shape_fails_closed() {
        let t = "on: [pull_request]\njobs:\n  a:\n    runs-on:\n      - self-hosted\n    steps:\n      - run: true\n";
        assert!(!check_workflow("t.yml", t).bad.is_empty());
    }

    #[test]
    fn comments_naming_self_hosted_are_ignored() {
        let t = format!("# runs on self-hosted\n{}", wf("on: [push]", &good("rust-cpu")));
        assert_eq!(check_workflow("t.yml", &t), Report { seen: 1, bad: vec![] });
    }

    #[test]
    fn shell_text_in_run_blocks_is_not_structure() {
        let t = format!(
            "on: [push]\njobs:\n  a:\n    runs-on: {}\n    steps:\n      - run: |\n          echo self-hosted fleet\n          kind=\"self-hosted\"\n      - name: x\n        run: true\n",
            good("light")
        );
        assert_eq!(check_workflow("t.yml", &t), Report { seen: 1, bad: vec![] });
    }

    #[test]
    fn a_runs_on_after_a_run_block_is_still_checked() {
        let t = "on: [push]\njobs:\n  a:\n    runs-on: ubuntu-24.04\n    steps:\n      - run: |\n          echo hi\n  b:\n    runs-on: [self-hosted, light]\n";
        assert_eq!(check_workflow("t.yml", t).bad.len(), 1);
    }

    #[test]
    fn computed_runners_are_rejected() {
        for v in [
            "${{ needs.pick.outputs.runner }}",
            "${{ inputs.runner }}",
            "${{ vars.RUNNER }}",
            "${{ fromJSON(needs.pick.outputs.labels) }}",
            "${{ github.event.inputs.runner || 'ubuntu-24.04' }}",
        ] {
            let r = check_workflow("t.yml", &wf("on: [workflow_dispatch]", v));
            assert_eq!(r.bad.len(), 1, "{v}: {r:?}");
        }
    }

    #[test]
    fn plain_matrix_and_literal_hosted_runners_pass() {
        for v in ["ubuntu-24.04", "macos-14", "windows-2022"] {
            let r = check_workflow("t.yml", &wf("on: [pull_request]", v));
            assert_eq!(r, Report { seen: 0, bad: vec![] }, "{v}");
        }
    }

    #[test]
    fn block_and_map_runs_on_are_rejected() {
        let list = "on: [push]\njobs:\n  a:\n    runs-on:\n      - ${{ needs.x.outputs.r }}\n";
        let map = "on: [push]\njobs:\n  a:\n    runs-on: { group: fleet }\n";
        assert_eq!(check_workflow("t.yml", list).bad.len(), 1);
        assert_eq!(check_workflow("t.yml", map).bad.len(), 1);
    }

    #[test]
    fn bare_and_listed_custom_labels_are_rejected() {
        for v in ["light", "[linux, light]", "[light]", "rust-cpu"] {
            let r = check_workflow("t.yml", &wf("on: [schedule]", v));
            assert_eq!(r.bad.len(), 1, "{v}: {r:?}");
        }
    }

    #[test]
    fn plain_matrix_ref_needs_every_value_hosted() {
        let job = |axis: &str| format!("on: [push]\njobs:\n  a:\n    strategy:\n      matrix:\n{axis}\n    runs-on: ${{{{ matrix.os }}}}\n");
        assert!(check_workflow("t.yml", &job("        os: [ubuntu-24.04, macos-14]")).bad.is_empty());
        assert!(check_workflow("t.yml", &job("        os:\n          - ubuntu-24.04\n          - windows-2022")).bad.is_empty());
        assert!(check_workflow("t.yml", &job("        include:\n          - os: ubuntu-24.04\n          - os: macos-14")).bad.is_empty());
        assert_eq!(check_workflow("t.yml", &job("        os: [ubuntu-24.04, light]")).bad.len(), 1);
        assert_eq!(check_workflow("t.yml", &job("        include:\n          - os: ubuntu-24.04\n          - os: light")).bad.len(), 1);
        // meld: flow-mapping include entries (release-npm.yml, release-pypi.yml).
        assert!(check_workflow("t.yml", &job("        include:\n          - { name: a, os: ubuntu-24.04, docker: '' }\n          - { name: b, os: macos-15 }")).bad.is_empty());
        assert_eq!(check_workflow("t.yml", &job("        include:\n          - { name: a, os: ubuntu-24.04 }\n          - { name: b, os: light }")).bad.len(), 1);
        assert_eq!(check_workflow("t.yml", &job("        os: ${{ fromJSON(vars.OSES) }}")).bad.len(), 1);
        // A matrix ref with no literal values for that key compared nothing.
        assert_eq!(check_workflow("t.yml", &job("        arch: [x64]")).bad.len(), 1);
    }

    #[test]
    fn matrix_form_rejects_a_custom_label_runner() {
        let job = "on: [pull_request]\njobs:\n  test:\n    strategy:\n      matrix:\n        include:\n          - runner: [linux, light]\n";
        let t = format!("{job}    runs-on: {MATRIX_FORM}\n");
        assert_eq!(check_workflow("t.yml", &t).bad.len(), 1);
    }

    #[test]
    fn a_workflow_without_self_hosted_is_not_counted() {
        let r = check_workflow("t.yml", &wf("on: [pull_request_target]", "ubuntu-24.04"));
        assert_eq!(r, Report { seen: 0, bad: vec![] });
    }
}
