//! Name manipulation, WASI-name normalization, semver comparison, and
//! component display-name helpers extracted from the merger.

use super::*;

/// Strip `@major.minor.patch` version suffix from a WASI module name.
///
/// `"wasi:io/error@0.2.0"` → `"wasi:io/error"`; `"env"` → `"env"`
/// Build a unique export-name suffix for a per-resource handle table.
///
/// Combines component index, sanitised interface, and resource name into
/// one identifier. The interface sanitisation replaces ':', '/', '@', '.'
/// (illegal in WASM export names? all are legal but conventionally avoided)
/// with '_'.
/// Strip a trailing `$N` dedup suffix from a resource name. Meld appends
/// these when multiple components import the same `[resource-*]X` helper —
/// the canonical resource name (used for handle-table lookup and the
/// canonical-ABI) doesn't include the suffix.
pub(crate) fn strip_dollar_suffix(s: &str) -> &str {
    if let Some(dollar_pos) = s.rfind('$') {
        let suffix = &s[dollar_pos + 1..];
        if !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()) {
            return &s[..dollar_pos];
        }
    }
    s
}

pub(crate) fn ht_export_suffix(comp_idx: usize, interface: &str, resource_name: &str) -> String {
    let safe_iface: String = interface
        .chars()
        .map(|c| match c {
            ':' | '/' | '@' | '.' | '-' => '_',
            other => other,
        })
        .collect();
    format!("{}_{}_{}", comp_idx, safe_iface, resource_name)
}

pub(crate) fn normalize_wasi_module_name(name: &str) -> &str {
    match name.rfind('@') {
        Some(pos) if name[..pos].contains(':') => &name[..pos],
        _ => name,
    }
}

/// Compare two semver-like version strings.
///
/// Implements a small subset of [semver 2.0.0] precedence rules sufficient
/// for the WASI version strings meld encounters:
///
/// * Build metadata (`+...`) is ignored.
/// * The main `MAJOR.MINOR.PATCH` triple is compared numerically; missing
///   trailing segments default to `0` (so `"0.2"` == `"0.2.0"`).
/// * A version *with* a pre-release suffix sorts BEFORE the same version
///   without one (`0.2.0-rc1 < 0.2.0`).
/// * Pre-release identifiers are compared dot-segment-wise: numeric
///   identifiers numerically, alphanumeric identifiers lexically, and
///   numeric identifiers always sort below alphanumeric ones.
/// * Non-numeric main segments fall back to a lexical comparison of that
///   segment (covers exotic inputs like `"0.2.x"`).
///
/// [semver 2.0.0]: https://semver.org/spec/v2.0.0.html
pub(crate) fn compare_version(a: &str, b: &str) -> std::cmp::Ordering {
    use std::cmp::Ordering;

    // Strip build metadata: it does not affect precedence.
    fn strip_build(s: &str) -> &str {
        match s.find('+') {
            Some(i) => &s[..i],
            None => s,
        }
    }
    // Split off pre-release suffix on the first '-'.
    fn split_pre(s: &str) -> (&str, Option<&str>) {
        match s.find('-') {
            Some(i) => (&s[..i], Some(&s[i + 1..])),
            None => (s, None),
        }
    }

    let (main_a, pre_a) = split_pre(strip_build(a));
    let (main_b, pre_b) = split_pre(strip_build(b));

    // Compare the MAJOR.MINOR.PATCH... segments. Treat missing trailing
    // segments as 0 so "0.2" == "0.2.0".
    let segs_a: Vec<&str> = main_a.split('.').collect();
    let segs_b: Vec<&str> = main_b.split('.').collect();
    let max_len = segs_a.len().max(segs_b.len());
    for i in 0..max_len {
        let sa = segs_a.get(i).copied().unwrap_or("0");
        let sb = segs_b.get(i).copied().unwrap_or("0");
        let cmp = match (sa.parse::<u64>(), sb.parse::<u64>()) {
            (Ok(na), Ok(nb)) => na.cmp(&nb),
            // Fall back to lexical compare for non-numeric main segments.
            _ => sa.cmp(sb),
        };
        if cmp != Ordering::Equal {
            return cmp;
        }
    }

    // Main triples are equal — compare pre-release suffixes per semver.
    match (pre_a, pre_b) {
        (None, None) => Ordering::Equal,
        // No-prerelease > has-prerelease.
        (None, Some(_)) => Ordering::Greater,
        (Some(_), None) => Ordering::Less,
        (Some(pa), Some(pb)) => compare_prerelease(pa, pb),
    }
}

/// Compare two semver pre-release strings dot-segment-wise.
///
/// Numeric identifiers compare numerically and sort below alphanumeric
/// identifiers; alphanumerics compare lexically; if all shared segments
/// are equal, the longer suffix wins.
fn compare_prerelease(a: &str, b: &str) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    let mut ia = a.split('.');
    let mut ib = b.split('.');
    loop {
        match (ia.next(), ib.next()) {
            (None, None) => return Ordering::Equal,
            (None, Some(_)) => return Ordering::Less,
            (Some(_), None) => return Ordering::Greater,
            (Some(sa), Some(sb)) => {
                let cmp = match (sa.parse::<u64>(), sb.parse::<u64>()) {
                    (Ok(na), Ok(nb)) => na.cmp(&nb),
                    // Numeric < alphanumeric per semver §11.4.3.
                    (Ok(_), Err(_)) => Ordering::Less,
                    (Err(_), Ok(_)) => Ordering::Greater,
                    (Err(_), Err(_)) => sa.cmp(sb),
                };
                if cmp != Ordering::Equal {
                    return cmp;
                }
            }
        }
    }
}

/// Extract the version suffix from a WASI module name, if any.
///
/// `"wasi:io/error@0.2.6"` → `Some("0.2.6")`; `"env"` → `None`
pub(crate) fn extract_version(name: &str) -> Option<&str> {
    match name.rfind('@') {
        Some(pos) if name[..pos].contains(':') => Some(&name[pos + 1..]),
        _ => None,
    }
}

/// Display name for a component (its declared name, else `component-<idx>`).
/// Used in #326 diagnostics.
pub(crate) fn component_display_name(components: &[ParsedComponent], comp_idx: usize) -> String {
    components
        .get(comp_idx)
        .and_then(|c| c.name.clone())
        .unwrap_or_else(|| format!("component-{comp_idx}"))
}
