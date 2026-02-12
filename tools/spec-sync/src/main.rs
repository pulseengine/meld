//! spec-sync: Generate Rocq specifications from WebAssembly spec reference interpreter
//!
//! This tool parses the OCaml type definitions from the WebAssembly spec's
//! reference interpreter and generates corresponding Rocq/Coq definitions.
//!
//! Key features:
//! - Handles OCaml mutual recursion (`type ... and ... and ...`) properly
//! - Generates Rocq `Inductive ... with ...` for mutually recursive types
//! - Uses Tarjan's algorithm to detect dependency cycles
//! - Deduplicates type definitions across source files
//!
//! Usage:
//!   spec-sync --spec-dir <path-to-wasm-spec> --output <output.v>

use anyhow::{Context, Result};
use clap::Parser;
use regex::Regex;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::PathBuf;

/// Generate Rocq specifications from WebAssembly spec
#[derive(Parser, Debug)]
#[command(author, version, about)]
struct Args {
    /// Path to WebAssembly spec repository
    #[arg(long)]
    spec_dir: PathBuf,

    /// Output Rocq file
    #[arg(long, short)]
    output: PathBuf,

    /// Generate version tracking file
    #[arg(long)]
    version_file: Option<PathBuf>,
}

/// Tracks spec versions for change detection
#[derive(Debug, Serialize, Deserialize)]
struct VersionInfo {
    spec_commit: String,
    generated_at: String,
    types_hash: String,
    ast_hash: String,
}

/// Represents an OCaml type definition
#[derive(Debug, Clone)]
enum OcamlType {
    /// type name = variant1 | variant2 | ...
    Variant {
        name: String,
        variants: Vec<VariantCase>,
    },
    /// type name = { field1: type1; field2: type2; ... }
    Record {
        name: String,
        fields: Vec<RecordField>,
    },
    /// type name = existing_type
    Alias {
        name: String,
        target: String,
    },
}

#[derive(Debug, Clone)]
struct VariantCase {
    name: String,
    args: Vec<String>,
}

#[derive(Debug, Clone)]
struct RecordField {
    name: String,
    ty: String,
    #[allow(dead_code)]
    mutable: bool,
}

/// A group of mutually recursive type definitions.
/// In OCaml: `type a = ... and b = ... and c = ...`
/// In Rocq: `Inductive a := ... with b := ... with c := ...`
#[derive(Debug, Clone)]
struct MutualRecGroup {
    /// The types in this mutual recursion group, in definition order
    types: Vec<OcamlType>,
    /// Source file identifier (for deduplication)
    source: String,
}

impl MutualRecGroup {
    fn new(types: Vec<OcamlType>, source: &str) -> Self {
        Self {
            types,
            source: source.to_string(),
        }
    }

    #[allow(dead_code)]
    fn single(ty: OcamlType, source: &str) -> Self {
        Self {
            types: vec![ty],
            source: source.to_string(),
        }
    }

    /// Get all type names in this group
    #[cfg(test)]
    fn type_names(&self) -> Vec<&str> {
        self.types.iter().map(|t| t.name()).collect()
    }

    /// Check if this group contains a type with the given name
    #[allow(dead_code)]
    fn contains(&self, name: &str) -> bool {
        self.types.iter().any(|t| t.name() == name)
    }
}

impl OcamlType {
    fn name(&self) -> &str {
        match self {
            OcamlType::Variant { name, .. } => name,
            OcamlType::Record { name, .. } => name,
            OcamlType::Alias { name, .. } => name,
        }
    }

    /// Get all type references (dependencies) used by this type
    fn dependencies(&self) -> Vec<String> {
        match self {
            OcamlType::Variant { variants, .. } => {
                variants
                    .iter()
                    .flat_map(|v| v.args.iter().cloned())
                    .flat_map(|arg| extract_type_refs(&arg))
                    .collect()
            }
            OcamlType::Record { fields, .. } => {
                fields
                    .iter()
                    .flat_map(|f| extract_type_refs(&f.ty))
                    .collect()
            }
            OcamlType::Alias { target, .. } => extract_type_refs(target),
        }
    }
}

/// Extract base type references from a type expression
fn extract_type_refs(ty: &str) -> Vec<String> {
    let ty = ty.trim();
    let mut refs = Vec::new();

    // Remove common wrappers and extract base types
    // Handle: "t option", "t list", "t ref", "(t1 * t2)"
    let cleaned = ty
        .replace(" option", "")
        .replace(" list", "")
        .replace(" ref", "")
        .replace(" array", "");

    // Split on tuple separator and extract individual types
    for part in cleaned.split('*') {
        let part = part.trim().trim_matches(|c| c == '(' || c == ')');
        // Skip built-in types
        if !part.is_empty()
            && !["int", "int32", "int64", "float", "bool", "string", "unit", "nat"]
                .contains(&part)
        {
            // Extract just the type name (first word)
            if let Some(name) = part.split_whitespace().next() {
                // Skip qualified names from other modules
                if !name.contains('.') {
                    refs.push(name.to_string());
                }
            }
        }
    }

    refs
}

fn main() -> Result<()> {
    let args = Args::parse();

    let types_path = args.spec_dir.join("interpreter/syntax/types.ml");
    let ast_path = args.spec_dir.join("interpreter/syntax/ast.ml");

    // Read OCaml source files
    let types_content =
        fs::read_to_string(&types_path).context("Failed to read types.ml")?;
    let ast_content =
        fs::read_to_string(&ast_path).context("Failed to read ast.ml")?;

    // Parse type definitions, preserving mutual recursion groups
    let mut groups = Vec::new();
    groups.extend(parse_ocaml_types_grouped(&types_content, "types.ml")?);
    groups.extend(parse_ocaml_types_grouped(&ast_content, "ast.ml")?);

    // Deduplicate types (prefer first occurrence)
    let groups = deduplicate_groups(groups);

    // Find dependency cycles and merge affected groups
    let groups = merge_cyclic_groups(groups);

    // Topologically sort groups
    let sorted_groups = topological_sort_groups(groups);

    // Generate Rocq output
    let rocq_output = generate_rocq_from_groups(&sorted_groups)?;
    fs::write(&args.output, &rocq_output).context("Failed to write output")?;

    let total_types: usize = sorted_groups.iter().map(|g| g.types.len()).sum();
    println!(
        "Generated {} type definitions ({} groups) to {:?}",
        total_types,
        sorted_groups.len(),
        args.output
    );

    // Optionally write version info
    if let Some(version_path) = args.version_file {
        let version_info = VersionInfo {
            spec_commit: get_git_commit(&args.spec_dir)?,
            generated_at: chrono_lite_now(),
            types_hash: simple_hash(&types_content),
            ast_hash: simple_hash(&ast_content),
        };
        let json = serde_json::to_string_pretty(&version_info)?;
        fs::write(&version_path, json)?;
    }

    Ok(())
}

/// Parse OCaml type definitions from source, preserving mutual recursion groups
fn parse_ocaml_types_grouped(content: &str, source: &str) -> Result<Vec<MutualRecGroup>> {
    let mut groups = Vec::new();

    // Split into mutual recursion groups (type ... and ... and ...)
    let type_groups = split_type_blocks_grouped(content);

    for group_blocks in type_groups {
        let mut group_types = Vec::new();
        for block in group_blocks {
            if let Some(ty) = parse_single_type_def(&block)? {
                group_types.push(ty);
            }
        }
        if !group_types.is_empty() {
            groups.push(MutualRecGroup::new(group_types, source));
        }
    }

    Ok(groups)
}

/// Split content into groups of mutually recursive type definitions.
/// Each group is a Vec of individual type definition strings.
/// Types connected by `and` are kept together in the same group.
fn split_type_blocks_grouped(content: &str) -> Vec<Vec<String>> {
    let mut groups: Vec<Vec<String>> = Vec::new();
    let mut current_group: Vec<String> = Vec::new();
    let mut current_block = String::new();
    let mut in_type_def = false;
    let mut brace_depth: i32 = 0;
    let mut paren_depth: i32 = 0;

    // Remove comments first to avoid confusion
    let content = remove_ocaml_comments(content);

    for line in content.lines() {
        let trimmed = line.trim();

        // Skip empty lines in comment detection
        if trimmed.is_empty() && !in_type_def {
            continue;
        }

        // Track brace/paren depth for multi-line definitions
        let (new_brace, new_paren) = count_delimiters(trimmed);
        brace_depth += new_brace;
        paren_depth += new_paren;

        // Start of a new type block (not preceded by 'and')
        if trimmed.starts_with("type ") && brace_depth == 0 && paren_depth == 0 {
            // Finish previous group if any
            if !current_block.is_empty() {
                current_group.push(current_block.clone());
            }
            if !current_group.is_empty() {
                groups.push(current_group);
                current_group = Vec::new();
            }
            current_block = line.to_string();
            in_type_def = true;
        }
        // Continuation with 'and' keyword - stays in same mutual recursion group
        else if trimmed.starts_with("and ") && in_type_def && brace_depth == 0 && paren_depth == 0
        {
            // Save current block to current group
            if !current_block.is_empty() {
                current_group.push(current_block.clone());
            }
            // Start new block but keep in same group
            // Convert 'and' to 'type' for uniform parsing
            current_block = format!("type {}", &trimmed[4..]);
        }
        // Continue current block
        else if in_type_def {
            // Check if this line ends the type definition
            if trimmed.is_empty() && brace_depth == 0 && paren_depth == 0 {
                if !current_block.is_empty() {
                    current_group.push(current_block.clone());
                    current_block.clear();
                }
                if !current_group.is_empty() {
                    groups.push(current_group);
                    current_group = Vec::new();
                }
                in_type_def = false;
            } else {
                current_block.push('\n');
                current_block.push_str(line);
            }
        }
    }

    // Don't forget the last block/group
    if !current_block.is_empty() {
        current_group.push(current_block);
    }
    if !current_group.is_empty() {
        groups.push(current_group);
    }

    groups
}

/// Remove OCaml comments from source
fn remove_ocaml_comments(content: &str) -> String {
    let mut result = String::new();
    let mut depth = 0;
    let mut chars = content.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '(' && chars.peek() == Some(&'*') {
            chars.next(); // consume '*'
            depth += 1;
        } else if c == '*' && chars.peek() == Some(&')') && depth > 0 {
            chars.next(); // consume ')'
            depth -= 1;
        } else if depth == 0 {
            result.push(c);
        }
    }

    result
}

/// Count brace and paren delimiters in a line (returns net change)
fn count_delimiters(line: &str) -> (i32, i32) {
    let mut brace = 0i32;
    let mut paren = 0i32;
    let mut in_string = false;

    for c in line.chars() {
        match c {
            '"' => in_string = !in_string,
            '{' if !in_string => brace += 1,
            '}' if !in_string => brace -= 1,
            '(' if !in_string => paren += 1,
            ')' if !in_string => paren -= 1,
            _ => {}
        }
    }

    (brace, paren)
}

/// Deduplicate groups, keeping the first occurrence of each type name
fn deduplicate_groups(groups: Vec<MutualRecGroup>) -> Vec<MutualRecGroup> {
    let mut seen_names: HashSet<String> = HashSet::new();
    let mut result = Vec::new();

    for group in groups {
        let filtered_types: Vec<OcamlType> = group
            .types
            .into_iter()
            .filter(|ty| {
                let name = ty.name().to_string();
                if seen_names.contains(&name) {
                    false
                } else {
                    seen_names.insert(name);
                    true
                }
            })
            .collect();

        if !filtered_types.is_empty() {
            result.push(MutualRecGroup::new(filtered_types, &group.source));
        }
    }

    result
}

/// Merge groups that have cyclic dependencies between them
fn merge_cyclic_groups(groups: Vec<MutualRecGroup>) -> Vec<MutualRecGroup> {
    if groups.is_empty() {
        return groups;
    }

    // Build a map from type name to group index
    let mut name_to_group: HashMap<String, usize> = HashMap::new();
    for (i, group) in groups.iter().enumerate() {
        for ty in &group.types {
            name_to_group.insert(ty.name().to_string(), i);
        }
    }

    // Build dependency graph between groups
    let n = groups.len();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];

    for (i, group) in groups.iter().enumerate() {
        let mut deps: HashSet<usize> = HashSet::new();
        for ty in &group.types {
            for dep in ty.dependencies() {
                if let Some(&dep_group) = name_to_group.get(&dep) {
                    if dep_group != i {
                        deps.insert(dep_group);
                    }
                }
            }
        }
        adj[i] = deps.into_iter().collect();
    }

    // Find strongly connected components using Tarjan's algorithm
    let sccs = tarjan_scc(&adj);

    // Merge groups in same SCC
    let mut result = Vec::new();
    for scc in sccs {
        if scc.len() == 1 {
            result.push(groups[scc[0]].clone());
        } else {
            // Merge all groups in this SCC
            let mut merged_types = Vec::new();
            let mut source = String::new();
            for &idx in &scc {
                merged_types.extend(groups[idx].types.clone());
                if source.is_empty() {
                    source = groups[idx].source.clone();
                } else {
                    source = format!("{} + {}", source, groups[idx].source);
                }
            }
            result.push(MutualRecGroup::new(merged_types, &source));
        }
    }

    result
}

/// Tarjan's algorithm for finding strongly connected components
fn tarjan_scc(adj: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let n = adj.len();
    let mut index_counter = 0;
    let mut indices: Vec<Option<usize>> = vec![None; n];
    let mut lowlinks: Vec<usize> = vec![0; n];
    let mut on_stack: Vec<bool> = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut sccs: Vec<Vec<usize>> = Vec::new();

    fn strongconnect(
        v: usize,
        adj: &[Vec<usize>],
        index_counter: &mut usize,
        indices: &mut Vec<Option<usize>>,
        lowlinks: &mut Vec<usize>,
        on_stack: &mut Vec<bool>,
        stack: &mut Vec<usize>,
        sccs: &mut Vec<Vec<usize>>,
    ) {
        indices[v] = Some(*index_counter);
        lowlinks[v] = *index_counter;
        *index_counter += 1;
        stack.push(v);
        on_stack[v] = true;

        for &w in &adj[v] {
            if indices[w].is_none() {
                strongconnect(
                    w,
                    adj,
                    index_counter,
                    indices,
                    lowlinks,
                    on_stack,
                    stack,
                    sccs,
                );
                lowlinks[v] = lowlinks[v].min(lowlinks[w]);
            } else if on_stack[w] {
                lowlinks[v] = lowlinks[v].min(indices[w].unwrap());
            }
        }

        if lowlinks[v] == indices[v].unwrap() {
            let mut scc = Vec::new();
            loop {
                let w = stack.pop().unwrap();
                on_stack[w] = false;
                scc.push(w);
                if w == v {
                    break;
                }
            }
            sccs.push(scc);
        }
    }

    for v in 0..n {
        if indices[v].is_none() {
            strongconnect(
                v,
                adj,
                &mut index_counter,
                &mut indices,
                &mut lowlinks,
                &mut on_stack,
                &mut stack,
                &mut sccs,
            );
        }
    }

    // Reverse to get topological order
    sccs.reverse();
    sccs
}

/// Topologically sort groups based on dependencies
fn topological_sort_groups(groups: Vec<MutualRecGroup>) -> Vec<MutualRecGroup> {
    if groups.is_empty() {
        return groups;
    }

    // Build a map from type name to group index
    let mut name_to_group: HashMap<String, usize> = HashMap::new();
    for (i, group) in groups.iter().enumerate() {
        for ty in &group.types {
            name_to_group.insert(ty.name().to_string(), i);
        }
    }

    // Build dependency graph
    let n = groups.len();
    let mut in_degree: Vec<usize> = vec![0; n];
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];

    for (i, group) in groups.iter().enumerate() {
        let mut deps: HashSet<usize> = HashSet::new();
        for ty in &group.types {
            for dep in ty.dependencies() {
                if let Some(&dep_group) = name_to_group.get(&dep) {
                    if dep_group != i && !deps.contains(&dep_group) {
                        deps.insert(dep_group);
                        adj[dep_group].push(i);
                        in_degree[i] += 1;
                    }
                }
            }
        }
    }

    // Kahn's algorithm
    let mut queue: Vec<usize> = (0..n).filter(|&i| in_degree[i] == 0).collect();
    let mut result = Vec::new();

    while let Some(idx) = queue.pop() {
        result.push(groups[idx].clone());
        for &next in &adj[idx] {
            in_degree[next] -= 1;
            if in_degree[next] == 0 {
                queue.push(next);
            }
        }
    }

    // Add any remaining (cyclic) groups
    for group in groups.iter() {
        if !result.iter().any(|g: &MutualRecGroup| {
            g.types
                .iter()
                .any(|t| group.types.iter().any(|t2| t.name() == t2.name()))
        }) {
            result.push(group.clone());
        }
    }

    result
}

/// Parse a single type definition
fn parse_single_type_def(block: &str) -> Result<Option<OcamlType>> {
    let block = block.trim();

    // Skip empty blocks and comments
    if block.is_empty() || block.starts_with("(*") {
        return Ok(None);
    }

    // Pattern for type name extraction
    let name_re = Regex::new(r"^type\s+(\w+)")?;
    let name = match name_re.captures(block) {
        Some(cap) => cap[1].to_string(),
        None => return Ok(None),
    };

    // Skip module/functor related definitions
    if block.contains("module") || block.contains("struct") || block.contains("functor") {
        return Ok(None);
    }

    // Check for record type: type name = { ... }
    let record_re = Regex::new(r"type\s+\w+\s*=\s*\{([^}]+)\}")?;
    if let Some(cap) = record_re.captures(block) {
        let body = &cap[1];
        let field_re = Regex::new(r"(mutable\s+)?(\w+)\s*:\s*([^;]+)")?;
        let mut fields = Vec::new();

        for field_cap in field_re.captures_iter(body) {
            let mutable = field_cap.get(1).is_some();
            let field_name = field_cap[2].to_string();
            let field_ty = field_cap[3].trim().to_string();
            fields.push(RecordField {
                name: field_name,
                ty: clean_type_ref(&field_ty),
                mutable,
            });
        }

        if !fields.is_empty() {
            return Ok(Some(OcamlType::Record { name, fields }));
        }
    }

    // Check for simple alias: type name = existing_type (single word, no |)
    let alias_re = Regex::new(r"^type\s+\w+\s*=\s*(\w+)\s*$")?;
    if let Some(cap) = alias_re.captures(block) {
        let target = cap[1].to_string();
        return Ok(Some(OcamlType::Alias { name, target }));
    }

    // Check for variant type: type name = Variant1 | Variant2 of ... | ...
    // Look for '|' or constructor pattern
    let has_variants = block.contains('|') ||
        Regex::new(r"=\s*[A-Z]\w*(\s+of\s+|\s*$|\s*\|)")?.is_match(block);

    if has_variants {
        // Extract everything after the '='
        let body_re = Regex::new(r"type\s+\w+\s*=\s*([\s\S]+)")?;
        if let Some(cap) = body_re.captures(block) {
            let body = &cap[1];

            // Parse individual variants
            let variant_re = Regex::new(r"\|?\s*([A-Z]\w*)(?:\s+of\s+([^|]+))?")?;
            let mut variants = Vec::new();

            for var_cap in variant_re.captures_iter(body) {
                let var_name = var_cap[1].to_string();

                // Skip if it looks like a type name in a complex expression
                if var_name == "Some" || var_name == "None" || var_name == "T" {
                    continue;
                }

                let args = if let Some(args_match) = var_cap.get(2) {
                    parse_type_args(args_match.as_str().trim())
                } else {
                    vec![]
                };

                variants.push(VariantCase {
                    name: var_name,
                    args,
                });
            }

            if !variants.is_empty() {
                return Ok(Some(OcamlType::Variant { name, variants }));
            }
        }
    }

    Ok(None)
}

/// Clean up type references
fn clean_type_ref(ty: &str) -> String {
    ty.trim()
        .trim_end_matches(';')
        .trim()
        .to_string()
}

/// Parse type arguments from OCaml "of" clause
fn parse_type_args(args: &str) -> Vec<String> {
    // Simple parsing: split by '*' for tuples
    args.split('*')
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .collect()
}

/// Generate Rocq code from sorted groups, handling mutual recursion
fn generate_rocq_from_groups(groups: &[MutualRecGroup]) -> Result<String> {
    let mut output = String::new();

    // Header
    output.push_str(
        r#"(* =========================================================================
   WebAssembly Specification - Auto-generated from reference interpreter

   DO NOT EDIT MANUALLY - Generated by spec-sync tool
   Source: WebAssembly/spec interpreter/syntax/{types.ml, ast.ml}

   To regenerate:
     bazel run //tools/spec-sync -- --spec-dir <path> --output <output.v>

   This file handles mutual recursion using Rocq's "with" syntax.
   ========================================================================= *)

From Stdlib Require Import List ZArith Bool.
Import ListNotations.

(* Placeholder for strings - using nat for simplicity *)
Definition wasm_string := nat.

"#,
    );

    // Type mappings from OCaml to Rocq
    let type_map: HashMap<&str, &str> = [
        ("int32", "nat"),
        ("int64", "nat"),
        ("int", "nat"),
        ("bool", "bool"),
        ("string", "wasm_string"),
        ("unit", "unit"),
        ("float", "nat"), // Placeholder
        ("Utf8.unicode", "wasm_string"),
    ]
    .into_iter()
    .collect();

    // Generate each group
    for group in groups {
        if group.types.len() == 1 {
            // Single type - generate normally
            generate_single_type(&mut output, &group.types[0], &type_map);
        } else {
            // Mutual recursion group - use "with" syntax
            generate_mutual_rec_group(&mut output, group, &type_map);
        }
    }

    output.push_str("(* End of auto-generated definitions *)\n");

    Ok(output)
}

/// Generate a single type definition
fn generate_single_type(output: &mut String, ty: &OcamlType, type_map: &HashMap<&str, &str>) {
    match ty {
        OcamlType::Variant { name, variants } => {
            output.push_str(&format!(
                "(* {} *)\nInductive {} : Type :=\n",
                name,
                ocaml_to_rocq_name(name)
            ));
            for var in variants {
                let constructor = format!("{}_{}", ocaml_to_rocq_name(name), &var.name);
                if var.args.is_empty() {
                    output.push_str(&format!("  | {}\n", constructor));
                } else {
                    let args: Vec<String> = var
                        .args
                        .iter()
                        .map(|a| ocaml_type_to_rocq(a, type_map))
                        .collect();
                    output.push_str(&format!(
                        "  | {} ({})\n",
                        constructor,
                        args.iter()
                            .enumerate()
                            .map(|(i, t)| format!("arg{} : {}", i, t))
                            .collect::<Vec<_>>()
                            .join(") (")
                    ));
                }
            }
            output.push_str(".\n\n");
        }
        OcamlType::Record { name, fields } => {
            output.push_str(&format!(
                "(* {} *)\nRecord {} : Type := mk{} {{\n",
                name,
                ocaml_to_rocq_name(name),
                ocaml_to_rocq_name(name)
            ));
            for field in fields {
                let field_ty = ocaml_type_to_rocq(&field.ty, type_map);
                output.push_str(&format!(
                    "  {}_{} : {};\n",
                    ocaml_to_rocq_name(name),
                    &field.name,
                    field_ty
                ));
            }
            output.push_str("}.\n\n");
        }
        OcamlType::Alias { name, target } => {
            let target_ty = ocaml_type_to_rocq(target, type_map);
            output.push_str(&format!(
                "(* {} *)\nDefinition {} := {}.\n\n",
                name,
                ocaml_to_rocq_name(name),
                target_ty
            ));
        }
    }
}

/// Generate mutually recursive type definitions using Rocq "with" syntax
fn generate_mutual_rec_group(
    output: &mut String,
    group: &MutualRecGroup,
    type_map: &HashMap<&str, &str>,
) {
    // Collect type names for the comment
    let type_names: Vec<&str> = group.types.iter().map(|t| t.name()).collect();
    output.push_str(&format!(
        "(* Mutually recursive types: {} *)\n",
        type_names.join(", ")
    ));

    // Separate into inductives and others (records/aliases must be handled separately)
    let (inductives, others): (Vec<_>, Vec<_>) = group
        .types
        .iter()
        .partition(|t| matches!(t, OcamlType::Variant { .. }));

    // Generate mutually recursive inductives with "with"
    if !inductives.is_empty() {
        for (i, ty) in inductives.iter().enumerate() {
            if let OcamlType::Variant { name, variants } = ty {
                let keyword = if i == 0 { "Inductive" } else { "with" };
                output.push_str(&format!(
                    "{} {} : Type :=\n",
                    keyword,
                    ocaml_to_rocq_name(name)
                ));
                for var in variants {
                    let constructor = format!("{}_{}", ocaml_to_rocq_name(name), &var.name);
                    if var.args.is_empty() {
                        output.push_str(&format!("  | {}\n", constructor));
                    } else {
                        let args: Vec<String> = var
                            .args
                            .iter()
                            .map(|a| ocaml_type_to_rocq(a, type_map))
                            .collect();
                        output.push_str(&format!(
                            "  | {} ({})\n",
                            constructor,
                            args.iter()
                                .enumerate()
                                .map(|(i, t)| format!("arg{} : {}", i, t))
                                .collect::<Vec<_>>()
                                .join(") (")
                        ));
                    }
                }
            }
        }
        output.push_str(".\n\n");
    }

    // Generate records and aliases separately (they can't use "with" in Rocq)
    // For records in mutual recursion, we need to use a workaround
    for ty in others {
        match ty {
            OcamlType::Record { name, fields } => {
                // Records in mutual recursion need special handling in Rocq
                // We can use a wrapper inductive or just define them after
                output.push_str(&format!(
                    "(* Note: {} is part of mutual recursion but records require separate definition *)\n",
                    name
                ));
                output.push_str(&format!(
                    "Record {} : Type := mk{} {{\n",
                    ocaml_to_rocq_name(name),
                    ocaml_to_rocq_name(name)
                ));
                for field in fields {
                    let field_ty = ocaml_type_to_rocq(&field.ty, type_map);
                    output.push_str(&format!(
                        "  {}_{} : {};\n",
                        ocaml_to_rocq_name(name),
                        &field.name,
                        field_ty
                    ));
                }
                output.push_str("}.\n\n");
            }
            OcamlType::Alias { name, target } => {
                let target_ty = ocaml_type_to_rocq(target, type_map);
                output.push_str(&format!(
                    "Definition {} := {}.\n\n",
                    ocaml_to_rocq_name(name),
                    target_ty
                ));
            }
            _ => {}
        }
    }
}

/// Convert OCaml name to Rocq-compatible name
fn ocaml_to_rocq_name(name: &str) -> String {
    // Handle common patterns
    let name = name
        .replace("type", "wasm_type")
        .replace("'", "_prime");

    // Capitalize first letter for types
    let mut chars: Vec<char> = name.chars().collect();
    if let Some(c) = chars.first_mut() {
        *c = c.to_ascii_uppercase();
    }
    chars.into_iter().collect()
}

/// Convert OCaml type to Rocq type
fn ocaml_type_to_rocq(ty: &str, type_map: &HashMap<&str, &str>) -> String {
    let ty = ty.trim();

    // Check direct mapping
    if let Some(&mapped) = type_map.get(ty) {
        return mapped.to_string();
    }

    // Handle option types: t option -> option t
    if ty.ends_with(" option") {
        let inner = ty.trim_end_matches(" option").trim();
        return format!("option ({})", ocaml_type_to_rocq(inner, type_map));
    }

    // Handle list types: t list -> list t
    if ty.ends_with(" list") {
        let inner = ty.trim_end_matches(" list").trim();
        return format!("list ({})", ocaml_type_to_rocq(inner, type_map));
    }

    // Handle tuple types: t1 * t2 -> (t1 * t2)
    if ty.contains(" * ") {
        let parts: Vec<&str> = ty.split(" * ").collect();
        let converted: Vec<String> = parts
            .iter()
            .map(|p| ocaml_type_to_rocq(p.trim(), type_map))
            .collect();
        return format!("({})", converted.join(" * "));
    }

    // Default: convert name
    ocaml_to_rocq_name(ty)
}

/// Get git commit from spec directory
fn get_git_commit(spec_dir: &PathBuf) -> Result<String> {
    let output = std::process::Command::new("git")
        .args(["rev-parse", "HEAD"])
        .current_dir(spec_dir)
        .output();

    match output {
        Ok(o) if o.status.success() => {
            Ok(String::from_utf8_lossy(&o.stdout).trim().to_string())
        }
        _ => Ok("unknown".to_string()),
    }
}

/// Simple timestamp without chrono dependency
fn chrono_lite_now() -> String {
    use std::time::{SystemTime, UNIX_EPOCH};
    let duration = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    format!("{}", duration.as_secs())
}

/// Simple hash for change detection
fn simple_hash(content: &str) -> String {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut hasher = DefaultHasher::new();
    content.hash(&mut hasher);
    format!("{:016x}", hasher.finish())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper to get types from groups
    fn get_all_types(groups: &[MutualRecGroup]) -> Vec<&OcamlType> {
        groups.iter().flat_map(|g| g.types.iter()).collect()
    }

    #[test]
    fn test_parse_simple_variant() {
        let content = r#"
type numtype = I32T | I64T | F32T | F64T
"#;
        let groups = parse_ocaml_types_grouped(content, "test").unwrap();
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].types.len(), 1);
        match &groups[0].types[0] {
            OcamlType::Variant { name, variants } => {
                assert_eq!(name, "numtype");
                assert_eq!(variants.len(), 4);
                assert_eq!(variants[0].name, "I32T");
            }
            _ => panic!("Expected variant"),
        }
    }

    #[test]
    fn test_parse_variant_with_args() {
        let content = r#"
type valtype = NumT of numtype | VecT of vectype | RefT of reftype | BotT
"#;
        let groups = parse_ocaml_types_grouped(content, "test").unwrap();
        assert_eq!(groups.len(), 1);
        match &groups[0].types[0] {
            OcamlType::Variant { name, variants } => {
                assert_eq!(name, "valtype");
                assert_eq!(variants.len(), 4);
                assert_eq!(variants[0].name, "NumT");
                assert_eq!(variants[0].args, vec!["numtype"]);
            }
            _ => panic!("Expected variant"),
        }
    }

    #[test]
    fn test_parse_record() {
        let content = r#"
type limits = {min : int64; max : int64 option}
"#;
        let groups = parse_ocaml_types_grouped(content, "test").unwrap();
        assert_eq!(groups.len(), 1);
        match &groups[0].types[0] {
            OcamlType::Record { name, fields } => {
                assert_eq!(name, "limits");
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].name, "min");
                assert_eq!(fields[0].ty, "int64");
            }
            _ => panic!("Expected record"),
        }
    }

    #[test]
    fn test_parse_mutual_recursion() {
        let content = r#"
type tree = Leaf | Node of tree * forest
and forest = Empty | Trees of tree * forest
"#;
        let groups = parse_ocaml_types_grouped(content, "test").unwrap();
        // Should be in same group due to 'and' keyword
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].types.len(), 2);

        let type_names: Vec<&str> = groups[0].types.iter().map(|t| t.name()).collect();
        assert!(type_names.contains(&"tree"));
        assert!(type_names.contains(&"forest"));
    }

    #[test]
    fn test_mutual_recursion_rocq_generation() {
        let content = r#"
type tree = Leaf | Node of forest
and forest = Empty | Trees of tree
"#;
        let groups = parse_ocaml_types_grouped(content, "test").unwrap();
        let rocq = generate_rocq_from_groups(&groups).unwrap();

        // Should contain "with" for mutual recursion
        assert!(rocq.contains("with Forest"));
        assert!(rocq.contains("Inductive Tree"));
        // Should not have two separate "Inductive" declarations for these
        assert_eq!(rocq.matches("Inductive Tree").count(), 1);
        assert!(!rocq.contains("Inductive Forest")); // Forest uses "with"
    }

    #[test]
    fn test_deduplication() {
        let content1 = "type foo = A | B\n";
        let content2 = "type foo = C | D\n"; // Duplicate name

        let mut groups = Vec::new();
        groups.extend(parse_ocaml_types_grouped(content1, "file1").unwrap());
        groups.extend(parse_ocaml_types_grouped(content2, "file2").unwrap());

        let deduped = deduplicate_groups(groups);

        // Should only have one "foo"
        let all_types = get_all_types(&deduped);
        let foo_count = all_types.iter().filter(|t| t.name() == "foo").count();
        assert_eq!(foo_count, 1);

        // Should be the first one (A | B)
        match all_types.iter().find(|t| t.name() == "foo").unwrap() {
            OcamlType::Variant { variants, .. } => {
                assert_eq!(variants[0].name, "A");
            }
            _ => panic!("Expected variant"),
        }
    }

    #[test]
    fn test_cycle_detection() {
        // Two separate type blocks that reference each other
        let content = r#"
type alpha = Beta of beta

type beta = Alpha of alpha
"#;
        let groups = parse_ocaml_types_grouped(content, "test").unwrap();
        // Initially separate groups
        assert_eq!(groups.len(), 2);

        // After merging cycles, should be one group
        let merged = merge_cyclic_groups(groups);
        assert_eq!(merged.len(), 1);
        assert_eq!(merged[0].types.len(), 2);
    }

    #[test]
    fn test_topological_sort() {
        let content = r#"
type c = B of b

type b = A of a

type a = Leaf
"#;
        let groups = parse_ocaml_types_grouped(content, "test").unwrap();
        let sorted = topological_sort_groups(groups);

        // 'a' should come first, then 'b', then 'c'
        let names: Vec<&str> = sorted.iter().flat_map(|g| g.type_names()).collect();
        let a_pos = names.iter().position(|&n| n == "a").unwrap();
        let b_pos = names.iter().position(|&n| n == "b").unwrap();
        let c_pos = names.iter().position(|&n| n == "c").unwrap();

        assert!(a_pos < b_pos);
        assert!(b_pos < c_pos);
    }

    #[test]
    fn test_extract_type_refs() {
        assert_eq!(extract_type_refs("foo"), vec!["foo"]);
        assert_eq!(extract_type_refs("foo option"), vec!["foo"]);
        assert_eq!(extract_type_refs("foo list"), vec!["foo"]);
        assert_eq!(
            extract_type_refs("foo * bar"),
            vec!["foo".to_string(), "bar".to_string()]
        );
        assert!(extract_type_refs("int").is_empty());
        assert!(extract_type_refs("int32").is_empty());
    }

    #[test]
    fn test_remove_ocaml_comments() {
        let input = "type foo = (* comment *) A | B";
        let result = remove_ocaml_comments(input);
        assert_eq!(result, "type foo =  A | B");

        let nested = "type foo = (* outer (* inner *) *) A";
        let result = remove_ocaml_comments(nested);
        assert_eq!(result, "type foo =  A");
    }
}
