//! spec-sync: Generate Rocq specifications from WebAssembly spec reference interpreter
//!
//! This tool parses the OCaml type definitions from the WebAssembly spec's
//! reference interpreter and generates corresponding Rocq/Coq definitions.
//!
//! Usage:
//!   spec-sync --spec-dir <path-to-wasm-spec> --output <output.v>

use anyhow::{Context, Result};
use clap::Parser;
use regex::Regex;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
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
    mutable: bool,
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

    // Parse type definitions
    let mut types = Vec::new();
    types.extend(parse_ocaml_types(&types_content)?);
    types.extend(parse_ocaml_types(&ast_content)?);

    // Generate Rocq output
    let rocq_output = generate_rocq(&types)?;
    fs::write(&args.output, &rocq_output).context("Failed to write output")?;

    println!("Generated {} type definitions to {:?}", types.len(), args.output);

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

/// Parse OCaml type definitions from source
fn parse_ocaml_types(content: &str) -> Result<Vec<OcamlType>> {
    let mut types = Vec::new();

    // Pattern for simple type aliases: type name = target
    let alias_re = Regex::new(r"(?m)^type\s+(\w+)\s*=\s*(\w+)\s*$")?;

    // Pattern for variant types: type name = Variant1 | Variant2 of args | ...
    let variant_re = Regex::new(
        r"(?ms)^(?:and|type)\s+(\w+)\s*=\s*\n?((?:\s*\|?\s*\w+(?:\s+of\s+[^|]+)?\s*)+)"
    )?;

    // Pattern for record types: type name = { field1: type1; ... }
    let record_re = Regex::new(
        r"(?ms)^(?:and|type)\s+(\w+)\s*=\s*\{\s*([^}]+)\}"
    )?;

    // Parse variant types
    for cap in variant_re.captures_iter(content) {
        let name = cap[1].to_string();
        let body = &cap[2];

        // Skip if it's actually a record (contains '{')
        if body.contains('{') {
            continue;
        }

        // Parse variants
        let variant_case_re = Regex::new(r"\|?\s*(\w+)(?:\s+of\s+([^|]+))?")?;
        let mut variants = Vec::new();

        for var_cap in variant_case_re.captures_iter(body) {
            let var_name = var_cap[1].to_string();
            let args = if let Some(args_match) = var_cap.get(2) {
                parse_type_args(args_match.as_str())
            } else {
                vec![]
            };
            variants.push(VariantCase {
                name: var_name,
                args,
            });
        }

        if !variants.is_empty() {
            types.push(OcamlType::Variant { name, variants });
        }
    }

    // Parse record types
    for cap in record_re.captures_iter(content) {
        let name = cap[1].to_string();
        let body = &cap[2];

        let field_re = Regex::new(r"(mutable\s+)?(\w+)\s*:\s*([^;]+)")?;
        let mut fields = Vec::new();

        for field_cap in field_re.captures_iter(body) {
            let mutable = field_cap.get(1).is_some();
            let field_name = field_cap[2].to_string();
            let field_ty = field_cap[3].trim().to_string();
            fields.push(RecordField {
                name: field_name,
                ty: field_ty,
                mutable,
            });
        }

        if !fields.is_empty() {
            types.push(OcamlType::Record { name, fields });
        }
    }

    // Parse simple aliases
    for cap in alias_re.captures_iter(content) {
        let name = cap[1].to_string();
        let target = cap[2].to_string();

        // Skip if already captured as variant/record
        if !types.iter().any(|t| match t {
            OcamlType::Variant { name: n, .. }
            | OcamlType::Record { name: n, .. }
            | OcamlType::Alias { name: n, .. } => n == &name,
        }) {
            types.push(OcamlType::Alias { name, target });
        }
    }

    Ok(types)
}

/// Parse type arguments from OCaml "of" clause
fn parse_type_args(args: &str) -> Vec<String> {
    // Simple parsing: split by '*' for tuples
    args.split('*')
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .collect()
}

/// Generate Rocq code from parsed types
fn generate_rocq(types: &[OcamlType]) -> Result<String> {
    let mut output = String::new();

    // Header
    output.push_str(r#"(* =========================================================================
   WebAssembly Specification - Auto-generated from reference interpreter

   DO NOT EDIT MANUALLY - Generated by spec-sync tool
   Source: WebAssembly/spec interpreter/syntax/{types.ml, ast.ml}

   To regenerate:
     bazel run //tools/spec-sync -- --spec-dir <path> --output <output.v>
   ========================================================================= *)

From Stdlib Require Import List ZArith Bool.
Import ListNotations.

(* Placeholder for strings - using nat for simplicity *)
Definition wasm_string := nat.

"#);

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

    // Generate each type
    for ty in types {
        match ty {
            OcamlType::Variant { name, variants } => {
                output.push_str(&format!(
                    "(* {} *)\nInductive {} : Type :=\n",
                    name,
                    ocaml_to_rocq_name(name)
                ));
                for (i, var) in variants.iter().enumerate() {
                    let constructor = format!("{}_{}", ocaml_to_rocq_name(name), &var.name);
                    if var.args.is_empty() {
                        output.push_str(&format!("  | {}\n", constructor));
                    } else {
                        let args: Vec<String> = var
                            .args
                            .iter()
                            .map(|a| ocaml_type_to_rocq(a, &type_map))
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
                    let field_ty = ocaml_type_to_rocq(&field.ty, &type_map);
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
                let target_ty = ocaml_type_to_rocq(target, &type_map);
                output.push_str(&format!(
                    "(* {} *)\nDefinition {} := {}.\n\n",
                    name,
                    ocaml_to_rocq_name(name),
                    target_ty
                ));
            }
        }
    }

    output.push_str("(* End of auto-generated definitions *)\n");

    Ok(output)
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

    #[test]
    fn test_parse_simple_variant() {
        let content = r#"
type numtype = I32T | I64T | F32T | F64T
"#;
        let types = parse_ocaml_types(content).unwrap();
        assert_eq!(types.len(), 1);
        match &types[0] {
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
        let types = parse_ocaml_types(content).unwrap();
        assert_eq!(types.len(), 1);
        match &types[0] {
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
        let types = parse_ocaml_types(content).unwrap();
        assert_eq!(types.len(), 1);
        match &types[0] {
            OcamlType::Record { name, fields } => {
                assert_eq!(name, "limits");
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].name, "min");
                assert_eq!(fields[0].ty, "int64");
            }
            _ => panic!("Expected record"),
        }
    }
}
