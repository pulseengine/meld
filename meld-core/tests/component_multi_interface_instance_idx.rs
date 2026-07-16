//! Regression for the interface-export instance-index desync surfaced by the
//! #355 Mythos pass: a component exporting ≥2 interfaces bound the 2nd and later
//! interface exports to the *previous* interface's export-alias instance, so
//! they silently exported the wrong functions. The output still validated, so it
//! was silent (UCA-CP-1). Fix: advance `component_instance_idx` by 2 per
//! exported interface (the synthetic instance + the export-alias it binds).

use meld_core::{Fuser, FuserConfig, OutputFormat};
use wasmparser::*;

const TWO_IFACE: &str = r#"(component
  (core module $main
    (type (;0;) (func (param i32) (result i32)))
    (type (;1;) (func (result i32)))
    (memory (;0;) 2) (global (;0;) (mut i32) i32.const 65536)
    (export "memory" (memory 0)) (export "__stack_pointer" (global 0))
    (export "a:p/one#fa" (func $fa)) (export "b:p/two#fb" (func $fb))
    (func $fa (type 0) (param i32) (result i32) local.get 0)
    (func $fb (type 1) (result i32) i32.const 7))
  (core instance $main (;0;) (instantiate $main))
  (alias core export $main "memory" (core memory (;0;)))
  (type (;0;) (func (param "x" s32) (result u32)))
  (alias core export $main "a:p/one#fa" (core func (;0;)))
  (func (;0;) (type 0) (canon lift (core func 0)))
  (instance (;0;) (export "fa" (func 0)))
  (export (;1;) "a:p/one" (instance 0))
  (type (;1;) (func (result u32)))
  (alias core export $main "b:p/two#fb" (core func (;1;)))
  (func (;1;) (type 1) (canon lift (core func 1)))
  (instance (;2;) (export "fb" (func 1)))
  (export (;3;) "b:p/two" (instance 2)))"#;

#[test]
fn multi_interface_exports_reference_their_own_instance() {
    let input = wat::parse_str(TWO_IFACE).unwrap();
    let config = FuserConfig {
        output_format: OutputFormat::Component,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    fuser
        .add_component_named(&input, Some("two_iface.wasm"))
        .unwrap();
    let out = fuser.fuse().expect("fuse --component");

    // The bug is SILENT — the output validates either way.
    Validator::new_with_features(WasmFeatures::all())
        .validate_all(&out)
        .expect("output validates");

    // Resolve each exported interface instance → the func names it provides.
    let mut instance_funcs: std::collections::HashMap<u32, std::collections::BTreeSet<String>> =
        Default::default();
    let mut next_instance = 0u32;
    let mut iface_exports: Vec<(String, u32)> = Vec::new();
    for payload in Parser::new(0).parse_all(&out) {
        match payload.unwrap() {
            Payload::ComponentInstanceSection(r) => {
                for inst in r {
                    if let ComponentInstance::FromExports(exs) = inst.unwrap() {
                        let names = exs
                            .iter()
                            .filter(|e| e.kind == ComponentExternalKind::Func)
                            .map(|e| e.name.0.to_string())
                            .collect();
                        instance_funcs.insert(next_instance, names);
                    }
                    next_instance += 1;
                }
            }
            Payload::ComponentExportSection(r) => {
                for e in r {
                    let e = e.unwrap();
                    if e.kind == ComponentExternalKind::Instance {
                        iface_exports.push((e.name.0.to_string(), e.index));
                        next_instance += 1; // an instance export binds a new instance index
                    }
                }
            }
            _ => {}
        }
    }
    let funcs = |name: &str| {
        iface_exports
            .iter()
            .find(|(n, _)| n == name)
            .and_then(|(_, i)| instance_funcs.get(i))
            .cloned()
            .unwrap_or_default()
    };

    assert!(funcs("a:p/one").contains("fa"), "a:p/one must export fa");
    assert!(
        funcs("b:p/two").contains("fb"),
        "b:p/two must export its OWN fb, got {:?} (index-desync would export a:p/one's fa)",
        funcs("b:p/two")
    );
}
