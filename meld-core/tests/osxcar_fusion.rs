//! Integration test for OSxCAR anti-pinch component fusion.
//!
//! Verifies that the three osxcar components (anti_pinch_v2, motor_driver_v2,
//! soft_start_stop) can be individually fused and fused together as a group.
//! These are real-world automotive components from the OSxCAR project.

use meld_core::{Fuser, FuserConfig, MemoryStrategy, OutputFormat};

const COMPOSED_DIR: &str = "../tests/osxcar/composed";

fn component_path(name: &str) -> String {
    format!("{COMPOSED_DIR}/{name}.component.wasm")
}

fn component_exists(name: &str) -> bool {
    let path = component_path(name);
    if std::path::Path::new(&path).is_file() {
        true
    } else {
        eprintln!("skipping: osxcar component not found at {path}");
        false
    }
}

fn fuse_components(
    names: &[&str],
    format: OutputFormat,
) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let config = FuserConfig {
        memory_strategy: MemoryStrategy::MultiMemory,
        output_format: format,
        ..Default::default()
    };
    let mut fuser = Fuser::new(config);
    for name in names {
        let bytes = std::fs::read(component_path(name))?;
        fuser.add_component(&bytes)?;
    }
    Ok(fuser.fuse()?)
}

#[test]
fn test_osxcar_anti_pinch_fuses() {
    if !component_exists("anti_pinch_v2") {
        return;
    }
    let fused = fuse_components(&["anti_pinch_v2"], OutputFormat::CoreModule)
        .expect("anti_pinch_v2: fusion should succeed");
    assert!(
        fused.len() > 1000,
        "fused output too small: {} bytes",
        fused.len()
    );
    eprintln!("anti_pinch_v2 fused: {} bytes", fused.len());
}

#[test]
fn test_osxcar_motor_driver_fuses() {
    if !component_exists("motor_driver_v2") {
        return;
    }
    let fused = fuse_components(&["motor_driver_v2"], OutputFormat::CoreModule)
        .expect("motor_driver_v2: fusion should succeed");
    assert!(fused.len() > 500);
    eprintln!("motor_driver_v2 fused: {} bytes", fused.len());
}

#[test]
fn test_osxcar_soft_start_stop_fuses() {
    if !component_exists("soft_start_stop") {
        return;
    }
    let fused = fuse_components(&["soft_start_stop"], OutputFormat::CoreModule)
        .expect("soft_start_stop: fusion should succeed");
    assert!(fused.len() > 500);
    eprintln!("soft_start_stop fused: {} bytes", fused.len());
}

#[test]
fn test_osxcar_all_three_fuse_core_module() {
    for name in &["anti_pinch_v2", "motor_driver_v2", "soft_start_stop"] {
        if !component_exists(name) {
            return;
        }
    }
    let fused = fuse_components(
        &["anti_pinch_v2", "motor_driver_v2", "soft_start_stop"],
        OutputFormat::CoreModule,
    )
    .expect("all three osxcar components: core fusion should succeed");

    let input_size: usize = ["anti_pinch_v2", "motor_driver_v2", "soft_start_stop"]
        .iter()
        .map(|n| std::fs::read(component_path(n)).unwrap().len())
        .sum();
    eprintln!(
        "osxcar core fused: {} bytes (from {} bytes, {:.1}% reduction)",
        fused.len(),
        input_size,
        (1.0 - fused.len() as f64 / input_size as f64) * 100.0,
    );

    wasmparser::Validator::new()
        .validate_all(&fused)
        .expect("fused core module should be valid");
}

#[test]
fn test_osxcar_all_three_fuse_component() {
    for name in &["anti_pinch_v2", "motor_driver_v2", "soft_start_stop"] {
        if !component_exists(name) {
            return;
        }
    }
    let fused = fuse_components(
        &["anti_pinch_v2", "motor_driver_v2", "soft_start_stop"],
        OutputFormat::Component,
    )
    .expect("osxcar component fusion should succeed");
    eprintln!("osxcar P2 component: {} bytes", fused.len());

    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(&fused)
        .expect("fused component should be valid");
}
