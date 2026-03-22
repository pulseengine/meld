# OSxCAR Anti-Pinch Demo Components

WebAssembly components from the [OSxCAR project](https://osxcar.de/insights/demonstration/) —
an automotive research platform for software-defined vehicles using WebAssembly.

## Components

Three core WASM modules extracted from the osxcar.de interactive demonstration:

| Module | Interface | Description |
|--------|-----------|-------------|
| `anti_pinch_v2.wasm` | `aptiv:antipinch/anti-pinch-v2@0.1.0` | Pinch force detection via current measurement |
| `motor_driver_v2.wasm` | `aptiv:antipinch/motor-driver-v2@0.1.0` | Window motor simulation with realistic current |
| `soft_start_stop.wasm` | `aptiv:antipinch/soft-start-stop@0.1.0` | Smooth PWM ramp acceleration/deceleration |

Built with `wit-bindgen-c 0.46.0` and `wit-component 0.244.0`.

## Origin

These are core WASM modules produced by `jco` (JavaScript Component Output) transpilation
of original P2 component binaries. The JS glue code composes them at the browser level.

## Building Composed Components

To create a composed P2 component for meld testing:

```bash
# 1. Wrap each core module into a P2 component
wasm-tools component new fixtures/anti_pinch_v2.wasm -o anti_pinch_v2.component.wasm --wit wit/
wasm-tools component new fixtures/motor_driver_v2.wasm -o motor_driver_v2.component.wasm --wit wit/
wasm-tools component new fixtures/soft_start_stop.wasm -o soft_start_stop.component.wasm --wit wit/

# 2. Compose into a single component
wasm-tools compose -o osxcar_antipinch.wasm ...
```

## Cross-Tool Testing

These components serve as a real-world automotive test case across the PulseEngine toolchain:
- **meld**: Fuse composed components into a single core module
- **loom**: Optimize the fused output
- **synth + kiln**: Cross-compile WASM to ARM Cortex-M
- **gale**: Deploy to target ECU
