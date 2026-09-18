(module
  (memory (export "memory") 1)
  ;; The params-ptr convention needs the CALLEE's allocator: over
  ;; MAX_FLAT_PARAMS the caller stores the argument tuple in the callee's
  ;; memory, allocated through this. `wasm-tools component new` refuses the
  ;; module without it, which is the tooling stating the same requirement.
  (global $bump (mut i32) (i32.const 1024))
  (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
    (local $p i32)
    (local.set $p (global.get $bump))
    (global.set $bump (i32.add (local.get $p) (local.get 3)))
    (local.get $p))
  ;; tick(state, setpoint) -> out
  ;;
  ;; 18 flattened params is over MAX_FLAT_PARAMS, so the params arrive through
  ;; a pointer: state.f1..f14 at +0..+52, setpoint.r1..r4 at +56..+68.
  ;; Return area at 256.
  ;;   o1 = sum(state)   o2 = sum(setpoint)   o3 = state.f1   o4 = setpoint.r4
  (func (export "golden:wide/lib@0.1.0#tick") (param i32) (result i32)
    (local $sum f32)
    (local.set $sum (f32.const 0))
    (local.set $sum (f32.add (local.get $sum) (f32.load offset=0  (local.get 0))))
    (local.set $sum (f32.add (local.get $sum) (f32.load offset=4  (local.get 0))))
    (local.set $sum (f32.add (local.get $sum) (f32.load offset=8  (local.get 0))))
    (local.set $sum (f32.add (local.get $sum) (f32.load offset=12 (local.get 0))))
    (local.set $sum (f32.add (local.get $sum) (f32.load offset=16 (local.get 0))))
    (local.set $sum (f32.add (local.get $sum) (f32.load offset=20 (local.get 0))))
    (local.set $sum (f32.add (local.get $sum) (f32.load offset=24 (local.get 0))))
    (local.set $sum (f32.add (local.get $sum) (f32.load offset=28 (local.get 0))))
    (local.set $sum (f32.add (local.get $sum) (f32.load offset=32 (local.get 0))))
    (local.set $sum (f32.add (local.get $sum) (f32.load offset=36 (local.get 0))))
    (local.set $sum (f32.add (local.get $sum) (f32.load offset=40 (local.get 0))))
    (local.set $sum (f32.add (local.get $sum) (f32.load offset=44 (local.get 0))))
    (local.set $sum (f32.add (local.get $sum) (f32.load offset=48 (local.get 0))))
    (local.set $sum (f32.add (local.get $sum) (f32.load offset=52 (local.get 0))))
    (f32.store offset=0 (i32.const 256) (local.get $sum))
    (f32.store offset=4 (i32.const 256)
      (f32.add (f32.add (f32.load offset=56 (local.get 0)) (f32.load offset=60 (local.get 0)))
               (f32.add (f32.load offset=64 (local.get 0)) (f32.load offset=68 (local.get 0)))))
    (f32.store offset=8  (i32.const 256) (f32.load offset=0  (local.get 0)))
    (f32.store offset=12 (i32.const 256) (f32.load offset=68 (local.get 0)))
    (i32.const 256)))
