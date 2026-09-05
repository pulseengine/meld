(module
  (memory (export "memory") 1)
  ;; tick(a,b) -> motor{a, b, a+b, a*b}; return area at 256.
  (func (export "golden:ctrl/lib@0.1.0#tick") (param f32 f32) (result i32)
    (f32.store offset=0  (i32.const 256) (local.get 0))
    (f32.store offset=4  (i32.const 256) (local.get 1))
    (f32.store offset=8  (i32.const 256) (f32.add (local.get 0) (local.get 1)))
    (f32.store offset=12 (i32.const 256) (f32.mul (local.get 0) (local.get 1)))
    (i32.const 256))
  ;; blend(torque) -> f32; 4 flat f32 params fit, so no indirection.
  (func (export "golden:ctrl/lib@0.1.0#blend") (param f32 f32 f32 f32) (result f32)
    (f32.add (f32.add (local.get 0) (local.get 1))
             (f32.add (local.get 2) (local.get 3))))
  ;; pack(seq,a) -> command{seq, torque{a, 2a, 3a, 4a}}; the NESTED record.
  ;; Layout: seq u32 @0, then torque @4..20. Return area at 320 (clear of 256).
  (func (export "golden:ctrl/lib@0.1.0#pack") (param i32 f32) (result i32)
    (i32.store offset=0  (i32.const 320) (local.get 0))
    (f32.store offset=4  (i32.const 320) (local.get 1))
    (f32.store offset=8  (i32.const 320) (f32.mul (local.get 1) (f32.const 2)))
    (f32.store offset=12 (i32.const 320) (f32.mul (local.get 1) (f32.const 3)))
    (f32.store offset=16 (i32.const 320) (f32.mul (local.get 1) (f32.const 4)))
    (i32.const 320)))
