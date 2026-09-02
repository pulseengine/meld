(module
  (memory (export "memory") 1)
  ;; tick(a, b) -> torque{tx=a, ty=b, tz=a+b, thrust=a*b}
  ;; Return area lives at 256; the callee returns its address.
  (func (export "golden:ctrl/lib@0.1.0#tick") (param f32 f32) (result i32)
    (f32.store offset=0  (i32.const 256) (local.get 0))
    (f32.store offset=4  (i32.const 256) (local.get 1))
    (f32.store offset=8  (i32.const 256) (f32.add (local.get 0) (local.get 1)))
    (f32.store offset=12 (i32.const 256) (f32.mul (local.get 0) (local.get 1)))
    (i32.const 256)))
