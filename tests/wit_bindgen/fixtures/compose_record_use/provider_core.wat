(module
  (memory (export "memory") 1)
  ;; tick(a, b) -> motor{m1=a, m2=b, m3=a+b, m4=a*b}; returns the return-area ptr.
  (func (export "golden:ctrl/lib@0.1.0#tick") (param f32 f32) (result i32)
    (f32.store offset=0  (i32.const 256) (local.get 0))
    (f32.store offset=4  (i32.const 256) (local.get 1))
    (f32.store offset=8  (i32.const 256) (f32.add (local.get 0) (local.get 1)))
    (f32.store offset=12 (i32.const 256) (f32.mul (local.get 0) (local.get 1)))
    (i32.const 256))
  ;; blend(torque) -> f32; 4 flat f32 params fit, so no indirection here.
  (func (export "golden:ctrl/lib@0.1.0#blend") (param f32 f32 f32 f32) (result f32)
    (f32.add (f32.add (local.get 0) (local.get 1))
             (f32.add (local.get 2) (local.get 3)))))
