(module
  (import "golden:ctrl/lib@0.1.0" "tick" (func $tick (param f32 f32 i32)))
  (memory (export "memory") 1)
  ;; run() = tx + ty + tz + thrust for tick(3, 4) = 3 + 4 + 7 + 12 = 26
  (func (export "golden:recapp/runner@0.1.0#run") (result f32)
    (call $tick (f32.const 3) (f32.const 4) (i32.const 512))
    (f32.add
      (f32.add (f32.load offset=0 (i32.const 512)) (f32.load offset=4 (i32.const 512)))
      (f32.add (f32.load offset=8 (i32.const 512)) (f32.load offset=12 (i32.const 512))))))
