(module
  (import "golden:ctrl/lib@0.1.0" "tick" (func $tick (param f32 f32 i32)))
  (import "golden:ctrl/lib@0.1.0" "pack" (func $pack (param i32 f32 i32)))
  (memory (export "memory") 1)
  ;; run() = sum(tick(3,4)) + seq + sum(torque) of pack(5,6)
  ;;       = (3+4+7+12) + 5 + (6+12+18+24) = 26 + 5 + 60 = 91
  ;; Caller return areas at 512 and 600, clear of the provider's 256/320.
  (func (export "golden:recapp/runner@0.1.0#run") (result f32)
    (call $tick (f32.const 3) (f32.const 4) (i32.const 512))
    (call $pack (i32.const 5) (f32.const 6) (i32.const 600))
    (f32.add
      (f32.add
        (f32.add (f32.add (f32.load offset=0 (i32.const 512)) (f32.load offset=4 (i32.const 512)))
                 (f32.add (f32.load offset=8 (i32.const 512)) (f32.load offset=12 (i32.const 512))))
        (f32.convert_i32_u (i32.load offset=0 (i32.const 600))))
      (f32.add
        (f32.add (f32.load offset=4 (i32.const 600)) (f32.load offset=8 (i32.const 600)))
        (f32.add (f32.load offset=12 (i32.const 600)) (f32.load offset=16 (i32.const 600)))))))
