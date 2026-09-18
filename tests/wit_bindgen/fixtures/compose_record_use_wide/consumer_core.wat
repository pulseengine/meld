(module
  ;; 18 flattened params -> the argument tuple travels through a pointer;
  ;; the 4-flat result travels through a caller-provided return area.
  (import "golden:wide/lib@0.1.0" "tick" (func $tick (param i32 i32)))
  (memory (export "memory") 1)
  ;; run() = o1 + o2 + o3 + o4
  ;;       = sum(1..14) + sum(1..4) + 1 + 4 = 105 + 10 + 1 + 4 = 120
  ;; Params area at 512, return area at 800.
  (func (export "golden:wideapp/runner@0.1.0#run") (result f32)
    (f32.store offset=0 (i32.const 512) (f32.const 1))
    (f32.store offset=4 (i32.const 512) (f32.const 2))
    (f32.store offset=8 (i32.const 512) (f32.const 3))
    (f32.store offset=12 (i32.const 512) (f32.const 4))
    (f32.store offset=16 (i32.const 512) (f32.const 5))
    (f32.store offset=20 (i32.const 512) (f32.const 6))
    (f32.store offset=24 (i32.const 512) (f32.const 7))
    (f32.store offset=28 (i32.const 512) (f32.const 8))
    (f32.store offset=32 (i32.const 512) (f32.const 9))
    (f32.store offset=36 (i32.const 512) (f32.const 10))
    (f32.store offset=40 (i32.const 512) (f32.const 11))
    (f32.store offset=44 (i32.const 512) (f32.const 12))
    (f32.store offset=48 (i32.const 512) (f32.const 13))
    (f32.store offset=52 (i32.const 512) (f32.const 14))
    (f32.store offset=56 (i32.const 512) (f32.const 1))
    (f32.store offset=60 (i32.const 512) (f32.const 2))
    (f32.store offset=64 (i32.const 512) (f32.const 3))
    (f32.store offset=68 (i32.const 512) (f32.const 4))
    (call $tick (i32.const 512) (i32.const 800))
    (f32.add
      (f32.add (f32.load offset=0 (i32.const 800)) (f32.load offset=4 (i32.const 800)))
      (f32.add (f32.load offset=8 (i32.const 800)) (f32.load offset=12 (i32.const 800)))))
)
