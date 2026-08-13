(module
  (import "gate:math/lib@0.1.0" "add" (func $add (param i32 i32) (result i32)))
  (memory (export "memory") 1)
  ;; check(x): compute add(x,0) across the provider seam, then decide result > 40.
  ;; One decision; invoking with x above and below 40 covers both branch edges.
  (func $check (export "gate:seam/runner@0.1.0#check") (param $x i32) (result i32)
    local.get $x i32.const 0 call $add
    i32.const 40 i32.gt_u
    (if (result i32) (then i32.const 1) (else i32.const 0))))
