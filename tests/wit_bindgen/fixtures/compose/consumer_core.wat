(module
  (import "golden:math/lib@0.1.0" "add" (func $add (param i32 i32) (result i32)))
  (memory (export "memory") 1)
  (func (export "golden:app/runner@0.1.0#compute") (result i32)
    i32.const 20 i32.const 22 call $add))
