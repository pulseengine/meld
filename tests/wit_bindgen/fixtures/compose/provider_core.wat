(module
  (memory (export "memory") 1)
  (func (export "golden:math/lib@0.1.0#add") (param i32 i32) (result i32)
    local.get 0 local.get 1 i32.add))
