(component
  (component $A
    (core module $m (func (export "get") (result i32) (i32.const 41)))
    (core instance $i (instantiate $m))
    (func $get (result u32) (canon lift (core func $i "get")))
    (export "get" (func $get)))
  (component $B
    (import "get" (func $get (result u32)))
    (core func $get (canon lower (func $get)))
    (core module $m
      (import "a" "get" (func $get (result i32)))
      (func (export "run") (result i32) (i32.add (call $get) (i32.const 1))))
    (core instance $a (export "get" (func $get)))
    (core instance $i (instantiate $m (with "a" (instance $a))))
    (func $run (result u32) (canon lift (core func $i "run")))
    (export "run" (func $run)))
  (instance $a (instantiate $A))
  (instance $b (instantiate $B (with "get" (func $a "get"))))
  (export "run" (func $b "run")))
