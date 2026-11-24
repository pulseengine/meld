(component
  (component $callee
    (core module $main
      (global $sp (mut i32) (i32.const 0))
      (func $raw (export "local:t/calc#add") (param i32 i32) (result i32)
        (i32.add (i32.add (local.get 0) (local.get 1)) (global.get $sp)))
      (func (export "hook0") (param i32 i32) (result i32)
        (local $r i32)
        (global.set $sp (i32.const 1000))   ;; __wasm_task_hook(0): install the stack
        (local.set $r (call $raw (local.get 0) (local.get 1)))
        (global.set $sp (i32.const 0))
        (local.get $r)))
    (core instance $i (instantiate $main))
    (func $add (param "a" u32) (param "b" u32) (result u32) (canon lift (core func $i "hook0")))
    (instance $calc (export "add" (func $add)))
    (export "local:t/calc" (instance $calc)))
  (component $caller
    (import "local:t/calc" (instance $calc (export "add" (func (param "a" u32) (param "b" u32) (result u32)))))
    (core func $add (canon lower (func $calc "add")))
    (core module $m
      (import "local:t/calc" "add" (func $add (param i32 i32) (result i32)))
      (func (export "go") (result i32) (call $add (i32.const 1) (i32.const 2))))
    (core instance $i (instantiate $m (with "local:t/calc" (instance (export "add" (func $add))))))
    (func (export "go") (result u32) (canon lift (core func $i "go"))))
  (instance $c (instantiate $callee))
  (instance $r (instantiate $caller (with "local:t/calc" (instance $c "local:t/calc"))))
  (export "go" (func $r "go")))
