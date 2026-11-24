(component
  (component $callee
    (core func $tr (canon task.return (result u32)))
    (core module $m
      (import "[export]my:t/i" "[task-return]f" (func $tr (param i32)))
      (import "$root" "[waitable-set-poll]" (func $wsp (param i32 i32) (result i32)))
      (import "mm" "mem" (memory 1))
      (func (export "[async-lift]my:t/i#f") (param i32) (result i32) (call $tr (i32.add (local.get 0) (i32.const 100))) (i32.const 0))
      (func (export "[callback][async-lift]my:t/i#f") (param i32 i32 i32) (result i32) (i32.const 0)))
    (core module $memm (memory (export "mem") 1))
    (core instance $mem (instantiate $memm))
    (alias core export $mem "mem" (core memory $memory))
    (core func $wsp (canon waitable-set.poll (memory $memory)))
    (core instance $i (instantiate $m (with "[export]my:t/i" (instance (export "[task-return]f" (func $tr)))) (with "mm" (instance $mem)) (with "$root" (instance (export "[waitable-set-poll]" (func $wsp))))))
    (func $f async (param "x" u32) (result u32) (canon lift (core func $i "[async-lift]my:t/i#f") async (callback (core func $i "[callback][async-lift]my:t/i#f"))))
    (instance $inst (export "f" (func $f)))
    (export "my:t/i" (instance $inst)))
  (component $caller
    (import "my:t/i" (instance $imp (export "f" (func async (param "x" u32) (result u32)))))
    (core func $f (canon lower (func $imp "f")))
    (core module $m
      (import "my:t/i" "f" (func $f (param i32) (result i32)))
      (func (export "go") (result i32) (call $f (i32.const 7))))
    (core instance $i (instantiate $m (with "my:t/i" (instance (export "f" (func $f))))))
    (func (export "go") (result u32) (canon lift (core func $i "go"))))
  (instance $c (instantiate $callee))
  (instance $r (instantiate $caller (with "my:t/i" (instance $c "my:t/i"))))
  (export "go" (func $r "go")))
