(component
  (component $A
    (type $f (future u32))
    (core func $fdropr (canon future.drop-readable $f))
    (core module $m
      (import "b" "fdropr" (func $fdropr (param i32)))
      (func (export "my:t/i#take") (param i32) (call $fdropr (local.get 0))))
    (core instance $b (export "fdropr" (func $fdropr)))
    (core instance $i (instantiate $m (with "b" (instance $b))))
    (func $take (param "x" $f) (canon lift (core func $i "my:t/i#take")))
    (instance $inst (export "take" (func $take)))
    (export "my:t/i" (instance $inst)))
  (component $B
    (type $f (future u32))
    (import "my:t/i" (instance $imp (export "take" (func (param "x" $f)))))
    (core func $take (canon lower (func $imp "take")))
    (core func $fnew (canon future.new $f))
    (core module $m
      (import "my:t/i" "take" (func $take (param i32)))
      (import "b" "fnew" (func $fnew (result i64)))
      (func (export "run") (call $take (i32.wrap_i64 (call $fnew)))))
    (core instance $b (export "fnew" (func $fnew)))
    (core instance $i (instantiate $m (with "my:t/i" (instance (export "take" (func $take)))) (with "b" (instance $b))))
    (func (export "run") (canon lift (core func $i "run"))))
  (instance $a (instantiate $A))
  (instance $b (instantiate $B (with "my:t/i" (instance $a "my:t/i"))))
  (export "run" (func $b "run")))
