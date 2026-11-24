(component
  (type $s (stream u32))
  (core func $snew (canon stream.new $s))
  (core func $wsn (canon waitable-set.new))
  (core module $m
    (import "test:x/api" "[stream-new-0]get" (func $snew (result i64)))
    (import "$root" "[waitable-set-new]" (func $wsn (result i32)))
    (memory (export "memory") 1)
    (func (export "run1") (result i32) (drop (call $wsn)) (i32.wrap_i64 (call $snew))))
  (core instance $i (instantiate $m (with "test:x/api" (instance (export "[stream-new-0]get" (func $snew)))) (with "$root" (instance (export "[waitable-set-new]" (func $wsn))))))
  (func (export "run1") (result u32) (canon lift (core func $i "run1"))))
