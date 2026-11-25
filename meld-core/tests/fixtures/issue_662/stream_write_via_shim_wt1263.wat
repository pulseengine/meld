(component
  (core module $main (;0;)
    (type (;0;) (func (result i64)))
    (type (;1;) (func (param i32 i32 i32) (result i32)))
    (type (;2;) (func))
    (type (;3;) (func (result i32)))
    (import "[export]test:x/api" "[stream-new-0]get" (func $snew (;0;) (type 0) (result i64)))
    (import "[export]test:x/api" "[async-lower][stream-write-0]get" (func $swrite (;1;) (type 1) (param i32 i32 i32) (result i32)))
    (memory (;0;) 1)
    (export "memory" (memory 0))
    (export "_initialize" (func 2))
    (export "test:x/api#get" (func 3))
    (func (;2;) (type 2))
    (func (;3;) (type 3) (result i32)
      (local $p i64)
      call $snew
      local.set $p
      local.get $p
      i64.const 32
      i64.shr_u
      i32.wrap_i64
      i32.const 16
      i32.const 1
      call $swrite
      drop
      local.get $p
      i32.wrap_i64
    )
    (@producers
      (processed-by "wit-component" "0.263.0")
    )
  )
  (core module $wit-component-shim-module (;1;)
    (type (;0;) (func (param i32 i32 i32) (result i32)))
    (table (;0;) 1 1 funcref)
    (export "0" (func $"[export]test:x/api-[stream-write-0]get"))
    (export "$imports" (table 0))
    (func $"[export]test:x/api-[stream-write-0]get" (;0;) (type 0) (param i32 i32 i32) (result i32)
      local.get 0
      local.get 1
      local.get 2
      i32.const 0
      call_indirect (type 0)
    )
    (@producers
      (processed-by "wit-component" "0.263.0")
    )
  )
  (core instance $wit-component-shim-instance (;0;) (instantiate $wit-component-shim-module))
  (type (;0;) (stream u32))
  (core func $stream.new (;0;) (canon stream.new 0))
  (alias core export $wit-component-shim-instance "0" (core func $"[export]test:x/api-[stream-write-0]get" (;1;)))
  (core instance $"[export]test:x/api" (;1;)
    (export "[stream-new-0]get" (func $stream.new))
    (export "[async-lower][stream-write-0]get" (func $"[export]test:x/api-[stream-write-0]get"))
  )
  (core instance $main (;2;) (instantiate $main
      (with "[export]test:x/api" (instance $"[export]test:x/api"))
    )
  )
  (alias core export $main "memory" (core memory $memory (;0;)))
  (core module $wit-component-fixup (;2;)
    (type (;0;) (func (param i32 i32 i32) (result i32)))
    (type (;1;) (func))
    (import "actual" "0" (func $0 (;0;) (type 0) (param i32 i32 i32) (result i32)))
    (import "main" "_initialize" (func $_initialize (;1;) (type 1)))
    (import "shim" "$imports" (table (;0;) 1 1 funcref))
    (start $_initialize)
    (elem (;0;) (i32.const 0) func $0)
    (@producers
      (processed-by "wit-component" "0.263.0")
    )
  )
  (core func $stream.write (;2;) (canon stream.write 0 (memory $memory) async))
  (core instance $actual (;3;)
    (export "0" (func $stream.write))
  )
  (core instance $fixup (;4;) (instantiate $wit-component-fixup
      (with "actual" (instance $actual))
      (with "main" (instance $main))
      (with "shim" (instance $wit-component-shim-instance))
    )
  )
  (type (;1;) (func (result 0)))
  (alias core export $main "test:x/api#get" (core func $test:x/api#get (;3;)))
  (func $get (;0;) (type 1) (canon lift (core func $test:x/api#get)))
  (component $test:x/api-shim-component (;0;)
    (type (;0;) (stream u32))
    (type (;1;) (func (result 0)))
    (import "import-func-get" (func (;0;) (type 1)))
    (type (;2;) (stream u32))
    (type (;3;) (func (result 2)))
    (export (;1;) "get" (func 0) (func (type 3)))
  )
  (instance $test:x/api-shim-instance (;0;) (instantiate $test:x/api-shim-component
      (with "import-func-get" (func $get))
    )
  )
  (export $test:x/api (;1;) "test:x/api" (instance $test:x/api-shim-instance))
  (@producers
    (processed-by "wit-component" "0.263.0")
  )
)
