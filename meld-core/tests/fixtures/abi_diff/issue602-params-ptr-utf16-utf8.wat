(component
  (component $C

    (core module $M
      (memory (export "mem") 1)
      (global $next (mut i32) (i32.const 1024))
      (func (export "realloc") (param $old i32) (param $osize i32) (param $align i32) (param $nsize i32) (result i32)
        (local $r i32)
        (global.set $next (i32.and (i32.add (global.get $next) (i32.const 7)) (i32.const -8)))
        (local.set $r (global.get $next))
        (global.set $next (i32.add (global.get $next) (local.get $nsize)))
        (if (i32.ne (local.get $old) (i32.const 0)) (then (memory.copy (local.get $r) (local.get $old) (local.get $osize))))
        (local.get $r))
      (func (export "take") (param i32) (result i32) (i32.add (i32.mul (i32.load offset=4 (local.get 0)) (i32.const 0x10000)) (i32.add (i32.load8_u (i32.load (local.get 0))) (i32.load offset=64 (local.get 0))))))
    (core instance $m (instantiate $M))
    (func (export "take") (param "s" string) (param "a0" u32) (param "a1" u32) (param "a2" u32) (param "a3" u32) (param "a4" u32) (param "a5" u32) (param "a6" u32) (param "a7" u32) (param "a8" u32) (param "a9" u32) (param "a10" u32) (param "a11" u32) (param "a12" u32) (param "a13" u32) (param "a14" u32) (result u32)
      (canon lift (core func $m "take") string-encoding=utf8
        (memory (core memory $m "mem")) (realloc (core func $m "realloc")))))
  (component $D

    (import "take" (func $take (param "s" string) (param "a0" u32) (param "a1" u32) (param "a2" u32) (param "a3" u32) (param "a4" u32) (param "a5" u32) (param "a6" u32) (param "a7" u32) (param "a8" u32) (param "a9" u32) (param "a10" u32) (param "a11" u32) (param "a12" u32) (param "a13" u32) (param "a14" u32) (result u32)))
    (core module $Libc
      (memory (export "mem") 1)
      (global $next (mut i32) (i32.const 1024))
      (func (export "realloc") (param $old i32) (param $osize i32) (param $align i32) (param $nsize i32) (result i32)
        (local $r i32)
        (global.set $next (i32.and (i32.add (global.get $next) (i32.const 7)) (i32.const -8)))
        (local.set $r (global.get $next))
        (global.set $next (i32.add (global.get $next) (local.get $nsize)))
        (if (i32.ne (local.get $old) (i32.const 0)) (then (memory.copy (local.get $r) (local.get $old) (local.get $osize))))
        (local.get $r))
      (data (i32.const 64) "A\00B\00") (data (i32.const 128) "\40\00\00\00\02\00\00\00") (data (i32.const 192) "\07\00\00\00"))
    (core instance $libc (instantiate $Libc))
    (core func $take' (canon lower (func $take) string-encoding=utf16
      (memory (core memory $libc "mem")) (realloc (core func $libc "realloc"))))
    (core module $Main
      (import "" "mem" (memory 1))
      (import "" "take" (func $take (param i32) (result i32)))
      (func (export "run") (result i32) (call $take (i32.const 128))))
    (core instance $main (instantiate $Main
      (with "" (instance (export "mem" (memory $libc "mem")) (export "take" (func $take'))))))
    (func (export "run") (result u32) (canon lift (core func $main "run"))))
  (instance $c (instantiate $C))
  (instance $d (instantiate $D (with "take" (func $c "take"))))
  (export "run" (func $d "run")))
