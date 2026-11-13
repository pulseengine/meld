(component
  (component $C
    (core module $M
      (memory (export "mem") 1)
      (global $next (mut i32) (i32.const 1024))
      (func (export "realloc") (param $old i32) (param $osize i32) (param $align i32) (param $nsize i32) (result i32)
        (local $r i32)
        (if (i32.and (i32.ne (local.get $old) (i32.const 0))
                     (i32.le_u (local.get $nsize) (local.get $osize)))
          (then (return (local.get $old))))
        (global.set $next (i32.and (i32.add (global.get $next) (i32.const 7)) (i32.const -8)))
        (local.set $r (global.get $next))
        (global.set $next (i32.add (global.get $next) (local.get $nsize)))
        (if (i32.ne (local.get $old) (i32.const 0))
          (then (memory.copy (local.get $r) (local.get $old) (local.get $osize))))
        (local.get $r))
      ;; (ptr, len in utf16 code units) -> hash of len and every 16-bit unit
      (func (export "uf") (param $p i32) (param $len i32) (result i32)
        (local $h i32)
        (local $i i32)
        (local.set $h (local.get $len))
        (block $done
          (loop $l
            (br_if $done (i32.ge_u (local.get $i) (local.get $len)))
            (local.set $h
              (i32.add (i32.mul (local.get $h) (i32.const 31))
                (i32.load16_u (i32.add (local.get $p) (i32.shl (local.get $i) (i32.const 1))))))
            (local.set $i (i32.add (local.get $i) (i32.const 1)))
            (br $l)))
        (local.get $h))
    )
    (core instance $m (instantiate $M))
    (func (export "uf") (param "s" string) (result u32)
      (canon lift (core func $m "uf") string-encoding=utf16
        (memory (core memory $m "mem")) (realloc (core func $m "realloc"))))
  )
  (component $D
    (import "uf" (func $take (param "s" string) (result u32)))
    (core module $Libc
      (memory (export "mem") 1)
      (global $next (mut i32) (i32.const 1024))
      (func (export "realloc") (param $old i32) (param $osize i32) (param $align i32) (param $nsize i32) (result i32)
        (local $r i32)
        (if (i32.and (i32.ne (local.get $old) (i32.const 0))
                     (i32.le_u (local.get $nsize) (local.get $osize)))
          (then (return (local.get $old))))
        (global.set $next (i32.and (i32.add (global.get $next) (i32.const 7)) (i32.const -8)))
        (local.set $r (global.get $next))
        (global.set $next (i32.add (global.get $next) (local.get $nsize)))
        (if (i32.ne (local.get $old) (i32.const 0))
          (then (memory.copy (local.get $r) (local.get $old) (local.get $osize))))
        (local.get $r))
      ;; utf8: x, U+20AC, y, U+1F600, U+00E9 = 11 bytes
      (data (i32.const 64) "x\e2\82\acy\f0\9f\98\80\c3\a9"))
    (core instance $libc (instantiate $Libc))
    (core func $take' (canon lower (func $take) string-encoding=utf8
      (memory (core memory $libc "mem")) (realloc (core func $libc "realloc"))))
    (core module $Main
      (import "" "mem" (memory 1))
      (import "" "uf" (func $take (param i32 i32) (result i32)))
      (func (export "run") (result i32)
        (call $take (i32.const 64) (i32.const 11)))
    )
    (core instance $main (instantiate $Main
      (with "" (instance (export "mem" (memory $libc "mem")) (export "uf" (func $take'))))))
    (func (export "run") (result u32) (canon lift (core func $main "run")))
  )
  (instance $c (instantiate $C))
  (instance $d (instantiate $D (with "uf" (func $c "uf"))))
  (export "run" (func $d "run"))
)
