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
      ;; (ptr, utf8 byte len) -> hash of len and every byte
      (func (export "uf") (param $p i32) (param $len i32) (result i32)
        (local $h i32) (local $i i32)
        (local.set $h (local.get $len))
        (block $done
          (loop $l
            (br_if $done (i32.ge_u (local.get $i) (local.get $len)))
            (local.set $h
              (i32.add (i32.mul (local.get $h) (i32.const 31))
                       (i32.load8_u (i32.add (local.get $p) (local.get $i)))))
            (local.set $i (i32.add (local.get $i) (i32.const 1)))
            (br $l)))
        (local.get $h))
    )
    (core instance $m (instantiate $M))
    (func (export "uf") (param "s" string) (result u32)
      (canon lift (core func $m "uf") string-encoding=utf8
        (memory (core memory $m "mem")) (realloc (core func $m "realloc"))))
  )
  (component $D
    (import "uf" (func $f (param "s" string) (result u32)))
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
      ;; utf16le: e-acute, euro, U+1F600 (valid pair), 'a', LONE HIGH SURROGATE D800, 'z' = 7 code units
      (data (i32.const 64) "\e9\00\ac\20\3d\d8\00\de\61\00\00\d8\7a\00"))
    (core instance $libc (instantiate $Libc))
    (core func $f' (canon lower (func $f) string-encoding=utf16
      (memory (core memory $libc "mem")) (realloc (core func $libc "realloc"))))
    (core module $Main
      (import "" "mem" (memory 1))
      (import "" "uf" (func $f (param i32 i32) (result i32)))
      (func (export "run") (result i32)
        (call $f (i32.const 64) (i32.const 7)))
    )
    (core instance $main (instantiate $Main
      (with "" (instance (export "mem" (memory $libc "mem")) (export "uf" (func $f'))))))
    (func (export "run") (result u32) (canon lift (core func $main "run")))
  )
  (instance $c (instantiate $C))
  (instance $d (instantiate $D (with "uf" (func $c "uf"))))
  (export "run" (func $d "run"))
)
