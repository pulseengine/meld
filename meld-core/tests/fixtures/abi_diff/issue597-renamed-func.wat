;; #594 / #586: a `char` travelling next to a string between two latin1+utf16
;; components in different memories. That call takes the #582 adapter path,
;; which returned before the `char` check was spliced in. The callee returns
;; the `char` it received, so `run` returns 0x41 here. The test swaps the
;; marked constant for 0xD800, which the Canonical ABI must trap on.
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
      ;; (ptr, tagged len, char) -> char; checks the string arrived as latin1 "AB"
      (func (export "take") (param $p i32) (param $len i32) (param $c i32) (result i32)
        (if (i32.ne (local.get $len) (i32.const 2)) (then unreachable))
        (if (i32.ne (i32.load16_u (local.get $p)) (i32.const 0x4241)) (then unreachable))
        (local.get $c))
    )
    (core instance $m (instantiate $M))
    (func (export "tk") (param "s" string) (param "c" char) (result u32)
      (canon lift (core func $m "take") string-encoding=latin1+utf16
        (memory (core memory $m "mem")) (realloc (core func $m "realloc"))))
  )
  (component $D
    (import "tk" (func $take (param "s" string) (param "c" char) (result u32)))
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
      (data (i32.const 64) "AB"))
    (core instance $libc (instantiate $Libc))
    (core func $take' (canon lower (func $take) string-encoding=latin1+utf16
      (memory (core memory $libc "mem")) (realloc (core func $libc "realloc"))))
    (core module $Main
      (import "" "mem" (memory 1))
      (import "" "take" (func $take (param i32 i32 i32) (result i32)))
      (func (export "run") (result i32)
        (call $take (i32.const 64) (i32.const 2)
          (i32.const 0x41) ;; CHAR
        ))
    )
    (core instance $main (instantiate $Main
      (with "" (instance (export "mem" (memory $libc "mem")) (export "take" (func $take'))))))
    (func (export "run") (result u32) (canon lift (core func $main "run")))
  )
  (instance $c (instantiate $C))
  (instance $d (instantiate $D (with "tk" (func $c "tk"))))
  (export "run" (func $d "run"))
)
