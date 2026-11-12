;; #582 result side: latin1+utf16 on both sides; the callee returns "AB"
;; over-encoded as utf16 (tagged). The Canonical ABI deflates it on the way
;; back, so the caller must see latin1 "AB": 2 code units, tag clear, bytes
;; 41 42. `run` returns 9 only then.
(component
  (component $C
    (core module $M
      (memory (export "mem") 1)
      (global $next (mut i32) (i32.const 1024))
      ;; realloc as upstream transcode.wast's: a shrink keeps the allocation in
      ;; place (a transcoder allocates the worst case, then shrinks), a grow
      ;; copies the old contents.
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
      (data (i32.const 64) "\41\00\42\00")
      (func (export "give") (result i32)
        (i32.store (i32.const 0) (i32.const 64))
        (i32.store (i32.const 4) (i32.const 0x80000002))
        (i32.const 0))
    )
    (core instance $m (instantiate $M))
    (func (export "give") (result string)
      (canon lift (core func $m "give") string-encoding=latin1+utf16
        (memory (core memory $m "mem")) (realloc (core func $m "realloc"))))
  )
  (component $D
    (import "give" (func $give (result string)))
    (core module $Libc
      (memory (export "mem") 1)
      (global $next (mut i32) (i32.const 1024))
      ;; realloc as upstream transcode.wast's: a shrink keeps the allocation in
      ;; place (a transcoder allocates the worst case, then shrinks), a grow
      ;; copies the old contents.
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
        (local.get $r)))
    (core instance $libc (instantiate $Libc))
    (core func $give' (canon lower (func $give) string-encoding=latin1+utf16
      (memory (core memory $libc "mem")) (realloc (core func $libc "realloc"))))
    (core module $Main
      (import "" "mem" (memory 1))
      (import "" "give" (func $give (param i32)))
      (func (export "run") (result i32)
        (local $p i32)
        (call $give (i32.const 8))
        (if (i32.ne (i32.load (i32.const 12)) (i32.const 2)) (then unreachable))
        (local.set $p (i32.load (i32.const 8)))
        (if (i32.ne (i32.load16_u (local.get $p)) (i32.const 0x4241)) (then unreachable))
        (i32.const 9))
    )
    (core instance $main (instantiate $Main
      (with "" (instance (export "mem" (memory $libc "mem")) (export "give" (func $give'))))))
    (func (export "run") (result u32) (canon lift (core func $main "run")))
  )
  (instance $c (instantiate $C))
  (instance $d (instantiate $D (with "give" (func $c "give"))))
  (export "run" (func $d "run"))
)
