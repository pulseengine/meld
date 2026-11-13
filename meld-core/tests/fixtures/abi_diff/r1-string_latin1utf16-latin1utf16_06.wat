(component
  (component $C
    (core module $M
      (memory (export "mem") 1)
      (global $next (mut i32) (i32.const 1024))
      (func (export "realloc") (param $old i32) (param $osize i32) (param $align i32) (param $nsize i32) (result i32)
        (local $r i32)
        (if (i32.and (i32.ne (local.get $old) (i32.const 0)) (i32.le_u (local.get $nsize) (local.get $osize)))
          (then (return (local.get $old))))
        (global.set $next (i32.and (i32.add (global.get $next) (i32.const 7)) (i32.const -8)))
        (local.set $r (global.get $next))
        (global.set $next (i32.add (global.get $next) (local.get $nsize)))
        (if (i32.ne (local.get $old) (i32.const 0))
          (then (memory.copy (local.get $r) (local.get $old) (local.get $osize))))
        (local.get $r))
      (func $hs (param $h i32) (param $p i32) (param $len i32) (result i32)
        (local $i i32) (local $n i32)
        (local.set $h (i32.add (i32.mul (local.get $h) (i32.const 31)) (local.get $len)))
        (if (i32.and (local.get $len) (i32.const 0x80000000))
          (then
            (local.set $n (i32.and (local.get $len) (i32.const 0x7fffffff)))
            (loop $l
              (if (i32.lt_u (local.get $i) (local.get $n))
                (then
                  (local.set $h (i32.add (i32.mul (local.get $h) (i32.const 31)) (i32.load16_u (i32.add (local.get $p) (i32.shl (local.get $i) (i32.const 1))))))
                  (local.set $i (i32.add (local.get $i) (i32.const 1)))
                  (br $l)))))
          (else
            (local.set $n (local.get $len))
            (loop $l2
              (if (i32.lt_u (local.get $i) (local.get $n))
                (then
                  (local.set $h (i32.add (i32.mul (local.get $h) (i32.const 31)) (i32.load8_u (i32.add (local.get $p) (local.get $i)))))
                  (local.set $i (i32.add (local.get $i) (i32.const 1)))
                  (br $l2))))))
        (local.get $h))
      (func (export "uf") (param $p i32) (result i32)
        (local $h i32) (local $i i32)
        (local.set $h (call $hs (i32.const 0) (i32.load (local.get $p)) (i32.load offset=4 (local.get $p))))
        (loop $l
          (if (i32.lt_u (local.get $i) (i32.const 13))
            (then
              (local.set $h (i32.add (i32.mul (local.get $h) (i32.const 31)) (i32.load offset=8 (i32.add (local.get $p) (i32.shl (local.get $i) (i32.const 2))))))
              (local.set $i (i32.add (local.get $i) (i32.const 1)))
              (br $l))))
        (call $hs (local.get $h) (i32.load offset=60 (local.get $p)) (i32.load offset=64 (local.get $p))))
    )
    (core instance $m (instantiate $M))
    (func (export "uf") (param "a" string) (param "n0" u32) (param "n1" u32) (param "n2" u32) (param "n3" u32) (param "n4" u32) (param "n5" u32) (param "n6" u32) (param "n7" u32) (param "n8" u32) (param "n9" u32) (param "n10" u32) (param "n11" u32) (param "n12" u32) (param "b" string) (result u32)
      (canon lift (core func $m "uf") string-encoding=latin1+utf16
        (memory (core memory $m "mem")) (realloc (core func $m "realloc"))))
  )
  (component $D
    (import "uf" (func $f (param "a" string) (param "n0" u32) (param "n1" u32) (param "n2" u32) (param "n3" u32) (param "n4" u32) (param "n5" u32) (param "n6" u32) (param "n7" u32) (param "n8" u32) (param "n9" u32) (param "n10" u32) (param "n11" u32) (param "n12" u32) (param "b" string) (result u32)))
    (core module $Libc
      (memory (export "mem") 1)
      (global $next (mut i32) (i32.const 2048))
      (func (export "realloc") (param $old i32) (param $osize i32) (param $align i32) (param $nsize i32) (result i32)
        (local $r i32)
        (if (i32.and (i32.ne (local.get $old) (i32.const 0)) (i32.le_u (local.get $nsize) (local.get $osize)))
          (then (return (local.get $old))))
        (global.set $next (i32.and (i32.add (global.get $next) (i32.const 7)) (i32.const -8)))
        (local.set $r (global.get $next))
        (global.set $next (i32.add (global.get $next) (local.get $nsize)))
        (if (i32.ne (local.get $old) (i32.const 0))
          (then (memory.copy (local.get $r) (local.get $old) (local.get $osize))))
        (local.get $r))
      (data (i32.const 128) "caf\e9")
      (data (i32.const 256) "\ac\20a\00\3d\d8\00\de\e9\00"))
    (core instance $libc (instantiate $Libc))
    (core func $f' (canon lower (func $f) string-encoding=latin1+utf16
      (memory (core memory $libc "mem")) (realloc (core func $libc "realloc"))))
    (core module $Main
      (import "" "mem" (memory 1))
      (import "" "uf" (func $f (param i32) (result i32)))
      (func (export "run") (result i32)
        (local $i i32)
        (i32.store (i32.const 512) (i32.const 128))
        (i32.store (i32.const 516) (i32.const 4))
        (loop $l
          (if (i32.lt_u (local.get $i) (i32.const 13))
            (then
              (i32.store (i32.add (i32.const 520) (i32.shl (local.get $i) (i32.const 2)))
                (i32.add (i32.mul (local.get $i) (i32.const 1000003)) (i32.const 17)))
              (local.set $i (i32.add (local.get $i) (i32.const 1)))
              (br $l))))
        (i32.store (i32.const 572) (i32.const 256))
        (i32.store (i32.const 576) (i32.const 0x80000005))
        (call $f (i32.const 512)))
    )
    (core instance $main (instantiate $Main
      (with "" (instance (export "mem" (memory $libc "mem")) (export "uf" (func $f'))))))
    (func (export "run") (result u32) (canon lift (core func $main "run")))
  )
  (instance $c (instantiate $C))
  (instance $d (instantiate $D (with "uf" (func $c "uf"))))
  (export "run" (func $d "run"))
)
