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
      (func (export "uf") (param $p i32) (param $n i32) (result i32)
        (local $h i32) (local $i i32) (local $j i32) (local $sp i32) (local $sl i32) (local $e i32)
        (local.set $h (i32.add (i32.mul (i32.const 7) (i32.const 31)) (local.get $n)))
        (block $done
          (loop $outer
            (br_if $done (i32.ge_u (local.get $i) (local.get $n)))
            (local.set $e (i32.add (local.get $p) (i32.shl (local.get $i) (i32.const 3))))
            (local.set $sp (i32.load (local.get $e)))
            (local.set $sl (i32.load offset=4 (local.get $e)))
            (local.set $h (i32.add (i32.mul (local.get $h) (i32.const 31)) (local.get $sl)))
            (local.set $j (i32.const 0))
            (block $idone
              (loop $inner
                (br_if $idone (i32.ge_u (local.get $j) (local.get $sl)))
                (local.set $h (i32.add (i32.mul (local.get $h) (i32.const 31))
                  (i32.load8_u (i32.add (local.get $sp) (local.get $j)))))
                (local.set $j (i32.add (local.get $j) (i32.const 1)))
                (br $inner)))
            (local.set $i (i32.add (local.get $i) (i32.const 1)))
            (br $outer)))
        (local.get $h))
    )
    (core instance $m (instantiate $M))
    (func (export "uf") (param "l" (list string)) (result u32)
      (canon lift (core func $m "uf") string-encoding=utf8
        (memory (core memory $m "mem")) (realloc (core func $m "realloc"))))
  )
  (component $D
    (import "uf" (func $f (param "l" (list string)) (result u32)))
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
      (data (i32.const 128) "caf\e9")
      (data (i32.const 144) "a\00\ac\20")
      (data (i32.const 152) "\3d\d8\00\de\7a\00")
      (data (i32.const 160) "\e9\00")
      (data (i32.const 168) "hello, world!")
      (data (i32.const 512)
        "\80\00\00\00\04\00\00\00"
        "\88\00\00\00\00\00\00\00"
        "\90\00\00\00\02\00\00\80"
        "\98\00\00\00\03\00\00\80"
        "\a0\00\00\00\01\00\00\80"
        "\a8\00\00\00\0d\00\00\00"))
    (core instance $libc (instantiate $Libc))
    (core func $f' (canon lower (func $f) string-encoding=latin1+utf16
      (memory (core memory $libc "mem")) (realloc (core func $libc "realloc"))))
    (core module $Main
      (import "" "uf" (func $f (param i32 i32) (result i32)))
      (func (export "run") (result i32)
        (call $f (i32.const 512) (i32.const 6)))
    )
    (core instance $main (instantiate $Main
      (with "" (instance (export "uf" (func $f'))))))
    (func (export "run") (result u32) (canon lift (core func $main "run")))
  )
  (instance $c (instantiate $C))
  (instance $d (instantiate $D (with "uf" (func $c "uf"))))
  (export "run" (func $d "run"))
)
