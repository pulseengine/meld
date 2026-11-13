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
      ;; string data: latin1 "caf\e9", utf16 "\u20ac" "uro", utf16 U+1F600 "x", latin1 "Hello, w\f6rld \ff!"
      (data (i32.const 80) "caf\e9")
      (data (i32.const 96) "\ac\20" "u\00" "r\00" "o\00")
      (data (i32.const 112) "\3d\d8\00\de" "x\00")
      (data (i32.const 128) "Hello, w" "\f6" "rld " "\ff" "!")
      ;; element table at 512: five (ptr, tagged len) pairs: empty, latin1 4, utf16 4, utf16 3, latin1 15
      (data (i32.const 512)
        "\40\00\00\00\00\00\00\00"
        "\50\00\00\00\04\00\00\00"
        "\60\00\00\00\04\00\00\80"
        "\70\00\00\00\03\00\00\80"
        "\80\00\00\00\0f\00\00\00")
      ;; result area at 576: (ptr=512, len=5)
      (data (i32.const 576) "\00\02\00\00\05\00\00\00")
      (func (export "uf") (result i32) (i32.const 576))
    )
    (core instance $m (instantiate $M))
    (func (export "uf") (result (list string))
      (canon lift (core func $m "uf") string-encoding=latin1+utf16
        (memory (core memory $m "mem")) (realloc (core func $m "realloc"))))
  )
  (component $D
    (import "uf" (func $f (result (list string))))
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
        (local.get $r)))
    (core instance $libc (instantiate $Libc))
    (core func $f' (canon lower (func $f) string-encoding=utf8
      (memory (core memory $libc "mem")) (realloc (core func $libc "realloc"))))
    (core module $Main
      (import "" "mem" (memory 1))
      (import "" "uf" (func $f (param i32)))
      (func (export "run") (result i32)
        (local $p i32) (local $n i32) (local $i i32) (local $h i32) (local $sp i32) (local $sl i32) (local $j i32)
        (call $f (i32.const 256))
        (local.set $p (i32.load (i32.const 256)))
        (local.set $n (i32.load (i32.const 260)))
        (local.set $h (local.get $n))
        (block $done (loop $outer
          (br_if $done (i32.ge_u (local.get $i) (local.get $n)))
          (local.set $sp (i32.load (i32.add (local.get $p) (i32.shl (local.get $i) (i32.const 3)))))
          (local.set $sl (i32.load offset=4 (i32.add (local.get $p) (i32.shl (local.get $i) (i32.const 3)))))
          (local.set $h (i32.add (i32.mul (local.get $h) (i32.const 31)) (local.get $sl)))
          (local.set $j (i32.const 0))
          (block $id (loop $inner
            (br_if $id (i32.ge_u (local.get $j) (local.get $sl)))
            (local.set $h (i32.add (i32.mul (local.get $h) (i32.const 31))
              (i32.load8_u (i32.add (local.get $sp) (local.get $j)))))
            (local.set $j (i32.add (local.get $j) (i32.const 1)))
            (br $inner)))
          (local.set $i (i32.add (local.get $i) (i32.const 1)))
          (br $outer)))
        (local.get $h))
    )
    (core instance $main (instantiate $Main
      (with "" (instance (export "mem" (memory $libc "mem")) (export "uf" (func $f'))))))
    (func (export "run") (result u32) (canon lift (core func $main "run")))
  )
  (instance $c (instantiate $C))
  (instance $d (instantiate $D (with "uf" (func $c "uf"))))
  (export "run" (func $d "run"))
)
