(component
  (type $s (stream u32))
  (core func $sdr (canon stream.drop-readable $s))
  (core func $wsd (canon waitable-set.drop))
  (core module $m
    (import "$root" "[waitable-set-drop]" (func $a (param i32)))
    (import "$root" "[stream-drop-readable-0]x" (func $b (param i32)))
    (func (export "run") (param i32) (call $a (local.get 0)) (call $b (local.get 0))))
  ;; swapped on purpose: the module's "[waitable-set-drop]" is stream.drop-readable and vice versa
  (core instance $i (instantiate $m (with "$root" (instance (export "[waitable-set-drop]" (func $sdr)) (export "[stream-drop-readable-0]x" (func $wsd))))))
  (func (export "run") (param "x" u32) (canon lift (core func $i "run"))))
