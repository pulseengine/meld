# #547 fixtures: P3 cooperative-thread components

Real producer output, not hand-built, so the import names the tests assert are
the ones a host sees. Tracked in git (`.gitignore` exempts `tests/p3/**/*.wasm`);
the tests fail if one is missing.

## Seven clang C components (`*.wasm` in this directory)

Hand-written C against `wit-bindgen c --generate-threading-helpers`
(world `local:thr/w`, `export run: func() -> u32`), compiled with clang and
linked with wasm-ld, then `wasm-tools component new` (1.263). Each exports
`run`. wasmtime 51-dev (`-W component-model-async=y,component-model-threading=y`)
returns the value in the last column for the same component (kiln#620 oracle
table); `suspend_then_resume` and `promote` trap there ("cannot block a
synchronous task before returning"), so they are fused and inspected, never run.

| file | body of `run` (C) | wasmtime result | sha256 |
|---|---|---|---|
| `t1_new_resume.wasm` | `main_thread = thread_index(); t = thread_new_indirect(worker, 7); thread_resume_later(t); thread_yield(); return counter;` where `worker(a) { counter += a; }` | 7 | `4fb9b975493ff56abade9651648c246470ef729a87e282cef274c85405fce60b` |
| `t2_yield_index.wasm` | loop of 3: `thread_yield(); counter += thread_index();` | 3 | `2574cba400c9708884814ffda3df0124d98d41293fd84c8b1a3f5c9ee3d1a5e5` |
| `t3_suspend_resume.wasm` | `me = thread_index(); t = thread_new_indirect(worker, me); thread_resume_later(t); thread_suspend(); return counter;` where `worker(a) { counter = 1; thread_resume_later(a); counter = 2; }` | 2 | `dfd6620e7eb3003dfbf5ce528cbe818c47b4e42051b54dc9083d67be4a7bb7c2` |
| `t4_suspend_then_resume.wasm` | `t = thread_new_indirect(worker, 0); thread_suspend_then_resume(t); return counter;` where `worker` sets `counter = 5` | traps | `a84d93d089c89e76994da664ee57cf96e75dd6384474394a13f8bca53afe2826` |
| `t5_yield_then_resume.wasm` | `t = thread_new_indirect(worker, 0); thread_yield_then_resume(t); return counter;` where `worker` sets `counter = 9` | 9 | `ce082f5e678ff0d26e36ce657f36a1b4c3ae9cbb7d294a922adbc63ef6133f4f` |
| `t6_promote.wasm` | `t = thread_new_indirect(worker, 0); thread_yield_then_promote(t); u = thread_new_indirect(worker, 0); thread_suspend_then_promote(u); return counter;` where `worker` does `counter += 1` | traps | `64b844b6f678e291da6517311b8c770d27082ed0e8644203f7809dbc09cc5f47` |
| `t8_many_threads.wasm` | 8x `thread_new_indirect(worker, i)` + `thread_resume_later`, then `thread_yield()` | 36 | `e3ebd3645d67e5680c9dadf3957c0f9bd5ad19b6d502d0f52e16331fd4be327a` |

Between them they use all nine built-ins; the test checks that.

## Four wasmtime test-suite components (`corpus/`)

Extracted from `tests/misc_testsuite/component-model-threading/*.wast` of
wasmtime at commit 3cfc2d6 (`wasm-tools 1.263`, module N of the wast):

| file | wast#module | sha256 |
|---|---|---|
| `corpus/wasmtime_many-threads-indexed_m0.wasm` | many-threads-indexed.wast#module0 | `642346adc6dd6e4296cafdc4b77e216fb6e5470a999eb2c3c5e53c5d0a6fa1f4` |
| `corpus/wasmtime_promote-ready-threads_m0.wasm` | promote-ready-threads.wast#module0 | `913afabd3c16970289085924bd05b6b349272f4f313cf88cc4c5bd3dfcb88371` |
| `corpus/wasmtime_threading-builtins_m5.wasm` | threading-builtins.wast#module5 (two components, both `thread.index`: the second import surfaces as `[thread-index]$1`) | `b2332687d6f6bfd487f41307edbefd0769b991058b979f7b514cfb44b8603185` |
| `corpus/wasmtime_yield-cancellable_m0.wasm` | yield-cancellable.wast#module0 | `b8c563f3a98303106d06eaf54e1d099d73b6cceb820109005a6ce5a72ae139bc` |

## Two alias-chain components (`alias_chain/`)

Hand-written WAT, assembled with wasm-tools 1.263, from the Mythos review of
this change. Each wires a NON-lower canonical built-in into a core module's
import through bag -> `alias core export` -> bag, where the module's own import
name belongs to a DIFFERENT built-in. meld used to keep the module's name, so a
host would bind the wrong built-in.

| file | built-in reached | name the module imports it under | sha256 |
|---|---|---|---|
| `alias_chain/yield_via_alias_chain.wasm` | `thread.yield` | `$root::[thread-index]` | `557b75c6c28660ac032d25f6854830dc67af6ab675e56fad602ce1c954d46057` |
| `alias_chain/context_get_via_alias_chain.wasm` | `context.get i32 0` | `$root::[waitable-set-new]` | `f573a4a4a8331aaac8012fd04a70a8a3d2ba415dd3d9d1af791dc30fe3acede4` |

`yield_via_alias_chain.wasm`'s `run` calls `thread.new-indirect(1, 7)`,
`thread.resume-later`, then the aliased `thread.yield`, and returns a counter;
the composed component returns 7 on wasmtime 51-dev. The fused module must
import `[thread-yield]` and, on a host that resolves `fn_idx` through
`__meld_thread_table`, return 7.
