#!/usr/bin/env python3
"""Fail when a Python file cannot run on the Python floor (3.9).

macOS ships /usr/bin/python3 3.9, and committed scripts get run with it; CI
runs 3.11+, where all of the below is fine, so nothing caught them. Run this
under python3.9: the compile step is then the real 3.9 parser, and the AST
pass catches what parses on 3.9 but fails when it runs:

  - `import tomllib` (3.11) outside a try/except ImportError or a
    version_info guard;
  - `X | Y` in an annotation Python evaluates (function signature, module or
    class level) without `from __future__ import annotations`;
  - `X | None` / `int | str` used as a value, e.g. `isinstance(x, A | B)` --
    the __future__ import does not help there;
  - zip(strict=), datetime.UTC, and from-imports of names that do not exist
    on 3.9 (typing.TypeAlias, enum.StrEnum, ...).

vermin was tried first: it ignores `from __future__ import annotations` and
flags a guarded `import tomllib`, so it reports the fixed files as broken.

Usage: check-py-floor.py FILE...   |   check-py-floor.py --self-test
Exit 0 clean, 1 findings, 2 usage error.
"""
import ast
import sys

NEW_MODULES = {"tomllib": "3.11"}
NEW_NAMES = {
    ("typing", "TypeAlias"): "3.10", ("typing", "ParamSpec"): "3.10",
    ("typing", "Concatenate"): "3.10", ("typing", "TypeGuard"): "3.10",
    ("typing", "Self"): "3.11", ("typing", "Never"): "3.11",
    ("typing", "LiteralString"): "3.11", ("typing", "Required"): "3.11",
    ("typing", "NotRequired"): "3.11", ("typing", "assert_never"): "3.11",
    ("typing", "reveal_type"): "3.11", ("typing", "override"): "3.12",
    ("enum", "StrEnum"): "3.11", ("datetime", "UTC"): "3.11",
    ("itertools", "pairwise"): "3.10", ("itertools", "batched"): "3.12",
    ("contextlib", "chdir"): "3.11", ("hashlib", "file_digest"): "3.11",
}
TYPE_NAMES = {"None", "int", "str", "float", "bool", "bytes", "list", "dict",
              "set", "tuple", "frozenset", "type", "object", "complex"}


def _is_typeish(node):
    if isinstance(node, ast.Constant) and node.value is None:
        return True
    if isinstance(node, ast.Name) and node.id in TYPE_NAMES:
        return True
    if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name):
        return node.value.id in TYPE_NAMES
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        return _is_typeish(node.left) or _is_typeish(node.right)
    return False


def _has_union(node):
    return any(isinstance(n, ast.BinOp) and isinstance(n.op, ast.BitOr)
               for n in ast.walk(node))


def _is_guard_try(node):
    if not isinstance(node, ast.Try):
        return False
    for h in node.handlers:
        if h.type is None:
            return True
        types = h.type.elts if isinstance(h.type, ast.Tuple) else [h.type]
        if any(getattr(t, "id", "") in ("ImportError", "ModuleNotFoundError", "Exception")
               for t in types):
            return True
    return False


def _mentions_version(node):
    return any(isinstance(n, ast.Attribute) and n.attr in ("version_info", "version")
               for n in ast.walk(node))


def _exits(body):
    for n in body:
        for m in ast.walk(n):
            if isinstance(m, ast.Raise):
                return True
            if isinstance(m, ast.Call):
                f = m.func
                name = f.attr if isinstance(f, ast.Attribute) else getattr(f, "id", "")
                if name in ("exit", "SystemExit", "_exit"):
                    return True
    return False


def check_source(src, path="<src>"):
    try:
        tree = compile(src, path, "exec", ast.PyCF_ONLY_AST)
    except SyntaxError as e:
        return [f"{path}:{e.lineno}: does not parse on Python "
                f"{sys.version_info[0]}.{sys.version_info[1]}: {e.msg}"]
    future = any(isinstance(n, ast.ImportFrom) and n.module == "__future__"
                 and any(a.name == "annotations" for a in n.names)
                 for n in tree.body)
    findings = []
    # `import datetime as _dt` -> {"_dt": "datetime"}, so `_dt.UTC` is seen.
    alias = {}
    for n in ast.walk(tree):
        if isinstance(n, ast.Import):
            for a in n.names:
                alias[a.asname or a.name] = a.name

    # Imports guarded by try/except ImportError, an `if sys.version_info`
    # branch, or a top-level version check that exits before them.
    guarded = set()
    for n in ast.walk(tree):
        if _is_guard_try(n) or (isinstance(n, ast.If) and _mentions_version(n.test)):
            for m in ast.walk(n):
                if isinstance(m, (ast.Import, ast.ImportFrom)):
                    guarded.add(id(m))
        if isinstance(n, ast.If) and "TYPE_CHECKING" in (
                getattr(n.test, "id", ""), getattr(n.test, "attr", "")):
            for m in ast.walk(n):
                guarded.add(id(m))
    exited = False
    for stmt in tree.body:
        if isinstance(stmt, ast.If) and _mentions_version(stmt.test) and _exits(stmt.body):
            exited = True
        elif exited and isinstance(stmt, (ast.Import, ast.ImportFrom)):
            guarded.add(id(stmt))

    # Annotations Python evaluates at definition time: function signatures,
    # and AnnAssign outside function bodies.
    evaluated = []
    local_ann = set()
    for n in ast.walk(tree):
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            for body_node in (n.body if isinstance(n.body, list) else []):
                for m in ast.walk(body_node):
                    if isinstance(m, ast.AnnAssign):
                        local_ann.add(id(m))
    for n in ast.walk(tree):
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
            a = n.args
            args = a.posonlyargs + a.args + a.kwonlyargs + [x for x in (a.vararg, a.kwarg) if x]
            evaluated += [x.annotation for x in args if x.annotation is not None]
            if n.returns is not None:
                evaluated.append(n.returns)
        elif isinstance(n, ast.AnnAssign) and id(n) not in local_ann:
            evaluated.append(n.annotation)
    ann_nodes = set()
    for n in ast.walk(tree):
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
            a = n.args
            for x in a.posonlyargs + a.args + a.kwonlyargs + [x for x in (a.vararg, a.kwarg) if x]:
                if x.annotation is not None:
                    ann_nodes.update(id(m) for m in ast.walk(x.annotation))
            if n.returns is not None:
                ann_nodes.update(id(m) for m in ast.walk(n.returns))
        elif isinstance(n, ast.AnnAssign):
            ann_nodes.update(id(m) for m in ast.walk(n.annotation))
    if not future:
        for ann in evaluated:
            if _has_union(ann):
                findings.append(f"{path}:{ann.lineno}: `X | Y` annotation is evaluated on 3.9 "
                                "(TypeError); add `from __future__ import annotations`")

    for n in ast.walk(tree):
        if isinstance(n, ast.Import) and id(n) not in guarded:
            for a in n.names:
                top = a.name.split(".")[0]
                if top in NEW_MODULES:
                    findings.append(f"{path}:{n.lineno}: `import {top}` needs "
                                    f"{NEW_MODULES[top]}; guard it (try/except ImportError)")
        elif isinstance(n, ast.ImportFrom) and id(n) not in guarded and n.module:
            top = n.module.split(".")[0]
            if top in NEW_MODULES:
                findings.append(f"{path}:{n.lineno}: `from {n.module} import` needs "
                                f"{NEW_MODULES[top]}; guard it (try/except ImportError)")
            for a in n.names:
                v = NEW_NAMES.get((n.module, a.name))
                if v:
                    findings.append(f"{path}:{n.lineno}: {n.module}.{a.name} needs {v}")
        elif (isinstance(n, ast.BinOp) and isinstance(n.op, ast.BitOr)
              and id(n) not in ann_nodes and _is_typeish(n)):
            findings.append(f"{path}:{n.lineno}: `X | Y` type union as a value needs 3.10 "
                            "(TypeError on 3.9; __future__ does not help); use a tuple or Optional")
        elif isinstance(n, ast.Call) and getattr(n.func, "id", "") == "zip" and any(
                k.arg == "strict" for k in n.keywords):
            findings.append(f"{path}:{n.lineno}: zip(strict=) needs 3.10")
        elif (isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name)
              and (alias.get(n.value.id, n.value.id), n.attr) in NEW_NAMES
              and alias.get(n.value.id, n.value.id) != "typing"):
            mod = alias.get(n.value.id, n.value.id)
            findings.append(f"{path}:{n.lineno}: {mod}.{n.attr} needs {NEW_NAMES[(mod, n.attr)]}")
    # Several evaluated annotations nest (BinOp inside BinOp); report a line once.
    seen, out = set(), []
    for f in findings:
        if f not in seen:
            seen.add(f)
            out.append(f)
    return out


# (name, source, must_fail)
FIXTURES = [
    ("unguarded tomllib", "import tomllib\n", True),
    ("unguarded from-tomllib", "from tomllib import loads\n", True),
    ("union in signature", "def f(x: int | None) -> None:\n    pass\n", True),
    ("union in return", "def f() -> 'x' | None:\n    pass\n", True),
    ("module-level union annotation", "x: int | None = None\n", True),
    ("class-level union annotation", "class C:\n    x: str | None = None\n", True),
    ("union as value", "X = int | None\n", True),
    ("union in isinstance", "def g(v):\n    return isinstance(v, int | str)\n", True),
    ("zip strict", "list(zip([1], [2], strict=True))\n", True),
    ("datetime.UTC", "import datetime\nnow = datetime.datetime.now(datetime.UTC)\n", True),
    ("aliased datetime.UTC", "import datetime as _dt\nnow = _dt.datetime.now(_dt.UTC)\n", True),
    ("datetime.timezone.utc (3.9)", "import datetime\nnow = datetime.datetime.now(datetime.timezone.utc)\n", False),
    ("from datetime import UTC", "from datetime import UTC\n", True),
    ("typing.Self", "from typing import Self\n", True),
    ("match statement", "match 1:\n    case 1:\n        pass\n", sys.version_info < (3, 10)),
    ("guarded tomllib", "try:\n    import tomllib\nexcept ModuleNotFoundError:\n"
     "    import tomli as tomllib\n", False),
    ("nested guarded tomllib", "try:\n    import tomllib\nexcept ImportError:\n    try:\n"
     "        import tomli as tomllib\n    except ImportError:\n"
     "        raise SystemExit('needs 3.11 or tomli')\n", False),
    ("version-guarded tomllib", "import sys\nif sys.version_info < (3, 11):\n"
     "    sys.exit('needs 3.11')\nimport tomllib\n", False),
    ("if-branch tomllib", "import sys\nif sys.version_info >= (3, 11):\n    import tomllib\n", False),
    ("future + unions", "from __future__ import annotations\n"
     "def f(x: int | None) -> str | None:\n    pass\ny: int | None = None\n", False),
    ("string annotation", "def f(x: 'int | None') -> None:\n    pass\n", False),
    ("local annotation", "def f():\n    y: int | None = None\n    return y\n", False),
    ("set and int or", "s = {1} | {2}\nf = 1 | 2\ndef h(a, b):\n    return a | b\n", False),
    ("Optional", "from typing import Optional\ndef f(x: Optional[int]) -> None:\n    pass\n", False),
    ("TYPE_CHECKING import", "from typing import TYPE_CHECKING\nif TYPE_CHECKING:\n"
     "    from typing import Self\n", False),
    ("builtin generics (3.9)", "def f(x: list[int]) -> dict[str, int]:\n    return {}\n", False),
]


def self_test():
    bad = 0
    for name, src, must_fail in FIXTURES:
        got = bool(check_source(src, name))
        ok = got == must_fail
        bad += not ok
        print(f"{'ok  ' if ok else 'FAIL'} {name}: {'red' if got else 'green'}"
              f" (want {'red' if must_fail else 'green'})")
    if bad:
        print(f"self-test: {bad} fixture(s) wrong", file=sys.stderr)
        return 1
    print(f"self-test: {len(FIXTURES)} fixtures ok")
    return 0


def main(argv):
    if argv == ["--self-test"]:
        return self_test()
    if not argv or any(a.startswith("-") for a in argv):
        print(__doc__, file=sys.stderr)
        return 2
    findings = []
    for path in argv:
        with open(path, encoding="utf-8") as fh:
            findings += check_source(fh.read(), path)
    for f in findings:
        print(f)
    v = f"{sys.version_info[0]}.{sys.version_info[1]}"
    print(f"check-py-floor: {len(argv)} file(s) under Python {v}, {len(findings)} finding(s)",
          file=sys.stderr)
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
