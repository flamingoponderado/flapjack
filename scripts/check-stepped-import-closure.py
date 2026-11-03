#!/usr/bin/env python3
"""Check that the stepped source semantics is a removable leaf (issue #1251).

The modules listed in `scripts/stepped-modules.txt` hold the step-counted source
semantics, which is moving to the stepped-flapjack repository. No other module
may import them, directly or transitively, except:

- the umbrellas `Flapjack` (`Flapjack.lean`) and `Flapjack.Tests`;
- the test modules listed in `scripts/stepped-test-allowlist.txt`, which still
  exercise the stepped semantics and move or change with it in phase 4.

So the rule covers the whole library, every `lean_exe` root and every
`@[hol]`-tagged module. The allowlist is a ratchet: a test module that is not
listed must not reach a stepped module, and a listed one that no longer reaches
one must be removed from the list.

Imports are read from the file headers of the tracked Lean sources, with
comments removed by `check-native-trust.py`'s `without_comments`. An import
line that cannot be parsed, or an import of a `Flapjack` module with no tracked
source, is an error. Each violation is reported with an import chain from the
offending module to a stepped module.
"""

import argparse
from collections import deque
import importlib.util
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = Path(__file__).resolve().parent
STEPPED_LIST = SCRIPTS / "stepped-modules.txt"
TEST_ALLOWLIST = SCRIPTS / "stepped-test-allowlist.txt"
UMBRELLAS = {"Flapjack", "Flapjack.Tests"}

_SPEC = importlib.util.spec_from_file_location("native_trust", SCRIPTS / "check-native-trust.py")
assert _SPEC is not None and _SPEC.loader is not None
_NATIVE_TRUST = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(_NATIVE_TRUST)
without_comments = _NATIVE_TRUST.without_comments

IMPORT_START = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\b")
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?((?:[^\s«]|«[^»]*»)+)\s*$")
HEADER_LINE = re.compile(r"^\s*(?:$|module\b|prelude\b)")


class ParseError(Exception):
    pass


def normalize(name):
    """Drop `«»` quoting so `Flapjack.«A»` and `Flapjack.A` are the same module."""
    return name.replace("«", "").replace("»", "")


def header_imports(source):
    """Imports in the file header, which ends at the first other command."""
    found = []
    for line in without_comments(source).splitlines():
        if IMPORT_START.match(line):
            match = IMPORT.match(line)
            if match is None:
                raise ParseError(f"cannot parse import line: {line.strip()!r}")
            found.append(normalize(match.group(1)))
        elif not HEADER_LINE.match(line):
            break
    return found


def read_list(path):
    """Module names from a list file; blank lines and `#` comments are ignored."""
    names = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.split("#", 1)[0].strip()
        if line:
            names.append(line)
    return names


def module_imports(root):
    """Map each tracked `Flapjack` module to the modules it imports."""
    listed = subprocess.run(["git", "-C", str(root), "ls-files", "-z", "Flapjack.lean", "Flapjack"],
                            capture_output=True, check=True).stdout.decode("utf-8")
    imports = {}
    for name in listed.split("\0"):
        if not name.endswith(".lean"):
            continue
        module = normalize(name[:-len(".lean")].replace("/", "."))
        try:
            imports[module] = header_imports((root / name).read_text(encoding="utf-8"))
        except ParseError as error:
            raise ParseError(f"{name}: {error}") from None
    return imports


def unresolved(imports):
    """`(module, import)` pairs naming a `Flapjack` module with no tracked source."""
    return [(module, target) for module in sorted(imports) for target in imports[module]
            if (target == "Flapjack" or target.startswith("Flapjack.")) and target not in imports]


def reaching(imports, stepped):
    """Map each module that reaches a stepped module to its next step on a shortest chain.

    Stepped modules map to `None`. One reverse breadth-first search from the
    stepped set computes this for the whole graph.
    """
    importers = {}
    for module, targets in imports.items():
        for target in targets:
            importers.setdefault(target, []).append(module)
    following = {name: None for name in sorted(stepped)}
    queue = deque(sorted(stepped))
    while queue:
        current = queue.popleft()
        for module in sorted(importers.get(current, [])):
            if module not in following:
                following[module] = current
                queue.append(module)
    return following


def chain(following, module):
    path = [module]
    while following[path[-1]] is not None:
        path.append(following[path[-1]])
    return path


def violations(imports, stepped, allowed_tests=()):
    """Return `(module, chain)` for each non-exempt module that reaches a stepped one."""
    stepped = set(stepped)
    exempt = stepped | UMBRELLAS | set(allowed_tests)
    following = reaching(imports, stepped)
    return [(module, chain(following, module)) for module in sorted(imports)
            if module in following and module not in exempt]


def stale_allowlist(imports, stepped, allowed_tests):
    """Allowlisted test modules that are missing or no longer reach a stepped module."""
    following = reaching(imports, set(stepped))
    return [name for name in allowed_tests if name not in following]


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--stepped-list", type=Path, default=STEPPED_LIST)
    parser.add_argument("--test-allowlist", type=Path, default=TEST_ALLOWLIST)
    args = parser.parse_args()

    stepped = read_list(args.stepped_list)
    allowed = read_list(args.test_allowlist)
    try:
        imports = module_imports(args.root)
    except ParseError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1

    errors = [f"listed stepped module {name} has no tracked source"
              for name in stepped if name not in imports]
    errors += [f"{module} imports {target}, which has no tracked source"
               for module, target in unresolved(imports)]
    errors += [f"allowlisted test module {name} is missing or no longer reaches a stepped "
               f"module; remove it from {args.test_allowlist.name}"
               for name in stale_allowlist(imports, stepped, allowed)]
    found = violations(imports, stepped, allowed)
    for error in errors:
        print(f"error: {error}", file=sys.stderr)
    if found:
        print(f"FAIL: {len(found)} module(s) import stepped modules:", file=sys.stderr)
        for module, path in found:
            print(f"  {module}: {' -> '.join(path)}", file=sys.stderr)
    if errors or found:
        return 1
    checked = len(imports) - len(set(stepped)) - len(UMBRELLAS & set(imports)) - len(allowed)
    print(f"stepped import closure: {len(stepped)} stepped module(s), {len(allowed)} "
          f"allowlisted test module(s), {checked} other module(s) checked; no violations")
    return 0


if __name__ == "__main__":
    sys.exit(main())
