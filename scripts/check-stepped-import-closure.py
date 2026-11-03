#!/usr/bin/env python3
"""Check that the stepped source semantics is a removable leaf (issue #1251).

The modules listed in `scripts/stepped-modules.txt` hold the step-counted source
semantics, which is moving to the stepped-flapjack repository. No other library
module may import them, directly or transitively. Only the umbrellas
`Flapjack.lean` and `Flapjack/Tests.lean`, and test modules under
`Flapjack/Test/`, may. The rule therefore
covers the executables (`Flapjack.CompileMain` and the other `lean_exe` roots)
and every `@[hol]`-tagged module.

Imports are read from the `import` lines of the tracked Lean sources. Each
violation is reported with an import chain from the offending module to a
stepped module.
"""

import argparse
from collections import deque
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
STEPPED_LIST = Path(__file__).with_name("stepped-modules.txt")
UMBRELLAS = {"Flapjack", "Flapjack.Tests"}
TEST_PREFIX = "Flapjack.Test."
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.]+)")
HEADER_LINE = re.compile(r"^\s*(?:$|--|module\b|prelude\b|(?:public\s+)?(?:meta\s+)?import\b)")
BLOCK_COMMENT = re.compile(r"/-.*?-/", re.S)


def header_imports(source):
    """Imports in the file header, which ends at the first other command."""
    found = []
    for line in BLOCK_COMMENT.sub("", source).splitlines():
        if not HEADER_LINE.match(line):
            break
        match = IMPORT.match(line)
        if match:
            found.append(match.group(1))
    return found


def read_stepped(path):
    """Module names from the list file; blank lines and `#` comments are ignored."""
    names = []
    for line in path.read_text().splitlines():
        line = line.split("#", 1)[0].strip()
        if line:
            names.append(line)
    return names


def module_imports(root):
    """Map each tracked `Flapjack` module to the modules it imports."""
    listed = subprocess.run(["git", "-C", str(root), "ls-files", "Flapjack.lean", "Flapjack"],
                            capture_output=True, text=True, check=True).stdout.split()
    imports = {}
    for name in listed:
        if not name.endswith(".lean"):
            continue
        module = name[:-len(".lean")].replace("/", ".")
        imports[module] = header_imports((root / name).read_text())
    return imports


def exempt(module, stepped):
    """Stepped modules, the umbrellas and test modules may import stepped modules."""
    return module in stepped or module in UMBRELLAS or module.startswith(TEST_PREFIX)


def violations(imports, stepped):
    """Return `(module, chain)` for each restricted module that reaches a stepped one.

    `chain` starts at the module and ends at the first stepped module reached.
    """
    stepped = set(stepped)
    found = []
    for module in sorted(imports):
        if exempt(module, stepped):
            continue
        parent = {module: None}
        queue = deque([module])
        hit = None
        while queue and hit is None:
            current = queue.popleft()
            for target in imports.get(current, []):
                if target in parent:
                    continue
                parent[target] = current
                if target in stepped:
                    hit = target
                    break
                queue.append(target)
        if hit is not None:
            chain = [hit]
            while parent[chain[-1]] is not None:
                chain.append(parent[chain[-1]])
            found.append((module, list(reversed(chain))))
    return found


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--stepped-list", type=Path, default=STEPPED_LIST)
    args = parser.parse_args()

    stepped = read_stepped(args.stepped_list)
    imports = module_imports(args.root)
    missing = [name for name in stepped if name not in imports]
    if missing:
        for name in missing:
            print(f"error: listed stepped module {name} has no source file", file=sys.stderr)
        return 1

    found = violations(imports, stepped)
    if found:
        print(f"FAIL: {len(found)} module(s) outside {TEST_PREFIX}* import stepped modules:",
              file=sys.stderr)
        for module, chain in found:
            print(f"  {module}: {' -> '.join(chain)}", file=sys.stderr)
        return 1
    restricted = sum(1 for m in imports if not exempt(m, set(stepped)))
    print(f"stepped import closure: {len(stepped)} stepped module(s), "
          f"{restricted} other library module(s) checked, no violations")
    return 0


if __name__ == "__main__":
    sys.exit(main())
