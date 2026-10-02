#!/usr/bin/env python3
"""Reject native proof/trust tokens outside comments in tracked Lean sources.

The existing native_decide allowlist is enforced by check-native-decide.sh.
These additional mechanisms have no allowance. This is a conservative lexical
ratchet (strings still count), not an audit of elaborated theorem axioms.
"""

import re
import subprocess
import sys
from pathlib import Path


FORBIDDEN = re.compile(r"\b(bv_decide|ofReduceBool|trustCompiler)\b")
CHAR = re.compile(r"'(?:\\.|[^\\'])'")
MARKER = re.compile(r'''--|/-|["']''')
BLOCK = re.compile(r"/-|-/")
STRING = re.compile(r'\\[\s\S]|"')
NOT_NEWLINE = re.compile(r"[^\n]")


def without_comments(source: str) -> str:
    """Blank nested/line comments, keeping positions and quoted contents intact."""
    result = []
    i = 0
    while i < len(source):
        marker = MARKER.search(source, i)
        if marker is None:
            result.append(source[i:])
            break
        start = marker.start()
        result.append(source[i:start])
        token = marker.group()
        if token == "--":
            i = start
            end = source.find("\n", i)
            if end < 0:
                end = len(source)
        elif token == "/-":
            i = start
            depth, end = 1, i + 2
            while depth:
                inner = BLOCK.search(source, end)
                if inner is None:
                    end = len(source)
                    break
                depth += 1 if inner.group() == "/-" else -1
                end = inner.end()
        elif token == '"':
            end = marker.end()
            while True:
                inner = STRING.search(source, end)
                if inner is None:
                    end = len(source)
                    break
                end = inner.end()
                if inner.group() == '"':
                    break
            result.append(source[start:end])
            i = end
            continue
        else:
            char = CHAR.match(source, start)
            end = char.end() if char is not None else marker.end()
            result.append(source[start:end])
            i = end
            continue
        result.append(NOT_NEWLINE.sub(" ", source[i:end]))
        i = end
    return "".join(result)


def violations(source: str) -> list[tuple[int, str]]:
    text = without_comments(source)
    return [(text.count("\n", 0, match.start()) + 1, match.group())
            for match in FORBIDDEN.finditer(text)]


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    paths = subprocess.check_output(
        ["git", "ls-files", "-z", "--", "*.lean"], cwd=root
    ).decode().split("\0")
    failed = False
    for name in paths:
        if not name:
            continue
        path = root / name
        if not path.exists():  # A tracked deletion has no remaining source use.
            continue
        for line, token in violations(path.read_text(encoding="utf-8")):
            print(f"FAIL {name}:{line}: {token} has no native-trust allowance")
            failed = True
    if failed:
        print("Use a kernel-checked proof; inspect #print axioms for affected theorems.",
              file=sys.stderr)
        return 1
    print("native trust: no bv_decide, ofReduceBool or trustCompiler uses")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
