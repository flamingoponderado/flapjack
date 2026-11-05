#!/usr/bin/env python3
"""Report theorems that no other declaration uses (informational, not a gate).

Issue #1275 asks which lemmas of the Pancake port can be folded away.  The
cheapest are the ones nothing uses.  This script lists, for the modules under
a prefix (default ``Flapjack.Pancake``), the untagged theorems that are not
reachable from any other declaration of the ``Flapjack`` library; see
``scripts/UnusedTheorems.lean`` for the exact rule.

Names that occur outside Lean proofs are kept as roots: every identifier in
the tracked Markdown, Python, shell, JSON (except the theorem inventory
``docs/HOL-THEOREM-MAP.json``, which lists every Proofs theorem), TOML, YAML
and text files and in ``Flapjack/Test`` and ``scripts`` Lean files.  This is
deliberately coarse (a leaf name mentioned anywhere protects every theorem
with that leaf name) so the report errs towards keeping a theorem.

Only theorems written as a ``theorem``/``lemma`` in the source file of their
module are printed; generated equation and structure lemmas are dropped.

The Lean half imports the whole ``Flapjack`` library, so run
``lake build Flapjack`` first.  It runs ``lake env lean`` and therefore counts
as a Lake command: do not run it concurrently with other Lake commands in the
same worktree.

Usage::

    python3 scripts/report-unused-theorems.py                       # Pancake
    python3 scripts/report-unused-theorems.py --prefix Flapjack.Pancake.Proofs.PanSimp
    python3 scripts/report-unused-theorems.py --json
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile
from collections import Counter

TEXT_GLOBS = ["*.md", "*.py", "*.sh", "*.json", "*.toml", "*.txt", "*.yml", "*.yaml",
              "Flapjack/Test/*.lean", "scripts/*.lean"]
EXCLUDED_TEXT = {"docs/HOL-THEOREM-MAP.json"}
TOKEN_RE = re.compile(r"[A-Za-z_][\w?!'.]*")
THEOREM_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+"
    r"([^\s:(\[{]+)",
    re.MULTILINE,
)


def text_roots(repo: pathlib.Path) -> set[str]:
    files = subprocess.run(["git", "ls-files", *TEXT_GLOBS], cwd=repo, check=True,
                           capture_output=True, text=True).stdout.split()
    names: set[str] = set()
    for f in files:
        if f in EXCLUDED_TEXT or f.startswith(("cakeml/", "HOL/")):
            continue
        path = repo / f
        if not path.is_file():
            continue
        for tok in TOKEN_RE.findall(path.read_text(encoding="utf-8", errors="replace")):
            names.add(tok.rsplit(".", 1)[-1])
    return names


def source_theorems(path: pathlib.Path) -> set[str]:
    """Leaf names of the theorems written in a Lean source file."""
    if not path.is_file():
        return set()
    text = path.read_text(encoding="utf-8", errors="replace")
    return {m.group(1).rsplit(".", 1)[-1] for m in THEOREM_RE.finditer(text)}


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--prefix", default="Flapjack.Pancake",
                    help="module prefix whose theorems are candidates (default: %(default)s)")
    ap.add_argument("--json", action="store_true", help="print the report as JSON")
    args = ap.parse_args(argv)

    repo = pathlib.Path(__file__).resolve().parent.parent
    with tempfile.TemporaryDirectory() as tmp:
        roots_file = pathlib.Path(tmp) / "text-roots.txt"
        roots_file.write_text("\n".join(sorted(text_roots(repo))) + "\n")
        env = dict(os.environ, UNUSED_THEOREMS_PREFIX=args.prefix,
                   UNUSED_THEOREMS_TEXT_ROOTS=str(roots_file))
        proc = subprocess.run(["lake", "env", "lean", "scripts/UnusedTheorems.lean"],
                              cwd=repo, env=env, capture_output=True, text=True)
    if proc.returncode != 0:
        sys.stderr.write(proc.stdout + proc.stderr)
        return proc.returncode

    cache: dict[str, set[str]] = {}
    found: list[dict] = []
    for line in proc.stdout.splitlines():
        if "\t" not in line:
            continue
        module, name = line.split("\t", 1)
        file = module.replace(".", "/") + ".lean"
        if file not in cache:
            cache[file] = source_theorems(repo / file)
        if name.rsplit(".", 1)[-1] in cache[file]:
            found.append({"file": file, "module": module, "name": name})

    if args.json:
        json.dump({"prefix": args.prefix, "unused": found}, sys.stdout, indent=2)
        print()
        return 0
    per_file = Counter(d["file"] for d in found)
    for d in found:
        print(f"{d['file']}\t{d['name']}")
    print(f"\n{len(found)} unused theorems in {len(per_file)} files under {args.prefix}",
          file=sys.stderr)
    for file, n in per_file.most_common():
        print(f"{n:>6}  {file}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
