#!/usr/bin/env python3
"""Report Lean-to-HOL lemma density per HOL script (informational, not a gate).

Issue #1275 asks for a report that, for each cited HOL script, compares the
size of its Lean port with the script itself, so that the ratio stays visible
while passes are ported and later simplified.  For every HOL script cited by
an ``@[hol "<path>" "<name>"]`` attribute under the given Lean roots, this
script prints:

* the HOL script's lines and declarations (``Theorem``, ``Triviality``,
  ``Definition``, ``Inductive``, ``CoInductive`` and ``Datatype`` headers at
  the start of a line, outside comments);
* the Lean files attributed to it, with their lines, ``theorem``/``lemma``
  declarations and ``@[hol]`` tags citing it;
* the two ratios Lean lines / HOL lines and Lean theorems / HOL declarations.

Attribution is by file.  A Lean file belongs to the HOL script that most of
its own ``@[hol]`` tags cite (ties go to the alphabetically first script).  A
file without tags belongs to the script most cited in the nearest enclosing
directory whose subtree has tags; this attributes the helper modules that sit
beside a pass's tagged modules to that pass.  Files under a root with no tags
at all are counted as unattributed.  The attribution is a heuristic: a file
that ports parts of two scripts is counted entirely for the majority one.

Older ``val NAME = store_thm (...)`` bindings are not counted as HOL
declarations, so a script written in that style has a too-small denominator.

Usage::

    python3 scripts/check-lemma-density.py                    # Pancake subtree
    python3 scripts/check-lemma-density.py Flapjack/Compiler  # other roots
    python3 scripts/check-lemma-density.py --json             # machine-readable

The exit status is always 0 unless the arguments are invalid: the report
measures, it does not enforce.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import pathlib
import re
import sys
from collections import Counter, defaultdict

DEFAULT_ROOTS = ["Flapjack/Pancake"]
UNATTRIBUTED = "(unattributed)"

THEOREM_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s",
    re.MULTILINE,
)
HOL_TAG_RE = re.compile(r'@\[\s*hol\s+"([^"]+)"')
HOL_DECL_RE = re.compile(
    r"^(?:Theorem|Triviality|Definition|Inductive|CoInductive|Datatype)\b", re.MULTILINE
)

_RPD = pathlib.Path(__file__).resolve().parent / "report-proof-duplication.py"
_spec = importlib.util.spec_from_file_location("report_proof_duplication", _RPD)
_rpd = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_rpd)
mask_lean_comments = _rpd.mask_comments


def mask_sml_comments(text: str) -> str:
    """Blank out (nested) SML comments, keeping newlines and offsets."""
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        if text.startswith("(*", i):
            depth, j = 0, i
            while j < n:
                if text.startswith("(*", j):
                    depth += 1
                    j += 2
                elif text.startswith("*)", j):
                    depth -= 1
                    j += 2
                    if depth == 0:
                        break
                else:
                    j += 1
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        else:
            i += 1
    return "".join(out)


def lean_file_stats(text: str) -> tuple[int, int, Counter]:
    """Lines, theorem/lemma declarations and cited HOL scripts of one file.

    Tags are read from the raw text, but only where the ``@[`` is not inside
    a comment; theorem headers are read from the comment-masked text."""
    masked = mask_lean_comments(text)
    theorems = len(THEOREM_RE.findall(masked))
    tags: Counter = Counter()
    for m in HOL_TAG_RE.finditer(text):
        if masked[m.start()] == "@":
            tags[m.group(1)] += 1
    return text.count("\n"), theorems, tags


def hol_file_stats(path: pathlib.Path) -> tuple[int, int] | None:
    if not path.is_file():
        return None
    text = path.read_text(encoding="utf-8", errors="replace")
    return text.count("\n"), len(HOL_DECL_RE.findall(mask_sml_comments(text)))


def majority(tags: Counter) -> str | None:
    if not tags:
        return None
    return min(tags.items(), key=lambda kv: (-kv[1], kv[0]))[0]


def attribute(files: dict[str, Counter]) -> dict[str, str]:
    """Map each Lean file (a ``/``-separated relative path) to a HOL script."""
    subtree: dict[str, Counter] = defaultdict(Counter)
    for f, tags in files.items():
        parts = f.split("/")[:-1]
        for i in range(len(parts) + 1):
            subtree["/".join(parts[:i])].update(tags)
    result = {}
    for f, tags in files.items():
        script = majority(tags)
        parts = f.split("/")[:-1]
        while script is None and parts is not None:
            script = majority(subtree.get("/".join(parts), Counter()))
            parts = parts[:-1] if parts else None
        result[f] = script or UNATTRIBUTED
    return result


def ratio(a: int, b: int) -> float | None:
    return round(a / b, 1) if b else None


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("roots", nargs="*", default=DEFAULT_ROOTS,
                    help="Lean files or directories to scan (default: %(default)s)")
    ap.add_argument("--sort", choices=["lines", "line-ratio", "theorem-ratio", "script"],
                    default="lines", help="row order (default: Lean lines, largest first)")
    ap.add_argument("--json", action="store_true", help="print the report as JSON")
    args = ap.parse_args(argv)

    repo = pathlib.Path(__file__).resolve().parent.parent
    paths: list[pathlib.Path] = []
    for root in args.roots:
        p = pathlib.Path(root) if pathlib.Path(root).is_absolute() else repo / root
        if p.is_file():
            paths.append(p)
        elif p.is_dir():
            paths.extend(sorted(p.rglob("*.lean")))
        else:
            ap.error(f"no such file or directory: {root}")

    stats: dict[str, tuple[int, int, Counter]] = {}
    for p in paths:
        rp = p.resolve()
        rel = rp.relative_to(repo).as_posix() if rp.is_relative_to(repo) else rp.as_posix()
        stats[rel] = lean_file_stats(p.read_text(encoding="utf-8", errors="replace"))
    owner = attribute({f: s[2] for f, s in stats.items()})

    rows: dict[str, dict] = {}
    for f, (lines, theorems, tags) in stats.items():
        script = owner[f]
        row = rows.setdefault(script, {"script": script, "lean_files": 0, "lean_lines": 0,
                                       "lean_theorems": 0, "hol_tags": 0})
        row["lean_files"] += 1
        row["lean_lines"] += lines
        row["lean_theorems"] += theorems
    for f, (_, _, tags) in stats.items():
        for script, n in tags.items():
            if script in rows:
                rows[script]["hol_tags"] += n
    for script, row in rows.items():
        hol = None if script == UNATTRIBUTED else hol_file_stats(repo / script)
        row["hol_lines"], row["hol_declarations"] = hol if hol else (None, None)
        row["line_ratio"] = ratio(row["lean_lines"], row["hol_lines"] or 0)
        row["theorem_ratio"] = ratio(row["lean_theorems"], row["hol_declarations"] or 0)

    def key(r: dict):
        if args.sort == "script":
            return r["script"]
        if args.sort == "line-ratio":
            return -(r["line_ratio"] or 0)
        if args.sort == "theorem-ratio":
            return -(r["theorem_ratio"] or 0)
        return -r["lean_lines"]

    ordered = sorted(rows.values(), key=key)
    totals = {k: sum(r[k] or 0 for r in ordered)
              for k in ("lean_files", "lean_lines", "lean_theorems", "hol_tags",
                        "hol_lines", "hol_declarations")}

    if args.json:
        json.dump({"roots": args.roots, "scripts": ordered, "totals": totals},
                  sys.stdout, indent=2)
        print()
        return 0

    def fmt(v) -> str:
        return "-" if v is None else str(v)

    header = (f"{'HOL lines':>9} {'decls':>6} | {'files':>5} {'Lean lines':>10} {'thms':>6} "
              f"{'tags':>5} | {'lines x':>7} {'thms x':>6}  HOL script")
    print(header)
    print("-" * len(header))
    for r in ordered:
        print(f"{fmt(r['hol_lines']):>9} {fmt(r['hol_declarations']):>6} | "
              f"{r['lean_files']:>5} {r['lean_lines']:>10} {r['lean_theorems']:>6} "
              f"{r['hol_tags']:>5} | {fmt(r['line_ratio']):>7} {fmt(r['theorem_ratio']):>6}  "
              f"{r['script']}")
    print("-" * len(header))
    print(f"{totals['hol_lines']:>9} {totals['hol_declarations']:>6} | "
          f"{totals['lean_files']:>5} {totals['lean_lines']:>10} {totals['lean_theorems']:>6} "
          f"{totals['hol_tags']:>5} | {fmt(ratio(totals['lean_lines'], totals['hol_lines'])):>7} "
          f"{fmt(ratio(totals['lean_theorems'], totals['hol_declarations'])):>6}  "
          f"total ({len(ordered)} scripts)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
