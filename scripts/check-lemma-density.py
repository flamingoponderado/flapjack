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
* the two ratios Lean lines / HOL lines and Lean theorems / HOL declarations
  (blank for a script that owns no Lean file).

Two totals follow: over the scripts that own at least one Lean file, and over
all rows (including unattributed files and scripts cited only by minority
tags).

Attribution is by file.  A Lean file belongs to the HOL script that most of
its own ``@[hol]`` tags cite (ties go to the alphabetically first script).  A
file without tags belongs to the script most cited in the nearest enclosing
directory whose subtree has tags; this attributes the helper modules that sit
beside a pass's tagged modules to that pass.  The search never goes above the
scanned root containing the file, so separate roots do not borrow each other's
tags; a file under a root with no tags at all is counted as unattributed.  The
attribution is a heuristic: a file that ports parts of two scripts is counted
entirely for the majority one, and the other script's row (which every cited
script gets, possibly with no files) counts only that tag.

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
    """Blank out (nested) SML comments, keeping newlines and offsets.

    String literals are skipped, so a ``(*`` inside a string does not open a
    comment; inside a comment, strings are not special (as in SML)."""
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
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            i = j + 1
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


def attribute(files: dict[str, Counter], roots: list[str] | None = None) -> dict[str, str]:
    """Map each Lean file (a ``/``-separated relative path) to a HOL script.

    ``roots`` are the scanned directories (``/``-separated, relative); the
    fallback for an untagged file never looks above the root containing it,
    so separate roots do not borrow each other's tags.  A file given directly
    as a root, or outside every root, falls back no further than its own
    directory."""
    # ``None`` (the default) means one root covering every file; an empty list
    # (only file roots were given) means no directory root at all.
    roots = [r.rstrip("/") for r in ([""] if roots is None else roots)]
    subtree: dict[str, Counter] = defaultdict(Counter)
    for f, tags in files.items():
        parts = f.split("/")[:-1]
        for i in range(len(parts) + 1):
            subtree["/".join(parts[:i])].update(tags)
    result = {}
    for f, tags in files.items():
        parts = f.split("/")[:-1]
        enclosing = [r for r in roots if r == "" or f.startswith(r + "/")]
        floor = max((len(r.split("/")) if r else 0) for r in enclosing) if enclosing else len(parts)
        script = majority(tags)
        while script is None and len(parts) >= floor:
            script = majority(subtree.get("/".join(parts), Counter()))
            if not parts:
                break
            parts = parts[:-1]
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
    def rel(p: pathlib.Path) -> str:
        rp = p.resolve()
        return rp.relative_to(repo).as_posix() if rp.is_relative_to(repo) else rp.as_posix()

    paths: list[pathlib.Path] = []
    dir_roots: list[str] = []
    for root in args.roots:
        p = pathlib.Path(root) if pathlib.Path(root).is_absolute() else repo / root
        if p.is_file():
            paths.append(p)
        elif p.is_dir():
            paths.extend(sorted(p.rglob("*.lean")))
            dir_roots.append(rel(p))
        else:
            ap.error(f"no such file or directory: {root}")

    stats: dict[str, tuple[int, int, Counter]] = {}
    for p in paths:
        stats[rel(p)] = lean_file_stats(p.read_text(encoding="utf-8", errors="replace"))
    owner = attribute({f: s[2] for f, s in stats.items()}, dir_roots)

    rows: dict[str, dict] = {}

    def row_for(script: str) -> dict:
        return rows.setdefault(script, {"script": script, "lean_files": 0, "lean_lines": 0,
                                        "lean_theorems": 0, "hol_tags": 0})

    for f, (lines, theorems, tags) in stats.items():
        row = row_for(owner[f])
        row["lean_files"] += 1
        row["lean_lines"] += lines
        row["lean_theorems"] += theorems
        # Every cited script gets a row, even one that owns no file (cited
        # only by minority tags), so that no tag or HOL script is dropped.
        for script, n in tags.items():
            row_for(script)["hol_tags"] += n
    for script, row in rows.items():
        hol = None if script == UNATTRIBUTED else hol_file_stats(repo / script)
        row["hol_lines"], row["hol_declarations"] = hol if hol else (None, None)
        # A script that owns no file has no Lean side to compare.
        owned = row["lean_files"] > 0
        row["line_ratio"] = ratio(row["lean_lines"], row["hol_lines"] or 0) if owned else None
        row["theorem_ratio"] = (ratio(row["lean_theorems"], row["hol_declarations"] or 0)
                                if owned else None)

    def key(r: dict):
        if args.sort == "script":
            return r["script"]
        if args.sort == "line-ratio":
            return -(r["line_ratio"] or 0)
        if args.sort == "theorem-ratio":
            return -(r["theorem_ratio"] or 0)
        return -r["lean_lines"]

    ordered = sorted(rows.values(), key=key)
    fields = ("lean_files", "lean_lines", "lean_theorems", "hol_tags", "hol_lines",
              "hol_declarations")
    # Two totals: over every cited script, and over the scripts that own at
    # least one Lean file.  A script cited only by minority tags adds its whole
    # HOL size but no Lean lines, so the first total's ratios are lower.
    totals = {k: sum(r[k] or 0 for r in ordered) for k in fields}
    owning = [r for r in ordered if r["lean_files"] and r["script"] != UNATTRIBUTED]
    totals_owning = {k: sum(r[k] or 0 for r in owning) for k in fields}

    if args.json:
        json.dump({"roots": args.roots, "scripts": ordered, "totals": totals,
                   "totals_owning_scripts": totals_owning},
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

    def total_line(t: dict, label: str) -> None:
        print(f"{t['hol_lines']:>9} {t['hol_declarations']:>6} | "
              f"{t['lean_files']:>5} {t['lean_lines']:>10} {t['lean_theorems']:>6} "
              f"{t['hol_tags']:>5} | {fmt(ratio(t['lean_lines'], t['hol_lines'])):>7} "
              f"{fmt(ratio(t['lean_theorems'], t['hol_declarations'])):>6}  {label}")

    total_line(totals_owning, f"total over the {len(owning)} scripts owning Lean files")
    total_line(totals, f"total over all {len(ordered)} rows (scripts cited only by "
                       f"minority tags add HOL size, no Lean lines)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
