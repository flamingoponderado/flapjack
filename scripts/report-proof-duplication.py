#!/usr/bin/env python3
"""Report proof duplication in the Lean sources (informational, not a gate).

Issue #1276 asks for a report that lists theorem counts and repeated proof
shapes per encoder module, so that deduplication work can be measured.  This
script prints, for every ``.lean`` file under the given roots:

* the number of lines and of top-level declarations (theorems separately);

and, across all of them, clusters of declarations whose proofs are nearly
identical after normalisation.

Normalisation drops comments, replaces numeric literals by ``0`` and the
declaration's own name by ``SELF``, and splits the remaining text into
tokens.  Two declarations are similar when the Jaccard similarity of their
token ``k``-gram sets reaches ``--threshold``; clusters are the connected
components of that relation.  Only declarations with at least ``--min-lines``
lines are compared, because short lemmas are often alike by design.

Usage::

    python3 scripts/report-proof-duplication.py                # encoder tree
    python3 scripts/report-proof-duplication.py Flapjack/Foo   # other roots
    python3 scripts/report-proof-duplication.py --json         # machine-readable

The exit status is always 0 unless the arguments are invalid: the report
measures, it does not enforce.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys
from collections import defaultdict

DEFAULT_ROOTS = ["Flapjack/Compiler/Encoders"]

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|inductive)\s+([^\s:(\[{]+)"
)
TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.!?]*|\d+|\S")
NUM_RE = re.compile(r"^\d+$")


class Decl:
    """One top-level declaration with its source span."""

    def __init__(self, path: str, kind: str, name: str, start: int, end: int, text: str):
        self.path = path
        self.kind = kind
        self.name = name
        self.start = start  # 1-based first line of the declaration keyword
        self.end = end  # 1-based last line
        self.text = text

    @property
    def lines(self) -> int:
        return self.end - self.start + 1

    def label(self) -> str:
        return f"{self.path}:{self.start} {self.name} ({self.lines} lines)"


def strip_comments(text: str) -> str:
    """Remove Lean line comments and (possibly nested) block comments."""
    out = []
    i = 0
    depth = 0
    n = len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth:
            i += 1
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def parse_decls(path: pathlib.Path, rel: str) -> list[Decl]:
    """Split a Lean file into top-level declarations.

    A declaration starts at a column-0 declaration keyword and extends to the
    line before the next column-0 line that is not part of its body (another
    declaration, a doc comment, a section command, or ``end``)."""
    lines = path.read_text(encoding="utf-8", errors="replace").split("\n")
    starts: list[tuple[int, str, str]] = []
    for idx, line in enumerate(lines):
        m = DECL_RE.match(line)
        if m:
            starts.append((idx, m.group(1), m.group(2)))
    decls = []
    for k, (idx, kind, name) in enumerate(starts):
        limit = starts[k + 1][0] if k + 1 < len(starts) else len(lines)
        end = idx + 1
        while end < limit and (lines[end] == "" or lines[end][0] in " \t)"):
            end += 1
        while end > idx + 1 and lines[end - 1].strip() == "":
            end -= 1
        decls.append(Decl(rel, kind, name, idx + 1, end, "\n".join(lines[idx:end])))
    return decls


def shingles(decl: Decl, k: int) -> set[int]:
    toks = []
    for tok in TOKEN_RE.findall(strip_comments(decl.text)):
        if tok == decl.name:
            toks.append("SELF")
        elif NUM_RE.match(tok):
            toks.append("0")
        else:
            toks.append(tok)
    if len(toks) < k:
        return {hash(tuple(toks))}
    return {hash(tuple(toks[i : i + k])) for i in range(len(toks) - k + 1)}


def clusters(decls: list[Decl], k: int, threshold: float, max_df: int) -> list[list[Decl]]:
    """Connected components of the pairwise Jaccard >= threshold relation.

    Candidate pairs come from an inverted index over shingles; shingles that
    occur in more than ``max_df`` declarations are boilerplate shared by many
    proofs and are ignored for candidate generation (not for scoring)."""
    sets = [shingles(d, k) for d in decls]
    index: dict[int, list[int]] = defaultdict(list)
    for i, s in enumerate(sets):
        for h in s:
            index[h].append(i)
    shared: dict[tuple[int, int], int] = defaultdict(int)
    for ids in index.values():
        if len(ids) < 2 or len(ids) > max_df:
            continue
        for a in range(len(ids)):
            for b in range(a + 1, len(ids)):
                shared[(ids[a], ids[b])] += 1
    parent = list(range(len(decls)))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for (a, b), _ in shared.items():
        sa, sb = sets[a], sets[b]
        inter = len(sa & sb)
        if inter / (len(sa) + len(sb) - inter) >= threshold:
            parent[find(a)] = find(b)
    groups: dict[int, list[Decl]] = defaultdict(list)
    for i, d in enumerate(decls):
        groups[find(i)].append(d)
    result = [sorted(g, key=lambda d: (d.path, d.start)) for g in groups.values() if len(g) > 1]
    result.sort(key=lambda g: -sum(d.lines for d in g))
    return result


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("roots", nargs="*", default=DEFAULT_ROOTS,
                    help="files or directories to scan (default: %(default)s)")
    ap.add_argument("--min-lines", type=int, default=20,
                    help="only compare declarations with at least this many lines")
    ap.add_argument("--threshold", type=float, default=0.8,
                    help="Jaccard similarity of token k-grams for two proofs to count as alike")
    ap.add_argument("--k", type=int, default=8, help="token k-gram length")
    ap.add_argument("--max-df", type=int, default=200,
                    help="ignore k-grams shared by more declarations than this when pairing")
    ap.add_argument("--top", type=int, default=25, help="number of clusters to print")
    ap.add_argument("--json", action="store_true", help="print the report as JSON")
    args = ap.parse_args(argv)
    if not 0 < args.threshold <= 1:
        ap.error("--threshold must be in (0, 1]")

    repo = pathlib.Path(__file__).resolve().parent.parent
    files: list[pathlib.Path] = []
    for root in args.roots:
        p = (repo / root) if not pathlib.Path(root).is_absolute() else pathlib.Path(root)
        if p.is_file():
            files.append(p)
        elif p.is_dir():
            files.extend(sorted(p.rglob("*.lean")))
        else:
            ap.error(f"no such file or directory: {root}")

    per_file = []
    decls: list[Decl] = []
    for f in files:
        rel = str(f.resolve().relative_to(repo)) if f.resolve().is_relative_to(repo) else str(f)
        ds = parse_decls(f, rel)
        decls.extend(ds)
        per_file.append({
            "file": rel,
            "lines": f.read_text(encoding="utf-8", errors="replace").count("\n"),
            "declarations": len(ds),
            "theorems": sum(1 for d in ds if d.kind in ("theorem", "lemma")),
        })

    big = [d for d in decls if d.lines >= args.min_lines]
    groups = clusters(big, args.k, args.threshold, args.max_df)
    clustered_lines = sum(d.lines for g in groups for d in g)

    if args.json:
        json.dump({
            "files": per_file,
            "settings": {"min_lines": args.min_lines, "threshold": args.threshold,
                         "k": args.k, "max_df": args.max_df},
            "compared_declarations": len(big),
            "clusters": [[{"file": d.path, "line": d.start, "name": d.name,
                           "lines": d.lines} for d in g] for g in groups],
            "lines_in_clusters": clustered_lines,
        }, sys.stdout, indent=2)
        print()
        return 0

    print(f"{'lines':>7} {'decls':>6} {'thms':>5}  file")
    for row in sorted(per_file, key=lambda r: -r["lines"]):
        print(f"{row['lines']:>7} {row['declarations']:>6} {row['theorems']:>5}  {row['file']}")
    total_lines = sum(r["lines"] for r in per_file)
    print(f"{total_lines:>7} {sum(r['declarations'] for r in per_file):>6} "
          f"{sum(r['theorems'] for r in per_file):>5}  total ({len(per_file)} files)")
    print()
    print(f"Near-duplicate proofs (>= {args.min_lines} lines, Jaccard >= {args.threshold}, "
          f"k = {args.k}): {len(groups)} clusters, {clustered_lines} lines, "
          f"out of {len(big)} compared declarations")
    for n, g in enumerate(groups[: args.top], 1):
        print(f"\n[{n}] {len(g)} declarations, {sum(d.lines for d in g)} lines")
        for d in g:
            print(f"    {d.label()}")
    if len(groups) > args.top:
        print(f"\n... {len(groups) - args.top} more clusters (raise --top to list them)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
