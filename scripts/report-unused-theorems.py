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

Theorems whose ``docs/HOL-THEOREM-MAP.json`` row cites a HOL declaration or
has a status other than ``no_hol_reference_pending_classification`` (for
example an untagged ``documented_mismatch`` row, which records a known HOL
counterpart and the work tracked for an exact port) are roots as well, so
the report never recommends deleting port bookkeeping, nor anything such a
theorem uses.

Theorems that carry any attribute other than ``hol`` (``@[simp]``,
``@[grind]``, ``@[ext]``, a custom simp set, ...), on the declaration or
through a later ``attribute [...] name`` command anywhere under ``Flapjack``,
are roots as well: automation can use them without naming them, so a proof
or ``example`` added later could depend on them although no stored proof
term mentions them today.

Proof terms do not record every use by name: a ``rfl`` theorem passed to
``simp``/``simpa``/``rw``/``dsimp`` is applied by definitional unfolding and
may leave no constant behind.  And a theorem that a surviving docstring or
module comment names is presented there as a result.  So after the Lean
half, a candidate whose name occurs anywhere in a ``Flapjack`` Lean file,
comments included, outside the candidate declarations and their attached
comments is kept, and this is repeated until nothing changes; a mention
inside another unused theorem does not keep it.

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
import importlib.util

TEXT_GLOBS = ["*.md", "*.py", "*.sh", "*.json", "*.toml", "*.txt", "*.yml", "*.yaml",
              "Flapjack/Test/*.lean", "scripts/*.lean"]
EXCLUDED_TEXT = {"docs/HOL-THEOREM-MAP.json"}  # read by inventory_roots instead
TOKEN_RE = re.compile(r"[A-Za-z_][\w?!'.]*")
THEOREM_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+"
    r"([^\s:(\[{]+)",
    re.MULTILINE,
)


def text_roots(repo: pathlib.Path) -> set[str]:
    """Every dotted component of every identifier in the tracked text files.

    A dotted mention such as ``foo.mp`` protects ``foo`` as well as ``mp``."""
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
            names.update(tok.split("."))
    return names


_RPD = pathlib.Path(__file__).resolve().parent / "report-proof-duplication.py"
_spec = importlib.util.spec_from_file_location("report_proof_duplication", _RPD)
_rpd = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_rpd)

DECL_AFTER_ATTRS_RE = re.compile(
    r"\s*(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev|instance|"
    r"structure|inductive|opaque|axiom)\s+([^\s:(\[{]+)"
)
ATTRIBUTE_CMD_RE = re.compile(r"^attribute\s*\[", re.MULTILINE)


def _bracket_end(text: str, start: int) -> int:
    """Index just past the ``]`` matching the ``[`` at ``start``."""
    depth = 0
    for i in range(start, len(text)):
        if text[i] == "[":
            depth += 1
        elif text[i] == "]":
            depth -= 1
            if depth == 0:
                return i + 1
    return len(text)


def _attribute_names(content: str) -> list[str]:
    """Attribute names in the body of ``@[...]``/``attribute [...]``."""
    names, depth, item = [], 0, ""
    for ch in content + ",":
        if ch in "[(":
            depth += 1
        elif ch in "])":
            depth -= 1
        if ch == "," and depth == 0:
            words = item.split()
            words = [w for w in words if w not in ("local", "scoped", "-")]
            if words:
                names.append(words[0])
            item = ""
        else:
            item += ch
    return names


def attributed_theorems(text: str) -> set[str]:
    """Leaf names of theorems given a non-``hol`` attribute in one Lean file.

    Covers ``@[...]`` blocks before a ``theorem``/``lemma`` header and
    ``attribute [...] name ...`` commands.  Comments and strings are masked
    first."""
    masked = _rpd.mask_comments(text)
    found: set[str] = set()
    i = 0
    while True:
        i = masked.find("@[", i)
        if i < 0:
            break
        attrs: list[str] = []
        j = i
        while masked.startswith("@[", j):
            end = _bracket_end(masked, j + 1)
            attrs += _attribute_names(masked[j + 2 : end - 1])
            j = end
            while j < len(masked) and masked[j].isspace():
                j += 1
        m = DECL_AFTER_ATTRS_RE.match(masked, j)
        if m and m.group(1) in ("theorem", "lemma") and any(a != "hol" for a in attrs):
            found.add(m.group(2).rsplit(".", 1)[-1])
        i = max(j, i + 2)
    for m in ATTRIBUTE_CMD_RE.finditer(masked):
        start = m.end() - 1
        end = _bracket_end(masked, start)
        attrs = _attribute_names(masked[start + 1 : end - 1])
        # The names run to the next line that starts in column 0, so a
        # command whose names continue on indented lines is covered.
        nxt = re.compile(r"\n(?=\S)").search(masked, end)
        rest = masked[end : len(masked) if nxt is None else nxt.start()]
        if any(a != "hol" for a in attrs):
            for tok in rest.split():
                found.update(tok.split("."))
    return found


def automation_roots(repo: pathlib.Path) -> set[str]:
    files = subprocess.run(["git", "ls-files", "Flapjack/*.lean", "Flapjack.lean"], cwd=repo,
                           check=True, capture_output=True, text=True).stdout.split()
    names: set[str] = set()
    for f in files:
        path = repo / f
        if path.is_file():
            names |= attributed_theorems(path.read_text(encoding="utf-8", errors="replace"))
    return names


def drop_named_uses(repo: pathlib.Path, found: list[dict]) -> list[dict]:
    """Keep only candidates that no surviving Lean source names.

    Every token of every ``Flapjack`` Lean file counts, comments and strings
    included, except the lines of candidate declarations and their attached
    comments, as split by ``report-proof-duplication.py``'s parser; so
    ``example``s, attribute commands, macros and documentation count too.  Every dotted component of a token counts,
    so ``simp [foo.mp]`` names ``foo``.  Iterates to a fixed point: a candidate
    named elsewhere stops being a candidate, and its own body then counts."""
    if not found:
        return []
    files = subprocess.run(["git", "ls-files", "Flapjack/*.lean", "Flapjack.lean"], cwd=repo,
                           check=True, capture_output=True, text=True).stdout.split()
    sources = {f: repo / f for f in files if (repo / f).is_file()}
    return filter_named_uses(sources, found)


def attached_start(lines: list[str], start: int) -> int:
    """First line (0-based) of the comments attached to a declaration.

    ``start`` is the 0-based line of the declaration keyword.  Attached are
    directly preceding ``@[...]`` and ``--`` lines, a ``/-- ... -/`` docstring
    ending directly above them, and, after blank lines, a ``/-! ... -/``
    comment that is not a section heading (``is_heading``).  A comment documenting
    only one declaration is written this way, so it goes with it."""
    k = start
    while k > 0 and (lines[k - 1].startswith("@[") or lines[k - 1].startswith("--")):
        k -= 1
    if k > 0 and lines[k - 1].rstrip().endswith("-/"):
        m = k - 1
        while m > 0 and not lines[m].lstrip().startswith("/-"):
            m -= 1
        if lines[m].startswith("/--"):
            k = m
    j = k
    while j > 0 and lines[j - 1] == "":
        j -= 1
    if j > 0 and lines[j - 1].rstrip().endswith("-/"):
        m = j - 1
        while m > 0 and not lines[m].startswith("/-"):
            m -= 1
        if lines[m].startswith("/-!") and not is_heading(lines, m):
            k = m
    return k


def is_heading(lines: list[str], m: int) -> bool:
    """Whether the ``/-!`` comment opening on line ``m`` is a section heading.

    A heading's text starts with ``#``, either on the opening line
    (``/-! # Title``) or, after blank lines, on a later one (``/-!`` then
    ``# Title``)."""
    rest = lines[m][3:].strip()
    i = m
    while not rest and i + 1 < len(lines):
        i += 1
        rest = lines[i].strip()
    return rest.startswith("#")


def filter_named_uses(sources: dict[str, pathlib.Path], found: list[dict]) -> list[dict]:
    """``drop_named_uses`` over explicit ``{relative path: file}`` sources.

    Mentions in comments and strings count: a theorem that a surviving
    docstring or module comment names is presented as a result, so the
    report keeps it.  The lines of a candidate declaration, including its
    attached comments (``attached_start``), do not count."""
    lines_of: dict[str, list[set[str]]] = {}
    spans: dict[tuple[str, str], list[tuple[int, int]]] = {}
    for f, path in sources.items():
        raw = path.read_text(encoding="utf-8", errors="replace")
        lines = raw.split("\n")
        lines_of[f] = [{c for t in TOKEN_RE.findall(line) for c in t.split(".")}
                       for line in lines]
        for d in _rpd.parse_decls(path, f):
            first = attached_start(lines, d.start - 1)
            spans.setdefault((f, d.name.rsplit(".", 1)[-1]), []).append((first, d.end))
    cand = {(d["file"], d["name"].rsplit(".", 1)[-1]) for d in found}
    while True:
        excluded: dict[str, set[int]] = {}
        for key in cand:
            for first, end in spans.get(key, []):
                excluded.setdefault(key[0], set()).update(range(first, end))
        named: set[str] = set()
        for f, toks in lines_of.items():
            skip = excluded.get(f, set())
            for i, line_toks in enumerate(toks):
                if i not in skip:
                    named |= line_toks
        kept = {c for c in cand if c[1] in named}
        if not kept:
            break
        cand -= kept
    return [d for d in found if (d["file"], d["name"].rsplit(".", 1)[-1]) in cand]


INVENTORY = "docs/HOL-THEOREM-MAP.json"
PENDING = "no_hol_reference_pending_classification"


def inventory_roots(repo: pathlib.Path) -> set[str]:
    """Leaf names of Lean theorems whose inventory row is more than a placeholder."""
    path = repo / INVENTORY
    if not path.is_file():
        return set()
    return {row["lean_name"].rsplit(".", 1)[-1]
            for row in json.loads(path.read_text(encoding="utf-8"))
            if row.get("hol_path") or row.get("hol_name") or row.get("statement_status") != PENDING}


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
        roots = text_roots(repo) | automation_roots(repo) | inventory_roots(repo)
        roots_file.write_text("\n".join(sorted(roots)) + "\n")
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

    found = drop_named_uses(repo, found)

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
