"""Small source-shape checks for reviewed native declaration regressions.

These checks do not establish HOL-to-Lean equivalence. They compare the reviewed
Lean definition body or theorem statement, allowing comments, formatting and
theorem proof changes. Lake and manual source review remain separate gates.
"""
import re
import runpy
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
strip_comments = runpy.run_path(str(ROOT / "scripts/check-hol-refs.py"))["strip_lean_comments"]

def tokens(text):
    return re.findall(r'"(?:\\.|[^"\\])*"|[\w\x27]+|[^\s]', strip_comments(text))

def declaration(text, kind, name, statement=False):
    clean = strip_comments(text)
    starts = list(re.finditer(r"(?m)^" + re.escape(kind) + r"\s+" + re.escape(name) + r"\b", clean))
    if len(starts) != 1:
        raise ValueError("expected one Lean " + kind + " " + name)
    fragment = clean[starts[0].start():]
    if statement:
        end = re.search(r"\s:=\s+by\b", fragment)
    else:
        end = re.search(r"(?m)^(?:def|theorem|abbrev|inductive|structure|end)\b", fragment[starts[0].end()-starts[0].start():])
        if end:
            offset = starts[0].end()-starts[0].start()
            return fragment[:offset + end.start()]
    if end is None:
        raise ValueError("missing Lean declaration boundary for " + name)
    return fragment[:end.start()]

def check_declaration(text, kind, name, expected, statement=False):
    if tokens(declaration(text, kind, name, statement)) != tokens(expected):
        raise ValueError("reviewed Lean native contract drift: " + name)
