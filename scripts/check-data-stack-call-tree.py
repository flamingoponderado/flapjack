#!/usr/bin/env python3
"""Compare the Lean arithmetic call tree with its captured HOL definition."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
hol = (ROOT / "scripts/hol-probes/data_sem_stack_probe.out").read_text()
lean = (ROOT / "Flapjack/Compiler/Backend/DataToWord/CallTree.lean").read_text()
row = next(line for line in hol.splitlines() if line.startswith("any_arith_call_tree="))
hol_expr = row.split("=", 2)[2]
hol_expr = re.sub(r"\s*:(num|call_tree)", "", hol_expr)
hol_expr = re.sub(r"\((\d+)\)", r"\1", hol_expr)
lean_expr = lean.split("def anyArithCallTree : WordDepth.CallTree :=", 1)[1]
lean_expr = lean_expr.split("end Flapjack", 1)[0]


def parse(text, pattern, names):
    tokens = re.findall(pattern, text)
    index = 0

    def expr():
        nonlocal index
        token = tokens[index]
        index += 1
        if token == "(":
            result = expr()
            if tokens[index] != ")":
                raise ValueError("missing closing parenthesis")
            index += 1
            return result
        kind = names.get(token, token)
        if kind == "leaf":
            return (kind,)
        if kind == "call":
            label = int(tokens[index])
            index += 1
            return (kind, label, expr())
        if kind == "branch":
            return (kind, expr(), expr())
        raise ValueError(f"unexpected token: {token}")

    result = expr()
    if index != len(tokens):
        raise ValueError("extra tokens after call tree")
    return result


hol_tree = parse(hol_expr, r"Branch|Call|Leaf|\d+|[()]",
                 {"Branch": "branch", "Call": "call", "Leaf": "leaf"})
lean_tree = parse(lean_expr, r"\.branch|\.call|\.leaf|\d+|[()]",
                  {".branch": "branch", ".call": "call", ".leaf": "leaf"})
if hol_tree != lean_tree:
    raise SystemExit("Lean arithmetic call tree differs from the captured HOL definition")
print("Lean arithmetic call tree matches the captured HOL definition")
