#!/usr/bin/env python3
"""Render the pinned HOL bignum mini-program in the Lean mini-language."""
import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
INPUT = ROOT / "scripts/hol-probes/bignum_mini_probe.out"
OUTPUT = ROOT / "Flapjack/Compiler/Backend/WordBignum/GeneratedMini.lean"

MINI = {
    "Skip": (".skip", ()), "Continue": (".continue", ()), "Swap": (".swap", ()),
    "Assign": (".assign", ("nat", "exp")), "Delete": (".delete", ("nums",)),
    "Seq": (".seq", ("mini", "mini")), "Load": (".load", ("nat", "nat", "addr")),
    "Store": (".store", ("nat", "nat")),
    "If": (".ite", ("cmp", "nat", "reg", "mini", "mini")),
    "Add": (".add", ("nat", "nat", "nat", "reg", "reg")),
    "Sub": (".sub", ("nat", "nat", "nat", "reg", "reg")),
    "Mul": (".mul", ("nat", "nat", "nat", "nat")),
    "Div": (".div", ("nat", "nat", "nat", "nat", "nat")),
    "Loop": (".loop", ("bool", "nums", "mini")),
    "Rec": (".recurse", ("nums", "nums")), "LoopBody": (".loopBody", ("mini",)),
}
EXP = {"Var": (".var", ("nat",)), "Const": (".const", ("word",)),
       "Op": (".op", ("bin", "exps")), "Shift": (".shift", ("shift", "exp", "exp"))}
ATOMS = {"cmp": {"Equal": ".equal", "Lower": ".lower", "Less": ".less", "Test": ".test"},
         "bin": {"Add": ".add", "Sub": ".sub", "And": ".and", "Or": ".or", "Xor": ".xor"},
         "shift": {"Lsl": ".lsl", "Lsr": ".lsr", "Asr": ".asr", "Ror": ".ror"},
         "addr": {"In1": ".in1", "In2": ".in2", "Out": ".out"},
         "bool": {"T": "true", "F": "false"}}


def render():
    rows = dict(line.split("=", 1) for line in INPUT.read_text().splitlines())
    source = rows["generic"]
    if source != rows["mini"]:
        raise ValueError("polymorphic and 64-bit mini-program captures differ")
    tokens = re.findall(r"-1w|0x[0-9A-Fa-f]+w|[0-9]+w|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[][();]", source)
    if "".join(tokens) != re.sub(r"\s+", "", source):
        raise ValueError("unexpected character in mini-program capture")
    pos = 0
    fragments = []

    def parse(kind):
        nonlocal pos
        token = tokens[pos]
        pos += 1
        if token == "(":
            result = parse(kind)
            if tokens[pos] != ")":
                raise ValueError("expected closing parenthesis")
            pos += 1
            return result
        if kind in ("nums", "exps"):
            if token != "[":
                raise ValueError("expected list")
            items = []
            while tokens[pos] != "]":
                items.append(parse("nat" if kind == "nums" else "exp"))
                if tokens[pos] == ";":
                    pos += 1
                elif tokens[pos] != "]":
                    raise ValueError("expected list separator")
            pos += 1
            return "[" + ", ".join(items) + "]"
        if kind == "nat":
            if not token.isdigit():
                raise ValueError(f"expected natural number, got {token}")
            return token
        if kind == "word":
            if token == "-1w":
                return "(-1)"
            if not token.endswith("w"):
                raise ValueError(f"expected word, got {token}")
            return str(int(token[:-1], 0) if token.startswith("0x") else int(token[:-1]))
        if kind in ATOMS:
            return ATOMS[kind][token]
        if kind == "reg":
            if token == "Reg":
                return f"(.reg {parse('nat')})"
            if token == "Imm":
                return f"(.imm {parse('word')})"
            raise ValueError(f"unknown register operand {token}")
        if kind == "exp" and token == "ShiftN":
            op, exp, amount = parse("shift"), parse("exp"), parse("nat")
            return f"(.shift {op} {exp} (.const {amount}))"
        table = MINI if kind == "mini" else EXP if kind == "exp" else {}
        if token not in table:
            raise ValueError(f"unknown {kind} constructor {token}")
        name, kinds = table[token]
        args = [parse(arg_kind) for arg_kind in kinds]
        if kind == "mini":
            for index, (arg_kind, arg) in enumerate(zip(kinds, args)):
                if arg_kind == "mini" and len(arg) > 1000:
                    fragment = f"fragment{len(fragments)}"
                    fragments.append((fragment, arg))
                    args[index] = f"({fragment} width)"
        return "(" + " ".join((name, *args)) + ")" if args else name

    sys.setrecursionlimit(10000)
    body = parse("mini")
    if pos != len(tokens):
        raise ValueError("trailing tokens in mini-program capture")
    definitions = "\n\n".join(
        f"private def {name} (width : Nat) : Mini (BitVec width) :=\n  {value}"
        for name, value in fragments
    )
    return f'''-- Generated from the pinned HOL mini-program capture; do not edit.
import Flapjack.Compiler.Backend.WordBignum.Mini

namespace Flapjack.Compiler.Backend.WordBignum

{definitions}

/-- Captured source-generated mini-program, polymorphic in the word width.
The capture is regression evidence, not a port of the original shallow-to-deep
generator or a proof of cross-language equality. -/
def mcIopCode (width : Nat) : Mini (BitVec width) :=
  {body}

end Flapjack.Compiler.Backend.WordBignum
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = render()
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text() != expected:
            raise SystemExit(f"{OUTPUT} is stale; regenerate it from the HOL capture")
        print("bignum mini-program matches the captured HOL output")
    else:
        OUTPUT.write_text(expected)


if __name__ == "__main__":
    main()
