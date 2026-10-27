#!/usr/bin/env python3
"""Generate a complete Lean word-program pattern from the pinned HOL capture."""
import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
INPUT = ROOT / "scripts/hol-probes/empty_cake_word_probe.out"
OUTPUT = ROOT / "Flapjack/Test/EmptyCakeWordOracle.lean"
CONSTRUCTORS = {
    "Seq": (".seq", 2), "Assign": (".assign", 2), "Const": (".const", 1),
    "If": (".ite", 5), "Test": (".test", 0), "Imm": (".imm", 1),
    "Skip": (".skip", 0), "Alloc": (".alloc", 2), "Var": (".var", 1),
    "Lsr": (".lsr", 0), "Lsl": (".lsl", 0), "Lower": (".lower", 0),
    "Op": (".op", 2), "Add": (".add", 0), "Sub": (".sub", 0),
    "Lookup": (".lookup", 1), "TriggerGC": (".triggerGC", 0),
    "NextFree": (".nextFree", 0), "CurrHeap": (".currHeap", 0),
    "Reg": (".reg", 1), "MustTerminate": (".mustTerminate", 1),
    "Call": (".call", 4), "SOME": ("some", 1), "NONE": ("none", 0),
    "Store": (".store", 2), "Set": (".set", 2), "Globals": (".globals", 0),
    "GlobReal": (".globReal", 0), "Return": (".return", 2), "LN": (".ln", 0),
    "FALSE_CONST": ("(.const 2)", 0),
}


def render():
    raw = INPUT.read_text().strip()
    if not raw.startswith("entry="):
        raise ValueError("missing HOL entry row")
    source = raw[6:]
    tokens = re.findall(r"-1w|0x[0-9A-Fa-f]+w|[0-9]+w|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[][(),;⦕⦖]", source)
    if "".join(tokens) != re.sub(r"\s+", "", source):
        raise ValueError("unexpected character in HOL output")
    pos = 0
    sets = []
    words = []

    def parse():
        nonlocal pos
        if pos >= len(tokens):
            raise ValueError("unexpected end of HOL output")
        token = tokens[pos]
        pos += 1
        if token == "-1w":
            name = f"word{len(words)}"
            words.append(name)
            return name
        if token.endswith("w") and (token[0].isdigit()):
            return str(int(token[:-1], 0) if token.startswith("0x") else int(token[:-1]))
        if token.isdigit():
            return token
        if token == "⦕":
            keys = []
            while tokens[pos] != "⦖":
                if not tokens[pos].isdigit():
                    raise ValueError("non-numeric live-set element")
                keys.append(tokens[pos])
                pos += 1
                if tokens[pos] == ";":
                    pos += 1
                elif tokens[pos] != "⦖":
                    raise ValueError("expected live-set separator")
            pos += 1
            name = f"live{len(sets)}"
            sets.append((name, keys))
            return name
        if token == "[":
            items = []
            while tokens[pos] != "]":
                items.append(parse())
                if tokens[pos] == ";":
                    pos += 1
                elif tokens[pos] != "]":
                    raise ValueError("expected list separator")
            pos += 1
            return "[" + ", ".join(items) + "]"
        if token == "(":
            items = [parse()]
            while tokens[pos] == ",":
                pos += 1
                items.append(parse())
            if tokens[pos] != ")":
                raise ValueError("expected closing parenthesis")
            pos += 1
            return "(" + ", ".join(items) + ")"
        if token == "ShiftN":
            op, exp, amount = parse(), parse(), parse()
            return f"(.shift {op} {exp} (.const {amount}))"
        if token == "Move0":
            return f"(.move 0 {parse()})"
        if token not in CONSTRUCTORS:
            raise ValueError(f"unsupported HOL constructor {token!r}")
        name, arity = CONSTRUCTORS[token]
        args = [parse() for _ in range(arity)]
        return "(" + " ".join([name, *args]) + ")" if args else name

    pattern = parse()
    if pos != len(tokens):
        raise ValueError("trailing HOL output")
    checks = [f"decide ({name} = Flapjack.sptListInsert [{', '.join(keys)}] .ln)" for name, keys in sets]
    checks += [f"{name} == (-1 : BitVec 64)" for name in words]
    checks = " &&\n      ".join(checks) or "true"
    return f'''-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang

namespace Flapjack.Test.EmptyCakeWordOracle

/-- Match the complete captured entry function, including every live set. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) : Bool :=
  match code with
  | {pattern} =>
      {checks}
  | _ => false

end Flapjack.Test.EmptyCakeWordOracle
'''


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = render()
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text() != expected:
            raise SystemExit(f"{OUTPUT} is stale; regenerate it from the HOL capture")
        print("EmptyCakeWordOracle matches the captured HOL output")
    else:
        OUTPUT.write_text(expected)


if __name__ == "__main__":
    main()
