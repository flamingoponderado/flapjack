#!/usr/bin/env python3
"""Generate an exhaustive Lean data-program pattern from pinned HOL output."""
import argparse
import importlib.util
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
INPUT = ROOT / "scripts/hol-probes/empty_cake_data_probe.out"
OUTPUT = ROOT / "Flapjack/Test/EmptyCakeDataOracle.lean"

spec = importlib.util.spec_from_file_location("bvi_fixture", ROOT / "scripts/generate-cake-bvi-oracles.py")
bvi = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bvi)
CONSTRUCTORS = dict(bvi.CONSTRUCTORS, **{
    "Seq": (".seq", 2), "Assign": (".assign", 4), "If": (".ifThenElse", 3),
    "Return": (".return", 1), "Call": (".call", 4), "Move": (".move", 2),
    "MakeSpace": (".makeSpace", 2), "Skip": (".skip", 0), "LN": (".ln", 0),
    "ElemAt": (".elemAt", 1),
})


def render():
    raw = INPUT.read_text().strip()
    if not raw.startswith("code="):
        raise ValueError("missing HOL code row")
    source = raw[5:]
    tokens = re.findall(r"[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[][(),;⦕⦖]", source)
    if "".join(tokens) != re.sub(r"\s+", "", source):
        raise ValueError("unexpected character in HOL output")
    pos = 0
    sets = []

    def parse():
        nonlocal pos
        if pos >= len(tokens):
            raise ValueError("unexpected end of HOL output")
        token = tokens[pos]
        pos += 1
        if token.isdigit():
            return token
        if token == "⦕":
            keys = []
            while tokens[pos] != "⦖":
                key = tokens[pos]
                if not key.isdigit():
                    raise ValueError("non-numeric live-set element")
                keys.append(key)
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
        if token not in CONSTRUCTORS:
            raise ValueError(f"unsupported HOL constructor {token!r}")
        name, arity = CONSTRUCTORS[token]
        args = [parse() for _ in range(arity)]
        return "(" + " ".join([name, *args]) + ")" if args else name

    pattern = parse()
    if pos != len(tokens):
        raise ValueError("trailing HOL output")
    checks = " &&\n      ".join(
        f"decide ({name} = Flapjack.sptListInsert [{', '.join(keys)}] .ln)" for name, keys in sets
    ) or "true"
    return f'''-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Compiler.Backend.DataLang.Syntax

namespace Flapjack.Test.EmptyCakeDataOracle

/-- Match every location, arity, expression and live set in the captured program. -/
def matchesCaptured (code : List (Nat × Nat × Flapjack.Compiler.Backend.DataLang.Prog)) : Bool :=
  match code with
  | {pattern} =>
      {checks}
  | _ => false

end Flapjack.Test.EmptyCakeDataOracle
'''


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = render()
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text() != expected:
            raise SystemExit(f"{OUTPUT} is stale; regenerate it from the HOL capture")
        print("Full empty CakeML data fixture matches the captured HOL output")
    else:
        OUTPUT.write_text(expected)


if __name__ == "__main__":
    main()
