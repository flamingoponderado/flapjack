#!/usr/bin/env python3
"""Translate the captured original BVI tree into an exact Lean match pattern.

The grammar deliberately accepts only constructors present in this capture;
unexpected syntax fails the check instead of silently dropping output.
"""
import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CASES = (
    (ROOT / "scripts/hol-probes/empty_cake_bvi_probe.out",
     ROOT / "Flapjack/Test/EmptyCakeBviOracle.lean", "EmptyCakeBviOracle"),
    (ROOT / "scripts/hol-probes/reference_cake_bvi_probe.out",
     ROOT / "Flapjack/Test/ReferenceCakeBviOracle.lean", "ReferenceCakeBviOracle"),
    (ROOT / "scripts/hol-probes/match_cake_bvi_probe.out",
     ROOT / "Flapjack/Test/MatchCakeBviOracle.lean", "MatchCakeBviOracle"),
    (ROOT / "scripts/hol-probes/mti_cake_bvi_probe.out",
     ROOT / "Flapjack/Test/MtiCakeBviOracle.lean", "MtiCakeBviOracle"),
    (ROOT / "scripts/hol-probes/inline_cake_bvi_probe.out",
     ROOT / "Flapjack/Test/InlineCakeBviOracle.lean", "InlineCakeBviOracle"),
    (ROOT / "scripts/hol-probes/bvl_inline_cake_bvi_probe.out",
     ROOT / "Flapjack/Test/BvlInlineCakeBviOracle.lean", "BvlInlineCakeBviOracle"),
    (ROOT / "scripts/hol-probes/bvl_handle_cake_bvi_probe.out",
     ROOT / "Flapjack/Test/BvlHandleCakeBviOracle.lean", "BvlHandleCakeBviOracle"),
)

CONSTRUCTORS = {
    "Var": (".var", 1), "Let": (".let", 2), "If": (".ifThenElse", 3),
    "Call": (".call", 4), "Op": (".op", 2),
    "IntOp": (".intOp", 1), "MemOp": (".memOp", 1), "GlobOp": (".globOp", 1),
    "BlockOp": (".blockOp", 1), "ThunkOp": (".thunkOp", 1),
    "Const": (".const", 1), "Int": (".int", 1), "TagLenEq": (".tagLenEq", 2),
    "Cons": (".cons", 1), "EqualConst": (".equalConst", 1), "CopyByte": (".copyByte", 1),
    "SetGlobal": (".setGlobal", 1), "UpdateThunk": (".updateThunk", 1),
    "GlobalsPtr": (".globalsPtr", 0), "SetGlobalsPtr": (".setGlobalsPtr", 0),
    "Add": (".add", 0), "Sub": (".sub", 0), "Less": (".less", 0), "LessConstSmall": (".lessConstSmall", 1),
    "El": (".el", 0), "Length": (".length", 0), "Update": (".update", 0),
    "RefArray": (".refArray", 0), "UpdateByte": (".updateByte", 0),
    "DerefByte": (".derefByte", 0), "LengthByte": (".lengthByte", 0),
    "Ref": (".ref", 0), "Equal": (".equal", 0), "TagEq": (".tagEq", 1), "Evaluated": (".evaluated", 0),
    "ConsExtend": (".consExtend", 1), "Div": (".div", 0), "Global": (".global", 1),
    "Label": (".label", 1), "LengthBlock": (".lengthBlock", 0), "Mult": (".mult", 0), "Tick": (".tick", 1),
    "SOME": ("some", 1), "NONE": ("none", 0), "F": ("false", 0), "T": ("true", 0),
}


def render(input_path, namespace):
    raw = input_path.read_text().strip()
    if not raw.startswith("code="):
        raise ValueError("missing HOL code row")
    source = raw[5:]
    tokens = re.findall(r"[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[][(),;]", source)
    if "".join(tokens) != re.sub(r"\s+", "", source):
        raise ValueError("unexpected character in HOL output")
    pos = 0

    def parse():
        nonlocal pos
        if pos >= len(tokens):
            raise ValueError("unexpected end of HOL output")
        token = tokens[pos]
        pos += 1
        if token.isdigit():
            return token
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
        if token == "mk_unit":
            return "(.op (.blockOp (.cons 0)) [])"
        if token == "mk_elem_at":
            base, index = parse(), parse()
            return f"(.op (.blockOp (.elemAt {index})) [{base}])"
        if token not in CONSTRUCTORS:
            raise ValueError(f"unsupported HOL constructor {token!r}")
        name, arity = CONSTRUCTORS[token]
        args = [parse() for _ in range(arity)]
        return "(" + " ".join([name, *args]) + ")" if args else name

    if namespace in ("MtiCakeBviOracle", "BvlInlineCakeBviOracle", "BvlHandleCakeBviOracle"):
        if tokens[pos] != "[":
            raise ValueError("expected BVI program list")
        pos += 1
        entries = []
        while tokens[pos] != "]":
            entries.append(parse())
            if tokens[pos] == ";":
                pos += 1
            elif tokens[pos] != "]":
                raise ValueError("expected BVI function separator")
        pos += 1
        definitions = "\n\n".join(f'''private def matches{index} (entry : Nat × Nat × Flapjack.Compiler.Backend.Bvi.Exp) : Bool :=
  match entry with
  | {pattern} => true
  | _ => false''' for index, pattern in enumerate(entries))
        names = ", ".join(f"entry{index}" for index in range(len(entries)))
        checks = " &&\n      ".join(f"matches{index} entry{index}" for index in range(len(entries))) or "true"
        body = f"  match code with\n  | [{names}] =>\n      {checks}\n  | _ => false"
    else:
        pattern = parse()
        definitions = ""
        body = f"  match code with\n  | {pattern} => true\n  | _ => false"
    if pos != len(tokens):
        raise ValueError("trailing HOL output")
    return f'''-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Compiler.Backend.Bvi.Syntax

namespace Flapjack.Test.{namespace}

{definitions}

/-- Match every location, arity and expression in the captured BVI program. -/
def matchesCaptured (code : List (Nat × Nat × Flapjack.Compiler.Backend.Bvi.Exp)) : Bool :=
{body}

end Flapjack.Test.{namespace}
'''


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for input_path, output_path, namespace in CASES:
        expected = render(input_path, namespace)
        if args.check:
            if not output_path.exists() or output_path.read_text() != expected:
                raise SystemExit(f"{output_path} is stale; regenerate it from the HOL capture")
            print(f"{namespace} matches the captured HOL output")
        else:
            output_path.write_text(expected)


if __name__ == "__main__":
    main()
