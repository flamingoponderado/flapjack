#!/usr/bin/env python3
"""Render the pinned HOL bignum code constants and mini-program in Lean."""
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


CODE_INPUT = ROOT / "scripts/hol-probes/bignum_code_defs_probe.out"
TEST_OUTPUT = ROOT / "Flapjack/Test/WordBignumMiniExpansionParity.lean"
CODE_CONST = re.compile(r"mc_[a-z0-9_]+_code$")


def lean_name(hol_const):
    """HOL `mc_add_loop1_code` is Lean `mcAddLoop1Code`."""
    head, *rest = hol_const.split("_")
    return head + "".join(part[:1].upper() + part[1:] for part in rest)


def tokenize(source):
    tokens = re.findall(r"-1w|0x[0-9A-Fa-f]+w|[0-9]+w|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[][();]", source)
    if "".join(tokens) != re.sub(r"\s+", "", source):
        raise ValueError("unexpected character in mini-program capture")
    return tokens


def translate(source, fragment_limit=None, references=None):
    """Translate one printed HOL mini program. Generated code constants become
    applications of their Lean definitions; with `fragment_limit`, large
    sub-programs are split into private fragments."""
    tokens = tokenize(source)
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
        if kind == "mini" and CODE_CONST.match(token):
            if references is None:
                raise ValueError(f"unexpected code constant {token}")
            references.append(token)
            return f"({lean_name(token)} width)"
        table = MINI if kind == "mini" else EXP if kind == "exp" else {}
        if token not in table:
            raise ValueError(f"unknown {kind} constructor {token}")
        name, kinds = table[token]
        args = [parse(arg_kind) for arg_kind in kinds]
        if kind == "mini" and fragment_limit is not None:
            for index, (arg_kind, arg) in enumerate(zip(kinds, args)):
                if arg_kind == "mini" and len(arg) > fragment_limit:
                    fragment = f"fragment{len(fragments)}"
                    fragments.append((fragment, arg))
                    args[index] = f"({fragment} width)"
        return "(" + " ".join((name, *args)) + ")" if args else name

    sys.setrecursionlimit(10000)
    body = parse("mini")
    if pos != len(tokens):
        raise ValueError("trailing tokens in mini-program capture")
    return body, fragments


def render():
    rows = dict(line.split("=", 1) for line in CODE_INPUT.read_text().splitlines())
    defs = {}
    for label, source in rows.items():
        if not label.endswith("_code_def"):
            raise ValueError(f"unexpected row {label}")
        const = label[: -len("_def")]
        references = []
        body, _ = translate(source, references=references)
        defs[const] = (body, references)
    order = []
    seen = set()

    def visit(const, stack=()):
        if const in seen:
            return
        if const in stack:
            raise ValueError(f"cyclic code constants at {const}")
        if const not in defs:
            raise ValueError(f"missing captured definition for {const}")
        for dep in sorted(set(defs[const][1])):
            visit(dep, stack + (const,))
        seen.add(const)
        order.append(const)

    for const in sorted(defs):
        visit(const)
    if "mc_iop_code" not in defs:
        raise ValueError("mc_iop_code is not among the captured definitions")
    blocks = []
    for const in order:
        body, _ = defs[const]
        name = lean_name(const)
        blocks.append(f'''/-- HOL `{const}`, defined by `to_deep` (`Define`) when translating the
shallow `{const[:-len("_code")]}`; generated code constants it mentions are the
corresponding Lean definitions. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "{const}_def"
  (words_as_type_indexed_bitvec)]
def {name} (width : Nat) [NeZero width] : Mini (BitVec width) :=
  {body}''')
    definitions = "\n\n".join(blocks)
    return f'''-- Generated from the pinned HOL code-constant capture
-- (scripts/hol-probes/bignum_code_defs_probe.out) by
-- scripts/generate-bignum-mini.py; do not edit.
module

public import Flapjack.Compiler.Backend.WordBignum.Mini

@[expose] public section

/-! The 64 mini programs that HOL's `to_deep` (`word_bignumScript.sml`) defines
as constants `NAME_code`, in dependency order. Each mentions the other
generated constants by name, exactly as HOL's definitions do; `mcIopCode` is
the program the executable bignum generator compiles. These ports do not prove
the shallow-to-deep generator correct; that is the `*_corr_thm` family. -/

namespace Flapjack.Compiler.Backend.WordBignum

{definitions}

end Flapjack.Compiler.Backend.WordBignum
'''


def render_test():
    rows = dict(line.split("=", 1) for line in INPUT.read_text().splitlines())
    source = rows["generic"]
    if source != rows["mini"]:
        raise ValueError("polymorphic and 64-bit mini-program captures differ")
    body, fragments = translate(source, fragment_limit=1000)
    definitions = "\n\n".join(
        f"private def {name} (width : Nat) : Mini (BitVec width) :=\n  {value}"
        for name, value in fragments
    )
    return f'''-- Generated from the pinned HOL mini-program capture
-- (scripts/hol-probes/bignum_mini_probe.out) by scripts/generate-bignum-mini.py;
-- do not edit.
module

public import Flapjack.Compiler.Backend.WordBignum.GeneratedMini

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! The tagged `mcIopCode`, built from the generated code constants, unfolds to
the fully expanded program that HOL's `EVAL` prints for `mc_iop_code`. -/
namespace Flapjack.Test.WordBignumMiniExpansionParity
open Flapjack.Compiler.Backend.WordBignum

{definitions}

/-- HOL's `EVAL` of `mc_iop_code`, with every generated constant expanded. -/
def mcIopCodeExpanded (width : Nat) : Mini (BitVec width) :=
  {body}

theorem mcIopCode_eq_expanded (width : Nat) [NeZero width] :
    mcIopCode width = mcIopCodeExpanded width := rfl

end Flapjack.Test.WordBignumMiniExpansionParity
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    outputs = {OUTPUT: render(), TEST_OUTPUT: render_test()}
    if args.check:
        for path, expected in outputs.items():
            if not path.exists() or path.read_text() != expected:
                raise SystemExit(f"{path} is stale; regenerate it from the HOL capture")
        print("bignum mini-program matches the captured HOL output")
    else:
        for path, expected in outputs.items():
            path.write_text(expected)


if __name__ == "__main__":
    main()
