#!/usr/bin/env python3
"""Render HOL `word_bignum$generated_bignum_stubs_eq` as a Lean literal.

HOL saves `generated_bignum_stubs_eq` as `EVAL ``generated_bignum_stubs n`` |>
SIMP_RULE std_ss [GSYM ADD_ASSOC]` (`word_bignumScript.sml:576-577`): an
explicit list of 23 `(index, arity, program)` triples over the free numeral `n`
and the word dimension `:α`. This script reads that conclusion from the pinned
capture `scripts/hol-probes/word_bignum_stubs_eq_typed_probe.out` (row
`generated_bignum_stubs_eq_untyped`; the `_typed` row of the same capture is
the inferred statement for review) and renders every program term by term:

* each wordLang/asm constructor becomes the Lean constructor of the reviewed
  carriers (`Seq` -> `.seq`, `If` -> `.ite`, `Call` -> `.call`, ...);
* a numeral word `kw` becomes the Lean numeral `k` (`BitVec width` for
  `:α word`, `BitVec 5` for the `:word5` temporaries);
* `ShiftN sh e m`, wordLang's overload for `Shift sh e (Const (n2w m))`,
  becomes `.shift sh e (.const (BitVec.ofNat width m))`;
* `dimindex (:α)` becomes `width`, `dimword (:α)` becomes `2 ^ width`, and
  `n2w m` becomes `BitVec.ofNat width m`;
* `⦕ 0 ⦖` (sptree `LS ()`) becomes `.ls ()` and `LN` becomes `.ln`.

Each program is emitted as a separate definition `stubsEqProgK width n` in
one of the `GeneratedStubsEq/Part*.lean` modules, and the list itself as the
right-hand side of the tagged theorem in `GeneratedStubsEq.lean`, whose proof
uses the hand-written `GeneratedStubsEq/Evaluation.lean`. With `--check`, the
committed modules must equal the rendering.
"""
import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_module_header import to_module  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
CAPTURE = ROOT / "scripts/hol-probes/word_bignum_stubs_eq_typed_probe.out"
OUT_DIR = ROOT / "Flapjack/Compiler/Backend/WordBignum/GeneratedStubsEq"
ROW = "generated_bignum_stubs_eq_untyped="
NAMESPACE = "Flapjack.Compiler.Backend.WordBignum.GeneratedStubsEq"
PARTS = 4
EXPECTED_STUBS = 23

# HOL constructor -> (Lean constructor, arity).
CONSTRUCTORS = {
    # wordLang$prog
    "Skip": (".skip", 0), "Seq": (".seq", 2), "Assign": (".assign", 2),
    "Set": (".set", 2), "Store": (".store", 2), "Inst": (".inst", 1),
    "If": (".ite", 5), "Call": (".call", 4), "Return": (".return", 2),
    "MustTerminate": (".mustTerminate", 1),
    # wordLang$exp
    "Const": (".const", 1), "Var": (".var", 1), "Lookup": (".lookup", 1),
    "Load": (".load", 1), "Op": (".op", 2), "Shift": (".shift", 3),
    # stackLang$store_name
    "Temp": (".temp", 1),
    # asm
    "Arith": (".arith", 1), "AddCarry": (".addCarry", 4),
    "LongMul": (".longMul", 4), "Reg": (".reg", 1), "Imm": (".imm", 1),
    "Equal": (".equal", 0), "Lower": (".lower", 0), "Less": (".less", 0),
    "Test": (".test", 0), "Add": (".add", 0), "Sub": (".sub", 0),
    "And": (".and", 0), "Xor": (".xor", 0),
    # ast$shift
    "Lsl": (".lsl", 0), "Lsr": (".lsr", 0),
    # option, sptree
    "SOME": ("some", 1), "NONE": ("none", 0), "LN": (".ln", 0),
}

TOKEN = re.compile(r"\(:α\)|[0-9]+w|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[−+=(),;\[\]⦕⦖]")


def tokenize(text):
    tokens = TOKEN.findall(text)
    if "".join(tokens) != re.sub(r"\s+", "", text):
        raise ValueError("unexpected character in the HOL capture")
    return tokens


def fully_parenthesized(text):
    """Whether `text` is one parenthesized group."""
    if not text.startswith("("):
        return False
    depth = 0
    for i, ch in enumerate(text):
        depth += ch == "("
        depth -= ch == ")"
        if depth == 0:
            return i == len(text) - 1
    return False


class Parser:
    def __init__(self, tokens):
        self.tokens = tokens
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def take(self, expected=None):
        token = self.peek()
        if token is None:
            raise ValueError("unexpected end of the HOL capture")
        if expected is not None and token != expected:
            raise ValueError(f"expected {expected!r}, found {token!r} at token {self.pos}")
        self.pos += 1
        return token

    def is_atom_start(self):
        token = self.peek()
        if token is None or token in {")", ",", ";", "]", "⦖", "+", "−", "=", "then", "else"}:
            return False
        return True

    # term := 'if' term 'then' term 'else' term | sum ('=' sum)?
    def term(self):
        if self.peek() == "if":
            self.take("if")
            cond = self.term()
            self.take("then")
            yes = self.term()
            self.take("else")
            no = self.term()
            return f"(if {cond} then {yes} else {no})"
        left = self.sum()
        if self.peek() == "=":
            self.take("=")
            return f"{left} = {self.sum()}"
        return left

    # sum := app (('+' | '−') app)*   (HOL `+`/`−` are left associative)
    def sum(self):
        result = self.app()
        while self.peek() in {"+", "−"}:
            op = "+" if self.take() == "+" else "-"
            result = f"{result} {op} {self.app()}"
        return result

    def app(self):
        token = self.peek()
        if token in CONSTRUCTORS:
            self.take()
            name, arity = CONSTRUCTORS[token]
            args = [self.atom() for _ in range(arity)]
            return f"({name} {' '.join(args)})" if args else name
        if token == "ShiftN":
            self.take()
            op, exp, amount = self.atom(), self.atom(), self.atom()
            return f"(.shift {op} {exp} (.const (BitVec.ofNat width {amount})))"
        if token == "n2w":
            self.take()
            return f"(BitVec.ofNat width {self.atom()})"
        if token in {"dimindex", "dimword"}:
            self.take()
            self.take("(:α)")
            return "width" if token == "dimindex" else "2 ^ width"
        return self.atom()

    def atom(self):
        token = self.take()
        if token == "(":
            items = [self.term()]
            while self.peek() == ",":
                self.take(",")
                items.append(self.term())
            self.take(")")
            if len(items) == 1:
                return items[0] if fully_parenthesized(items[0]) or " " not in items[0] \
                    else f"({items[0]})"
            return f"({', '.join(items)})"
        if token == "[":
            items = []
            while self.peek() != "]":
                items.append(self.term())
                if self.peek() == ";":
                    self.take(";")
                elif self.peek() != "]":
                    raise ValueError("expected a list separator")
            self.take("]")
            return f"[{', '.join(items)}]"
        if token == "⦕":
            self.take("0")
            self.take("⦖")
            return "(.ls ())"
        if re.fullmatch(r"[0-9]+w", token):
            return token[:-1]
        if re.fullmatch(r"[0-9]+", token):
            return token
        if token == "n":
            return "n"
        if token in CONSTRUCTORS or token in {"ShiftN", "n2w", "dimindex", "dimword"}:
            self.pos -= 1
            if CONSTRUCTORS.get(token, (None, 1))[1] == 0:
                self.take()
                return CONSTRUCTORS[token][0]
            raise ValueError(f"applied constructor {token!r} must be parenthesized")
        raise ValueError(f"unsupported HOL token {token!r}")


def parse_capture(path=CAPTURE):
    rows = [line for line in path.read_text().splitlines() if line.startswith(ROW)]
    if len(rows) != 1:
        raise ValueError(f"expected exactly one {ROW} row in {path}")
    parser = Parser(tokenize(rows[0][len(ROW):]))
    for token in ("generated_bignum_stubs", "n", "=", "["):
        parser.take(token)
    stubs = []
    while parser.peek() != "]":
        parser.take("(")
        index = parser.term()
        parser.take(",")
        arity = parser.term()
        parser.take(",")
        program = parser.term()
        parser.take(")")
        stubs.append((index, arity, program))
        if parser.peek() == ";":
            parser.take(";")
        elif parser.peek() != "]":
            raise ValueError("expected a stub separator")
    parser.take("]")
    if parser.peek() is not None:
        raise ValueError("trailing tokens after the HOL list")
    if len(stubs) != EXPECTED_STUBS:
        raise ValueError(f"expected {EXPECTED_STUBS} stubs, found {len(stubs)}")
    return stubs


HEADER = "-- Generated from scripts/hol-probes/word_bignum_stubs_eq_typed_probe.out by\n" \
         "-- scripts/generate-bignum-stubs-eq.py; do not edit.\n"


def part_of(k):
    return k * PARTS // EXPECTED_STUBS


def render_part(part, stubs):
    defs = []
    for k, (_, _, program) in enumerate(stubs):
        if part_of(k) != part:
            continue
        defs.append(f'''/-- Program of entry {k} of HOL `generated_bignum_stubs_eq`, rendered term by
term from the capture. -/
def stubsEqProg{k} (width : Nat) [NeZero width] (n : Nat) : WordLangProgHOL (BitVec width) :=
  {program}
''')
    body = "\n".join(defs)
    return to_module(f'''{HEADER}import Flapjack.Pancake.WordLang

/-! Part {part} of the programs in HOL `generated_bignum_stubs_eq`
(`word_bignumScript.sml:576-577`). No separate HOL declarations. -/

namespace {NAMESPACE}
open Flapjack

{body}
end {NAMESPACE}
''')


def render_theorem(stubs):
    imports = "\n".join(f"import Flapjack.Compiler.Backend.WordBignum.GeneratedStubsEq.Part{p}"
                        for p in range(PARTS))
    entries = ",\n        ".join(f"({index}, {arity}, stubsEqProg{k} width n)"
                                 for k, (index, arity, _) in enumerate(stubs))
    return to_module(f'''{HEADER}{imports}
import Flapjack.Compiler.Backend.WordBignum.GeneratedStubsEq.Evaluation

/-! HOL `generated_bignum_stubs_eq` (`word_bignumScript.sml:576-577`). -/

namespace Flapjack.Compiler.Backend.WordBignum
open {NAMESPACE}

/-- HOL `generated_bignum_stubs_eq`, the evaluation of `generated_bignum_stubs n`
at an arbitrary word dimension, as an explicit list of `(index, arity, program)`
triples. The list and each program are rendered term by term from the HOL
capture by `scripts/generate-bignum-stubs-eq.py`; the programs are named
`stubsEqProgK` only to split the literal into modules. HOL's word dimension
`dimindex (:α)` is `width`, `dimword (:α)` is `2 ^ width`, `n2w m` is
`BitVec.ofNat width m`, and the `ShiftN sh e m` overload is
`.shift sh e (.const (BitVec.ofNat width m))`.

The proof evaluates `generatedBignumStubs` in the kernel through the
constant-independent compiler of `GeneratedStubsEq.Evaluation`. -/
@[hol "cakeml/compiler/backend/word_bignumScript.sml" "generated_bignum_stubs_eq"
  (words_as_type_indexed_bitvec)]
theorem generatedBignumStubs_eq {{width : Nat}} [NeZero width] (n : Nat) :
    (generatedBignumStubs width n : List (Nat × Nat × WordLangProgHOL (BitVec width))) =
      [{entries}] := by
  rw [generatedBignumStubs_eq_K]
  kernel_rfl

end Flapjack.Compiler.Backend.WordBignum
''')


def expected_files():
    stubs = parse_capture()
    files = {OUT_DIR / f"Part{p}.lean": render_part(p, stubs) for p in range(PARTS)}
    files[OUT_DIR.parent / "GeneratedStubsEq.lean"] = render_theorem(stubs)
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true",
                        help="fail if the committed modules differ from the rendering")
    args = parser.parse_args()
    files = expected_files()
    if args.check:
        stale = [str(p.relative_to(ROOT)) for p, text in files.items()
                 if not p.exists() or p.read_text() != text]
        if stale:
            raise SystemExit("stale generated_bignum_stubs_eq modules: " + ", ".join(stale))
        print("generated_bignum_stubs_eq modules match the HOL capture")
        return
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    for path, text in files.items():
        path.write_text(text)


if __name__ == "__main__":
    main()
