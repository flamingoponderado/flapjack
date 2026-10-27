#!/usr/bin/env python3
"""Render the pinned HOL bignum output as a 64-bit executable snapshot."""
import argparse
import importlib.util
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
INPUT = ROOT / "scripts/hol-probes/bignum_word_probe.out"
OUTPUT = ROOT / "Flapjack/Compiler/Backend/WordBignum/Generated64.lean"
spec = importlib.util.spec_from_file_location("word_fixture", ROOT / "scripts/generate-cake-word-oracles.py")
fixture = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fixture)


def render():
    entries = fixture.parse_entries(INPUT)
    if len(entries) != 23:
        raise ValueError("expected exactly 23 original bignum stubs")
    definitions = []
    for index, (pattern, sets, words) in enumerate(entries):
        if not pattern.endswith(", 0)"):
            raise ValueError("unexpected diagnostic label")
        term = pattern[:-4] + ")"
        for name, keys in sets:
            term = re.sub(rf"\b{name}\b", f"(Flapjack.sptListInsert [{', '.join(keys)}] .ln)", term)
        for name in words:
            term = re.sub(rf"\b{name}\b", "(-1)", term)
        definitions.append(f"private def stub{index} : Nat × Nat × WordLangProgHOL (BitVec 64) :=\n  {term}")
    names = ", ".join(f"stub{index}" for index in range(len(entries)))
    return f'''-- Generated from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang

namespace Flapjack.Compiler.Backend.WordBignum

{chr(10).join(definitions)}

/-- Flapjack's 64-bit snapshot of the original generated bignum stubs at the
fixed CakeML bignum location. This is an executable specialization, not a port
of the generic HOL generator or a cross-language correctness theorem. -/
def generatedStubs64 : List (Nat × Nat × WordLangProgHOL (BitVec 64)) :=
  [{names}]

end Flapjack.Compiler.Backend.WordBignum
'''


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = render()
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text() != expected:
            raise SystemExit(f"{OUTPUT} is stale; regenerate it from the HOL capture")
        print("64-bit bignum snapshot matches the captured HOL output")
    else:
        OUTPUT.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_text(expected)


if __name__ == "__main__":
    main()
