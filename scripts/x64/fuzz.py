#!/usr/bin/env python3
"""Differential fuzzer for the x86-64 Pancake backend.

Generates random Pancake programs, compiles them with the original CakeML
compiler (`cake --pancake --target=x64`) and with `flapjack-compile
--target=x64`, and compares the complete assembly output.  Exits nonzero on
the first mismatch and writes both outputs for inspection.
"""
import argparse
import random
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ORACLE = Path("/var/tmp/flapjack-cakeml-oracle/developers/bin/cake")
FLAPJACK = ROOT / ".lake/build/bin/flapjack-compile"

CONSTS = [0, 1, 2, 3, 7, 8, 16, 31, 63, 64, 127, 128, 255, 256, 4095, 4096,
          65535, 65536, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0x7FFFFFFFFFFFFFFF,
          0xFFFFFFFFFFFFFFFF, 12345, 305419896, 71777214294589695]


def const(rng: random.Random) -> str:
    value = rng.choice(CONSTS)
    if rng.random() < 0.15:
        return f"(0 - {value})"
    return str(value)


def expr(rng: random.Random, vars: list[str], depth: int = 2) -> str:
    choices = ["const"] if depth == 0 or not vars else ["const", "var", "bin", "shift", "cmp"]
    kind = rng.choice(choices)
    if kind == "const":
        return const(rng)
    if kind == "var":
        return rng.choice(vars)
    if kind == "bin":
        op = rng.choice(["+", "-", "&", "|", "^", "*"])
        return f"({expr(rng, vars, depth - 1)} {op} {expr(rng, vars, depth - 1)})"
    if kind == "shift":
        op = rng.choice(["<<", ">>>", ">>", "#>>"])
        return f"({expr(rng, vars, depth - 1)} {op} {const(rng)})"
    left = expr(rng, vars, depth - 1)
    right = expr(rng, vars, depth - 1)
    op = rng.choice(["==", "!=", "<", ">", "<=", ">="])
    return f"({left} {op} {right})"


def gen_program(rng: random.Random) -> str:
    lines: list[str] = []
    nglobals = rng.randrange(0, 3)
    for i in range(nglobals):
        lines.append(f"var 1 g{i} = {const(rng)};")
    nfuns = rng.randrange(1, 3)
    arities: list[int] = []
    for f in range(nfuns):
        params = [f"p{j}" for j in range(rng.randrange(0, 4))]
        arities.append(len(params))
        lines.append(f"fun 1 f{f}({', '.join('1 ' + p for p in params)}) {{")
        vars_ = list(params)
        for v in range(rng.randrange(1, 6)):
            name = f"v{v}"
            lines.append(f"  var 1 {name} = {expr(rng, vars_)};")
            vars_.append(name)
        for _ in range(rng.randrange(0, 2)):
            cond = f"({expr(rng, vars_)} {rng.choice(['==','!=','<','>','<=','>='])} {expr(rng, vars_)})"
            lines.append(f"  if {cond} {{ {rng.choice(vars_)} = {expr(rng, vars_)}; }}")
            lines.append(f"  else {{ {rng.choice(vars_)} = {expr(rng, vars_)}; }}")
        if rng.random() < 0.3:
            lines.append(f"  var 1 i = 0;")
            lines.append(f"  while (i < {rng.randrange(1, 20)}) {{")
            lines.append(f"    i = i + 1;")
            lines.append(f"    {rng.choice(vars_)} = {expr(rng, vars_ + ['i'])};")
            lines.append("  }")
        if rng.random() < 0.3:
            addr = rng.choice(vars_)
            lines.append(f"  st {addr}, {expr(rng, vars_)};")
            lines.append(f"  st8 {addr} + 1, {expr(rng, vars_)};")
            lines.append(f"  var 1 m = lds 1 {addr};")
            lines.append(f"  var 1 b = ld8 {addr} + 1;")
            vars_ += ["m", "b"]
        ret = expr(rng, vars_)
        if rng.random() < 0.3:
            ret = f"{rng.choice(vars_)}"
        lines.append(f"  return {ret};")
        lines.append("}")
    lines.append("fun 1 main() {")
    if nfuns:
        args = ", ".join(expr(rng, []) for _ in range(arities[0]))
        lines.append(f"  var 1 r = f0({args});")
        lines.append("  return r;")
    else:
        lines.append(f"  return {expr(rng, [])};")
    lines.append("}")
    return "\n".join(lines) + "\n"


def run(cmd: list[str], source: str) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, input=source, capture_output=True, text=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--count", type=int, default=100)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--keep-going", action="store_true")
    args = parser.parse_args()
    rng = random.Random(args.seed)
    failures = 0
    skipped = 0
    for i in range(args.count):
        source = gen_program(rng)
        oracle = run([str(ORACLE), "--pancake", "--target=x64"], source)
        if oracle.returncode != 0:
            skipped += 1
            continue
        flapjack = run([str(FLAPJACK), "--target=x64"], source)
        if flapjack.returncode != 0:
            print(f"FAIL {i}: flapjack exited {flapjack.returncode}: {flapjack.stderr.strip()}",
                  file=sys.stderr)
            print(source, file=sys.stderr)
            failures += 1
        elif flapjack.stdout != oracle.stdout:
            print(f"FAIL {i}: output differs", file=sys.stderr)
            print(source, file=sys.stderr)
            failures += 1
        else:
            continue
        if failures >= 5 and not args.keep_going:
            break
    print(f"{args.count} programs, {skipped} rejected by cake, {failures} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
