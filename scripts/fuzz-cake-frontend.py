#!/usr/bin/env python3
"""Compare generated CakeML frontend inputs with the pinned compiler."""
import argparse
import hashlib
import importlib.util
import random
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("cake_cli_parity", ROOT / "scripts/check-cake-cli-parity.py")
parity = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parity)

TERMS = ["1", "True", "\"x\"", "0w42", "(1,True)", "[1,2]", "fn x => x", "(fn x => x x)",
         "A", "Foo.x", "()", "#\"a\"", "1.5", "raise Fail \"x\"", "[True,1]", "fn x => x+1"]
PATTERNS = ["x", "_", "(x,y)", "A x", "[x,y]", "1", "True", "(x,x)", "x::xs"]
LEAVES = ["0", "1", "42", "~3", "99999999999999999999999", "x"]


def type_program(rng):
    a, b = rng.choices(TERMS, k=2)
    pattern = rng.choice(PATTERNS)
    return rng.choice([
        f"val {pattern} = {a};",
        f"val x = if {a} then {b} else {a};",
        f"val x = {a} + {b};",
        f"fun f {pattern} = {a}; val y = f {b};",
        f"val x = case {a} of {pattern} => {b} | _ => {a};",
        f"datatype t = A int | B; val x = {a};",
        f"local val x = {a} in val y = {b} end;",
    ])


def integer_expression(rng, depth):
    if depth == 0:
        return rng.choice(LEAVES)
    choice = rng.randrange(5)
    if choice == 0:
        return (f"({integer_expression(rng, depth - 1)} "
                f"{rng.choice(['+', '-', '*', 'div', 'mod'])} {integer_expression(rng, depth - 1)})")
    if choice == 1:
        return (f"(if {integer_expression(rng, depth - 1)} {rng.choice(['=', '<', '<=', '>'])} "
                f"{integer_expression(rng, depth - 1)} then {integer_expression(rng, depth - 1)} "
                f"else {integer_expression(rng, depth - 1)})")
    if choice == 2:
        return f"((fn y => y + 1) {integer_expression(rng, depth - 1)})"
    if choice == 3:
        return (f"(case [{integer_expression(rng, depth - 1)},{integer_expression(rng, depth - 1)}] "
                "of [] => 0 | h::t => h)")
    return rng.choice(LEAVES)


def run(executable, options, source, timeout):
    return subprocess.run([str(executable), "--target=riscv", *options], input=source.encode("ascii"),
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)


def summary(result):
    return {"exit": result.returncode, "stdout_bytes": len(result.stdout),
            "stdout_sha256": hashlib.sha256(result.stdout).hexdigest(),
            "stderr_bytes": len(result.stderr), "stderr": repr(result.stderr[:500])}


def compare(reference, cake, options, source, timeout, require_success, output_channel="stdout"):
    expected = run(reference, options, source, timeout)
    actual = run(cake, options, source, timeout)
    other_channel = "stderr" if output_channel == "stdout" else "stdout"
    if require_success and (expected.returncode != 0 or not getattr(expected, output_channel) or
                            getattr(expected, other_channel)):
        raise SystemExit(f"generated compilation case rejected by pinned CakeML: {source}\n{summary(expected)}")
    if (expected.returncode, expected.stdout, expected.stderr) != (actual.returncode, actual.stdout, actual.stderr):
        raise SystemExit(f"output mismatch for {options}:\n{source}\n"
                         f"reference: {summary(expected)}\nflapjack: {summary(actual)}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, required=True, help="pinned CakeML executable")
    parser.add_argument("--cake", type=Path, default=ROOT / ".lake/build/bin/cake")
    parser.add_argument("--type-cases", type=int, default=200)
    parser.add_argument("--compile-cases", type=int, default=20)
    parser.add_argument("--sexp-cases", type=int, default=100,
                        help="generated programs to compare in S-expression output mode")
    parser.add_argument("--byte-cases", type=int, default=256,
                        help="decimal string escapes to compare, from byte 0 (maximum 256)")
    parser.add_argument("--type-seed", type=int, default=42)
    parser.add_argument("--compile-seed", type=int, default=27)
    parser.add_argument("--timeout", type=int, default=90)
    args = parser.parse_args()
    if (args.type_cases < 0 or args.compile_cases < 0 or args.sexp_cases < 0 or
            not 0 <= args.byte_cases <= 256 or args.timeout <= 0):
        parser.error("case counts must be nonnegative, byte-cases at most 256, and timeout positive")
    parity.check_pinned_reference(args.reference)
    types_rng = random.Random(args.type_seed)
    for _ in range(args.type_cases):
        compare(args.reference, args.cake, ["--types", "--exclude_prelude=true"],
                type_program(types_rng), args.timeout, False)
    print(f"{args.type_cases} structured parser and type-checking cases match pinned CakeML", flush=True)
    sexp_rng = random.Random(args.type_seed)
    for _ in range(args.sexp_cases):
        compare(args.reference, args.cake, ["--print_sexp", "--exclude_prelude=true"],
                type_program(sexp_rng), args.timeout, False)
    print(f"{args.sexp_cases} generated S-expression output cases match pinned CakeML", flush=True)
    for byte in range(args.byte_cases):
        for literal in (f'"\\{byte:03d}"', f'#"\\{byte:03d}"'):
            compare(args.reference, args.cake, ["--print_sexp", "--exclude_prelude=true"],
                    f"val x = {literal};", args.timeout, True, output_channel="stderr")
    print(f"{args.byte_cases} decimal string and character escapes match pinned CakeML", flush=True)
    compile_rng = random.Random(args.compile_seed)
    for _ in range(args.compile_cases):
        depth = compile_rng.randint(1, 3)
        source = f"fun f x = {integer_expression(compile_rng, depth)}; val _ = print_int (f 7);"
        compare(args.reference, args.cake, [], source, args.timeout, True)
    print(f"{args.compile_cases} generated programs match complete pinned RISC-V output", flush=True)


if __name__ == "__main__":
    main()
