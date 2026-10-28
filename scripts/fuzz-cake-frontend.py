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
STRUCTURED_ATOMS = ["0", "~1", "3", "18446744073709551616", "0w0", "0w18446744073709551615",
                    "True", "False", "()", "[]", "[1,2]", "(1,True)", '"abc"', '#"x"', "x", "A",
                    "(fn x => x)", "(raise E 1)", "(case x of A y => y | _ => 0)"]
STRUCTURED_PATTERNS = ["x", "_", "0", "True", "A", "A x", "(x,y)", "(x,x)", "[]", "x::xs",
                       "[x,y]", '"abc"', "(A x,y)"]
STRUCTURED_TYPES = ["int", "bool", "int list", "int * bool", "'a", "'a list", "missing", "int -> int",
                    "(int * int)"]
LEX_PREFIXES = ["", "(* x *)", "(* a (* b *) c *)", '(* " *)', "(*", "   \n", "(* a *) (* b *)"]
LEX_SUFFIXES = ["", ";", ";;", "\n(* unterminated", " (* trailing *)", "\n"]
LEX_ATOMS = ['""', '"a\\n\\t\\r"', '"\\000\\127\\255"', '"\\001x"', '"\\256"', '"\\999"',
             '"\\x41"', '"\\^A"', '"\\ "', '"\\\\"', '"abc', '"a\nb"', '#"a"', '#"\\255"',
             '#"ab"', "0", "00", "123456789012345678901234567890", "~0", "~~1", "0w0",
             "0w99999999999999999999999999", "0xFF", "0wxFF", "0.0", "1.2e3", "1e2", "~1.5",
             "1.", "1..2", "1_000", "0b10", "x", "x'", "_", "_x", "Ab", "a.b", "a..b", "M.x",
             "a_b", "x0", "op", "andalso", "not", "type", "x\x7f"]
DECL_TYPES = ["int", "bool", "string", "'a", "'a list", "int * int", "t", "u", "int -> int", "missing"]
DECL_CONSTRUCTORS = ["A", "B", "C", "D", "A int", "B bool", "C (int * int)", "D 'a", "E t"]
DECL_VALUES = ["A", "B", "C 1", "(A, B)", "fn x => x", "1", "True", "[A,B]", "(raise E)"]
BACKEND_OPTIONS = [
    ["--multi=true", "--multi=false"], ["--known=true", "--known=false"],
    ["--call=true", "--call=false"], ["--tailrec=true", "--tailrec=false"],
    ["--tmc=true", "--tmc=false"], ["--split=true", "--split=false"],
    ["--reg_alg=0", "--reg_alg=1", "--reg_alg=2", "--reg_alg=3"],
    ["--gc=none", "--gc=simple", "--gc=gen", "--gc=gen5000"],
    ["--inline_size=0", "--inline_size=3", "--inline_size=20"],
    ["--max_app=0", "--max_app=2", "--max_app=8"], ["--tag_bits=2", "--tag_bits=3"],
    ["--hash_size=0", "--hash_size=4"],
]


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


def structured_expression(rng, depth):
    if depth == 0:
        return rng.choice(STRUCTURED_ATOMS)
    choice = rng.randrange(7)
    if choice == 0:
        return (f"({structured_expression(rng, depth - 1)} "
                f"{rng.choice(['+', '-', '*', 'div', 'mod', '=', '<', 'andalso', 'orelse', '::'])} "
                f"{structured_expression(rng, depth - 1)})")
    if choice == 1:
        return (f"(if {structured_expression(rng, depth - 1)} then {structured_expression(rng, depth - 1)} "
                f"else {structured_expression(rng, depth - 1)})")
    if choice == 2:
        return (f"(let val {rng.choice(STRUCTURED_PATTERNS)} = {structured_expression(rng, depth - 1)} "
                f"in {structured_expression(rng, depth - 1)} end)")
    if choice == 3:
        return (f"(case {structured_expression(rng, depth - 1)} of {rng.choice(STRUCTURED_PATTERNS)} => "
                f"{structured_expression(rng, depth - 1)} | _ => {structured_expression(rng, depth - 1)})")
    if choice == 4:
        return f"(fn {rng.choice(STRUCTURED_PATTERNS)} => {structured_expression(rng, depth - 1)})"
    if choice == 5:
        return f"({structured_expression(rng, depth - 1)} : {rng.choice(STRUCTURED_TYPES)})"
    return structured_expression(rng, 0)


def structured_program(rng):
    choice = rng.randrange(6)
    if choice == 0:
        return f"val {rng.choice(STRUCTURED_PATTERNS)} = {structured_expression(rng, 2)};"
    if choice == 1:
        return f"fun f {rng.choice(STRUCTURED_PATTERNS)} = {structured_expression(rng, 2)};"
    if choice == 2:
        return f"exception E int; datatype t = A int | B; val x = {structured_expression(rng, 2)};"
    if choice == 3:
        return f"local val x = {structured_expression(rng, 1)} in val y = {structured_expression(rng, 2)} end;"
    if choice == 4:
        return f"structure M = struct val x = {structured_expression(rng, 1)}; end; val y = {structured_expression(rng, 1)};"
    return f"datatype t = A {rng.choice(STRUCTURED_TYPES)} | B; val x = {structured_expression(rng, 1)};"


def lexical_program(rng):
    return (rng.choice(LEX_PREFIXES) + rng.choice(["val x = ", "val y = ", "fun f x = ", "type t = "]) +
            rng.choice(LEX_ATOMS) + rng.choice(LEX_SUFFIXES))


def declaration_program(rng):
    constructors = " | ".join(rng.choices(DECL_CONSTRUCTORS, k=rng.randrange(1, 5)))
    return rng.choice([
        f"datatype t = {constructors}; val x = {rng.choice(DECL_VALUES)};",
        f"datatype 'a t = {constructors}; val x = {rng.choice(DECL_VALUES)};",
        f"type t = {rng.choice(DECL_TYPES)}; type u = {rng.choice(DECL_TYPES)}; "
        f"val x : t = {rng.choice(DECL_VALUES)};",
        f"exception E {rng.choice(DECL_TYPES)}; exception F {rng.choice(DECL_TYPES)}; "
        f"val x = {rng.choice(DECL_VALUES)};",
        f"structure M = struct datatype t = {constructors}; val x = {rng.choice(DECL_VALUES)}; "
        "end; val z = M.x;",
        f"local datatype t = {constructors} in val x = {rng.choice(DECL_VALUES)} end;",
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


def rich_program(rng):
    """Generate well-typed programs that exercise frontend and backend passes."""
    a, b, c = (rng.randrange(1, 20) for _ in range(3))
    return rng.choice([
        f'datatype tree = L int | N (tree * tree); '
        f'fun sum t = case t of L n => n | N (x,y) => sum x + sum y; '
        f'val _ = print_int (sum (N (L {a}, L {b})));',
        f'fun make x = let val y = x + {a} in fn z => y * z end; '
        f'val _ = print_int (make {b} {c});',
        f'exception E int; fun f x = ((if x = {a} then raise E (x + {b}) else x) '
        f'handle E y => y * {c}); val _ = print_int (f {a});',
        f'fun f x = let val r = Ref x; val _ = r := !r + {a} '
        f'in !r * {b} end; val _ = print_int (f {c});',
        f'structure M = struct datatype t = A | B int; '
        f'fun f x = case x of A => {a} | B n => n + {b}; end; '
        f'val _ = print_int (M.f (M.B {c}));',
        f'fun f xs = case xs of [] => {a} | x::rest => x + f rest; '
        f'val _ = print_int (f [{a},{b},{c}]);',
        f'fun f x y = if x < y andalso y <> {a} then x + y else x * y; '
        f'val _ = print_int (f {b} {c});',
        f'val a = Array.array 3 {a}; val _ = Array.update a 1 {b}; '
        f'val _ = print_int (Array.sub a 0 + Array.sub a 1 + Array.sub a 2);',
        f'val a = Word8Array.array 3 (Word8.fromInt {a}); '
        f'val _ = Word8Array.update a 2 (Word8.fromInt {b}); '
        f'val _ = print_int (Word8.toInt (Word8Array.sub a 0) + Word8.toInt (Word8Array.sub a 2));',
        f'fun sum a i = if i = 3 then 0 else Array.sub a i + sum a (i + 1); '
        f'val a = Array.array 3 {a}; val _ = Array.update a 1 {b}; '
        f'val _ = print_int (sum a 0);',
    ])


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
    parser.add_argument("--rich-cases", type=int, default=20,
                        help="well-typed programs exercising diverse compiler passes")
    parser.add_argument("--declaration-cases", type=int, default=100,
                        help="generated datatype, exception, type and namespace cases")
    parser.add_argument("--config-cases", type=int, default=10,
                        help="successful compilations with generated backend options")
    parser.add_argument("--sexp-cases", type=int, default=100,
                        help="generated programs to compare in S-expression output mode")
    parser.add_argument("--byte-cases", type=int, default=256,
                        help="decimal string escapes to compare, from byte 0 (maximum 256)")
    parser.add_argument("--structured-cases", type=int, default=100,
                        help="nested expression, pattern, type and declaration cases")
    parser.add_argument("--lex-cases", type=int, default=100,
                        help="comment, literal, identifier and malformed-token cases")
    parser.add_argument("--type-seed", type=int, default=42)
    parser.add_argument("--compile-seed", type=int, default=27)
    parser.add_argument("--edge-seed", type=int, default=83219)
    parser.add_argument("--timeout", type=int, default=90)
    args = parser.parse_args()
    if (args.type_cases < 0 or args.compile_cases < 0 or args.rich_cases < 0 or args.sexp_cases < 0 or
            args.declaration_cases < 0 or args.config_cases < 0 or
            args.structured_cases < 0 or args.lex_cases < 0 or
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
    edge_rng = random.Random(args.edge_seed)
    for _ in range(args.structured_cases):
        source = structured_program(edge_rng)
        mode = edge_rng.choice(["--types", "--print_sexp"])
        compare(args.reference, args.cake, [mode, "--exclude_prelude=true"], source, args.timeout, False)
    print(f"{args.structured_cases} nested frontend cases match pinned CakeML", flush=True)
    for _ in range(args.lex_cases):
        source = lexical_program(edge_rng)
        mode = edge_rng.choice(["--types", "--print_sexp"])
        compare(args.reference, args.cake, [mode, "--exclude_prelude=true"], source, args.timeout, False)
    print(f"{args.lex_cases} lexical edge cases match pinned CakeML", flush=True)
    decl_rng = random.Random(args.edge_seed ^ 5431)
    for _ in range(args.declaration_cases):
        source = declaration_program(decl_rng)
        mode = decl_rng.choice(["--types", "--print_sexp"])
        compare(args.reference, args.cake, [mode, "--exclude_prelude=true"], source, args.timeout, False)
    print(f"{args.declaration_cases} generated declaration cases match pinned CakeML", flush=True)
    compile_rng = random.Random(args.compile_seed)
    for _ in range(args.compile_cases):
        depth = compile_rng.randint(1, 3)
        source = f"fun f x = {integer_expression(compile_rng, depth)}; val _ = print_int (f 7);"
        compare(args.reference, args.cake, [], source, args.timeout, True)
    print(f"{args.compile_cases} generated programs match complete pinned RISC-V output", flush=True)
    for _ in range(args.rich_cases):
        compare(args.reference, args.cake, [], rich_program(compile_rng), args.timeout, True)
    print(f"{args.rich_cases} diverse programs match complete pinned RISC-V output", flush=True)
    config_rng = random.Random(args.compile_seed ^ 7431)
    source = "fun f xs = case xs of [] => [] | x::rest => x::f rest; val a = f [1,2,3];"
    for _ in range(args.config_cases):
        options = [config_rng.choice(group) for group in config_rng.sample(BACKEND_OPTIONS, k=4)]
        compare(args.reference, args.cake, ["--exclude_prelude=true", *options], source, args.timeout, True)
    print(f"{args.config_cases} backend option combinations match complete pinned RISC-V output", flush=True)


if __name__ == "__main__":
    main()
