#!/usr/bin/env python3
"""Compare generated programs against the pinned CakeML compiler.

This is a bounded source-to-assembly differential check, not a correctness
proof. Both complete outputs, standard errors, and exit statuses must match.
Generated integer programs must also be accepted. Mutation and corpus modes
compare accepted and rejected inputs alike, including their diagnostics. The
checker needs a locally built pinned original compiler; see
docs/PARITY-TESTING.md.
"""
import argparse
import hashlib
import random
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CAKEML_REV = '857f0d98da8f8a3580f34423338e697809308ede'
HOL_REV = 'a390cbabd3a4521bab4ee20281e3e42933a8a3ae'

# Small source programs covering forms outside the integer-expression fuzzer.
# Run without the prelude so that unbound names also exercise diagnostics.
SOURCE_CORPUS = [
    ('val x = #"a";', 0),
    ('val x = 0w123;', 0),
    ('val x = [1,2,3];', 0),
    ('datatype t = X int | Y;', 0),
    ('exception E int;', 0),
    ('fun f x = case x of [] => 0 | h::t => h;', 0),
    ('fun f x = let fun g y = x in g 4 end;', 0),
    ('val (x,y) = (1,2);', 0),
    ('val x = (1 handle _ => 2);', 0),
    ('val x = "\\000\\255";', 0),
    ('structure S = struct val x = 3 end;', 0),
    ('local val x = 3 in val y = x end;', 0),
    ('fun f (x,y) = x;', 0),
    ('val x = Word8.fromInt 22;', 1),
    ('val x = (1, 2, "hello");', 0),
    ('val x = 999999999999999999999999999999999;', 0),
    ('val x = ~999999999999999999999999999999999;', 0),
    ('val x = if true then 1 else 2;', 1),
    ('val x = ref 1;', 1),
    ('fun f x = f x;', 0),
    ('val x = 1 div 0;', 1),
    ('val a = Array.array (2, 1);', 1),
]

# These programs also exercise the basis and full backend output. They must
# compile successfully with the standard prelude enabled.
BASIS_CORPUS = [
    'val _ = print "hello\\n";',
    'fun fib n = if n < 2 then n else fib (n-1) + fib (n-2); val _ = print_int (fib 8);',
    'datatype tree = Leaf int | Node tree tree; fun sum t = case t of Leaf n => n | Node a b => sum a + sum b; val _ = print_int (sum (Node (Leaf 1) (Leaf 2)));',
    'val _ = print_int (Word8.toInt (Word8.fromInt 300));',
    'exception E int; val x = (raise E 7) handle E n => n; val _ = print_int x;',
    'fun f x = let val y = x + 3 in fn z => y*z end; val _ = print_int (f 5 4);',
    'val x = "héllo"; val _ = print x;',
    'val _ = print (String.implode [#"a", #"b"]);',
    'fun fact n acc = if n = 0 then acc else fact (n-1) (n*acc); val _ = print_int (fact 7 1);',
]


def expression(rng, depth):
    if depth == 0:
        return rng.choice(['0', '1', '7', '~3', 'x'])
    left, right = expression(rng, depth - 1), expression(rng, depth - 1)
    return rng.choice([
        f'({left} + {right})',
        f'({left} * {right})',
        f'(if {left} < {right} then {right} else {left})',
        f'(let val y = {left} in y + {right} end)',
        f'((fn z => z + {right}) {left})',
    ])


def mutated_source(rng):
    """Make one reproducible insertion, deletion, or replacement in source."""
    source = rng.choice([
        'val x = 1;', 'fun f x = x + 2;', 'datatype t = A | B int;',
        'val x = (fn y => y) 3;', 'structure A = struct val x = 1; end;',
    ])
    position = rng.randrange(len(source) + 1)
    operation = rng.randrange(3)
    alphabet = ' abcdefXYZ01234()[];:=+-*<>"\'\n'
    if operation == 0:
        return source[:position] + rng.choice(alphabet) + source[position:]
    if position == len(source):
        return source
    if operation == 1:
        return source[:position] + source[position + 1:]
    return source[:position] + rng.choice(alphabet) + source[position + 1:]


def deep_mutated_source(rng):
    """Mutate nested declarations and expressions, preserving reproducibility."""
    source = rng.choice([
        'datatype tree = Leaf int | Node tree tree;',
        'fun append xs ys = case xs of [] => ys | x::tail => x::append tail ys;',
        'val x = let val a = (1,2) in case a of (x,y) => x end;',
        'structure S = struct datatype t = A | B int; val x = B 3 end;',
        'fun f x = (fn y => fn z => x) 4 5;',
        'exception Error int; fun f x = (raise Error x) handle Error y => y;',
        'val x = "hello\\n\\tworld";',
        '(* comment (* nested *) tail *) val x = [1,2,3];',
    ])
    alphabet = ' abcdefXYZ01234()[];:=+-*<>"\'\n!@#$%^&|,.\\'
    for _ in range(rng.randrange(1, 4)):
        position = rng.randrange(len(source) + 1)
        operation = rng.randrange(3)
        char = rng.choice(alphabet)
        source = source[:position] + (char if operation != 1 else '') + source[position + (operation != 0):]
    return source


def run(binary, source, timeout, exclude_prelude=False):
    flags = ['--exclude_prelude=true'] if exclude_prelude else []
    return subprocess.run([str(binary), '--target=riscv', *flags], input=source.encode('utf-8'),
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reference', type=Path, required=True, help='pinned original compiler')
    parser.add_argument('--cake', type=Path, default=ROOT / '.lake/build/bin/cake')
    parser.add_argument('--seed', type=int, default=88411)
    parser.add_argument('--count', type=int, default=30)
    parser.add_argument('--timeout', type=float, default=120)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--mutations', action='store_true',
                        help='compare mutated source and diagnostics with the prelude excluded')
    modes.add_argument('--deep-mutations', action='store_true',
                       help='mutate nested declarations and expressions with the prelude excluded')
    modes.add_argument('--corpus', action='store_true',
                       help='compare fixed language-feature and standard-prelude programs')
    args = parser.parse_args()
    if args.count < 0 or args.timeout <= 0:
        parser.error('count must be nonnegative and timeout must be positive')
    version = subprocess.check_output([str(args.reference), '--version'], text=True, timeout=args.timeout)
    if f'CakeML: {CAKEML_REV}' not in version or f'HOL4:   {HOL_REV}' not in version:
        raise SystemExit('reference compiler does not report the pinned CakeML and HOL revisions')
    rng = random.Random(args.seed)
    corpus = [(source, status, True) for source, status in SOURCE_CORPUS]
    corpus += [(source, 0, False) for source in BASIS_CORPUS]
    count = len(corpus) if args.corpus else args.count
    for index in range(count):
        source = (corpus[index][0] if args.corpus else deep_mutated_source(rng) if args.deep_mutations else
                  mutated_source(rng) if args.mutations else
                  'fun f x = ' + expression(rng, rng.randrange(1, 4)) + '; val _ = print_int (f 2);')
        exclude_prelude = corpus[index][2] if args.corpus else args.mutations or args.deep_mutations
        try:
            original = run(args.reference, source, args.timeout, exclude_prelude)
            candidate = run(args.cake, source, args.timeout, exclude_prelude)
        except subprocess.TimeoutExpired as error:
            raise SystemExit(f'case {index}, seed {args.seed}: compiler timed out: {error}\n{source}')
        expected = (original.returncode, original.stdout, original.stderr)
        actual = (candidate.returncode, candidate.stdout, candidate.stderr)
        if ((args.corpus and original.returncode != corpus[index][1]) or
                (not (args.mutations or args.deep_mutations or args.corpus) and original.returncode != 0) or
                actual != expected):
            def describe(result):
                return (f'exit={result.returncode} stdout_sha256={hashlib.sha256(result.stdout).hexdigest()} '
                        f'stderr={result.stderr!r}')
            raise SystemExit(f'case {index}, seed {args.seed}: output mismatch or rejection\n{source!r}\n'
                             f'original: {describe(original)}\ncandidate: {describe(candidate)}')
        print(f'case {index}: exact output matches', flush=True)
    print(f'{count} cases matched' + ('' if args.corpus else f' (seed {args.seed})'))


if __name__ == '__main__':
    main()
