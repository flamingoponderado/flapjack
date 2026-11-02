#!/usr/bin/env python3
"""Compare generated programs against the pinned CakeML compiler.

This is a bounded source-to-assembly differential check, not a correctness
proof. Both complete outputs, standard errors, and exit statuses must match.
Generated programs must also be accepted. Mutation and corpus modes
compare accepted and rejected inputs alike, including their diagnostics. The
checker needs a locally built pinned original compiler; see
docs/PARITY-TESTING.md.
"""
import argparse
import hashlib
import random
import re
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
    ('val a = 2305843009213693951; val b = 2305843009213693952; '
     'val c = ~2305843009213693952; val d = ~2305843009213693953; '
     'val e = 18446744073709551616; val f = ~18446744073709551616;', 0),
    ('val x = if true then 1 else 2;', 1),
    ('val x = ref 1;', 1),
    ('fun f x = f x;', 0),
    ('val x = 1 div 0;', 1),
    ('val a = Array.array (2, 1);', 1),
    ('val x : int = 3;', 0),
    ('val id = fn x => x; val y = id 3;', 0),
    ("datatype 'a option = NONE | SOME 'a; val x = SOME 3;", 0),
    ('datatype tree = Leaf int | Node tree tree; val x = Node (Leaf 3) (Leaf 4);', 0),
    ('datatype tags = A0 int | A1 int | A2 int | A3 int | A4 int | A5 int | A6 int | A7 int | '
     'A8 int | A9 int | A10 int | A11 int | A12 int | A13 int | A14 int | A15 int | A16 int | A17 int; '
     'val x = A17 7; val y = (1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17);', 0),
    ('fun f x y = x; val x = f 3 4;', 0),
    ('structure S = struct val x = 1 end; val y = S.x;', 0),
    ('exception E; val x = (raise E) handle E => 2;', 0),
    ('fun f x = (case x of [] => [] | x::xs => xs);', 0),
    ('val (a,b,c,d) = (1,2,3,4);', 0),
    ('val x = (fn x => x) ((fn y => y) 10);', 0),
    ('val f = fn x => fn y => fn z => (x,y,z); val x = f 1 2 3;', 0),
    ('val x = ((fn x => x) : int -> int) 1;', 0),
    ('val x = #"\\n";', 0),
    ('val x = "\\^A\\^_";', 1),
    ('val x = 0xff; val y = 0wxFF;', 0),
    ('fun f x = case x of SOME (x,y) => x | NONE => 0;', 1),
    ('fun id x = x; val x = (id 1,id "a");', 0),
    ('datatype t = A | B int; val B x = B 2;', 0),
    ('fun f x = let val z = x in let val x = 1 in z end end;', 0),
    ('fun f (x as SOME y) = y | f NONE = 0;', 1),
    ('fun f x = case x of (a,b) => (b,a);', 0),
    ('val x = fn (a,b) => fn (c,d) => (a,b,c,d);', 0),
    ('local datatype t = A | B in val x = A end;', 0),
    ('structure A = struct structure B = struct val z = 2 end end; val x = A.B.z;', 0),
    ('val x = 1; val x = 2; val y = x;', 0),
    ('fun even n = if n = 0 then true else odd (n-1) and odd n = if n = 0 then false else even (n-1);', 1),
    ('fun f x = let fun g y = y x in g (fn z => z) end;', 0),
    ('val x : bool = 5;', 1),
    ('val (x,x) = (1,2);', 1),
    ('fun f (x,x) = x;', 1),
    ('val (x,y) = 1;', 1),
    ('fun f x = x x;', 1),
    ('val x = "héllo"; val y = foo;', 1),
    ('datatype t = C int; val x = C "x";', 1),
    ('datatype t = C int; val x = C 2;', 0),
    ('fun f x = case x of (a,b) => a a;', 1),
    ('structure S = struct val x = 1 end; val x = S.x 4;', 1),
    ('val f = fn x => x; val x = (f 1, f "a");', 0),
    ('datatype t = A | B int; fun f x = case x of A => 0 | B y => y; val z = f (B 3);', 0),
    ('structure S = struct datatype t = A | B int; fun f x = case x of A => 0 | B n => n end; val z = S.f (S.B 5);', 0),
    ('datatype t = A | B int; exception E t; fun f x = (raise E x) handle E A => 0 | E (B n) => n; val z = f (B 2);', 0),
    ('fun f x y = let val (a,b) = (y,x) in fn z => (a,b,z) end; val z = f 1 2 3;', 0),
    ('val x = (fn f => f (fn x => x)) (fn g => g 5);', 0),
    ('val x = "λ😀"; val y = (x, x);', 0),
    ('fun f x = let val x = x in let val x = x in x end end; val y = f 1;', 0),
    ('val x = ((fn x => fn y => x) 1) "a"; val y = ((fn x => fn y => x) "b") 2;', 0),
    ('val x = (1, 2, 3); val (a,b,c) = x; val y = (c,b,a);', 0),
    ('structure A = struct datatype t = E | F int; val a = F 3 end; '
     'structure B = struct val b = A.a end; val z = B.b;', 0),
    ("datatype 'a option = NONE | SOME 'a; val x = SOME (SOME 2); val SOME (SOME y) = x;", 0),
    ('val a = 0w18446744073709551615; val b = 0wxFFFFFFFFFFFFFFFF;', 0),
    ('fun f x = (x,x,x,x,x,x,x,x,x,x,x,x,x,x,x,x,x,x,x,x); val z = f 1;', 0),
    ('fun f x = case x of 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | _ => 5; val z = f 2;', 0),
    ('datatype t = A | A;', 1),
    ('datatype t = A | B and u = A | C;', 0),
    ('datatype t = X t | Y u and u = Z t;', 0),
    ("datatype 'a t = A 'a | B 'b;", 1),
    ("datatype ('a,'b) pair = P 'a 'b; val x = P 1 2;", 0),
    ("type 'a t = 'a; type 'b u = 'b t; val x : int u = 1;", 0),
    ("type ('a,'a) t = int;", 1),
    ('exception E int; exception E int; val a = E 1;', 0),
    ('structure X = struct exception E int end; val x = (raise X.E 1) handle X.E y => y;', 0),
    ('local structure M = struct val x = 3 end in val y = M.x end;', 0),
    ('val x = let fun f x = g x and g x = f x in f end;', 1),
    ('val x = let exception E int in (raise E 2) handle E x => x end;', 1),
    ('val x = ((1,2), (3,4)); val ((a,b),(c,d)) = x;', 0),
    ('val f = fn x => x; val (a,b) = (f 1, f "a");', 0),
    ('val f = fn x => x; val z = (f (fn x => x)) 1;', 0),
    ('datatype a = A a | B; fun f x = case x of A (A y) => y | _ => B;', 0),
    ('fun f (x as x) = x;', 1),
    ('fun f (x as (y,x)) = y;', 1),
    ('datatype tree = L | N tree tree; fun swap x = case x of L => L | N a b => N (swap b) (swap a); val z = swap (N L L);', 0),
    ('datatype t = A | B int; datatype u = C t | D; fun f (C (B x)) = x | f _ = 0;', 1),
    ('exception X int; fun f x = (raise X x) handle X n => n;', 0),
    ('fun map f xs = case xs of [] => [] | x::xs => (f x)::map f xs; val x = map (fn x => x) [1,2,3];', 0),
    ('local val x = 42 in fun f y = (x,y) end; val z = f 1;', 0),
    ('structure M = struct datatype t = A | B int; fun f x = case x of A => 0 | B y => y end; val z = M.f (M.B 4);', 0),
    ('val f = let val z = 4 in fn x => fn y => (x,z,y) end; val z = f 2 3;', 1),
    ('fun f x y z = let fun h a b = (x,y,z,a,b) in h end; val g = f 1 2 3;', 1),
    ('exception E; fun f x = (raise E) handle E => x | _ => 0;', 0),
    ('val a = 0w0; val b = 0wxFFFFFFFFFFFFFFFF; val c = 0w123456789;', 0),
    ('fun f x = case x of 0 => 10 | 1 => 11 | 2 => 12 | 3 => 13 | 4 => 14 | _ => 100;', 0),
    ('datatype t = A | B | C | D | E | F | G | H | I | J; fun f x = case x of A => 1 | J => 2 | _ => 3;', 0),
    ('val f = fn (a,b,c,d,e,f,g,h) => (h,g,f,e,d,c,b,a); val y = f (1,2,3,4,5,6,7,8);', 0),
    ('val x = (fn f => f (fn x => x)) (fn g => (g 1, g "a"));', 1),
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
    'val a = Array.array 2 (Array.array 3 0); val _ = Array.update (Array.sub a 1) 2 4; val _ = print_int (Array.sub (Array.sub a 0) 2);',
    'val a = Word8Array.array 3 (Word8.fromInt 1); val _ = Word8Array.update a 1 (Word8.fromInt 2); val _ = Word8Array.copy a 0 2 a 1; val _ = print_int (Word8.toInt (Word8Array.sub a 2));',
    'fun even n = if n = 0 then 1 else odd (n-1) and odd n = if n = 0 then 0 else even (n-1); val _ = print_int (even 8);',
    'val _ = print (String.substring "abcdef" 2 3);',
    'fun f xs = List.foldl (fn x => fn a => a + x*x) 0 xs; val _ = print_int (f [1,2,3,4]);',
    'val _ = print (String.concat ["a", "b"]);',
    'val _ = print_int (List.hd (List.map (fn x => x + 1) [1,2,3]));',
    'val _ = print (Int.toString ~123);',
    'val _ = print_int (Vector.sub (Vector.fromList [1,2,3]) 1);',
    'val _ = print_int (List.hd (List.rev [1,2,3]));',
    'fun f xs = List.foldr (fn x => fn n => x - n) 0 xs; val _ = print_int (f [1,2,3,4]);',
    'val a = Array.fromList [5,6,7]; val _ = Array.update a 1 8; val _ = print_int (Array.length a + Array.sub a 1);',
    'exception E; fun f n = if n = 0 then raise E else n; val x = (f 0 handle E => 7); val _ = print_int x;',
    'val x = Word64.xorb (Word64.fromInt 123) (Word64.fromInt 456); val _ = print_int (Word64.toInt x);',
    'datatype t = N int | P t t; fun size x = case x of N n => n | P l r => size l + size r; '
    'val _ = print_int (size (P (N 2) (N 3)));',
    'val a = Array.array 1 0; fun f x = (Array.update a 0 (Array.sub a 0 + x); Array.sub a 0); '
    'val _ = print_int (f 3 + f 7);',
    'fun f x = let fun g y = fn z => x + y + z in g end; val _ = print_int (f 1 2 3);',
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


def rich_expression(rng, depth, variables):
    """Generate an integer expression with scoped closures and patterns."""
    if depth == 0:
        return rng.choice(variables + ['0', '1', '2', '~1'])
    left = rich_expression(rng, depth - 1, variables)
    right = rich_expression(rng, depth - 1, variables)
    form = rng.randrange(8)
    if form == 0:
        return f'({left} + {right})'
    if form == 1:
        return f'({left} * {right})'
    if form == 2:
        return f'(if {left} < {right} then {left} else {right})'
    if form == 3:
        body = rich_expression(rng, depth - 1, variables + ['z'])
        return f'(let val z = {left} in {body} end)'
    if form == 4:
        body = rich_expression(rng, depth - 1, variables + ['z'])
        return f'((fn z => {body}) {left})'
    if form == 5:
        body = rich_expression(rng, depth - 1, variables + ['u', 'v'])
        return f'(case ({left},{right}) of (u,v) => {body})'
    if form == 6:
        body = rich_expression(rng, depth - 1, variables + ['z'])
        return f'((fn f => f {left}) (fn z => {body}))'
    body = rich_expression(rng, depth - 1, variables + ['z'])
    return f'(let fun g z = {body} in g {left} end)'


def rich_source(rng):
    body = rich_expression(rng, rng.randrange(1, 4), ['x', 'y'])
    return f'fun f x y = {body}; val z = f 1 2;'


def structured_source(rng):
    """Generate accepted programs that exercise closures, patterns and modules."""
    a, b, c = (rng.randrange(1000) for _ in range(3))
    return rng.choice([
        f'datatype t = A | B int | C int int; '
        f'fun f x = case x of A => {a} | B n => n | C n m => m; val y = f (C {b} {c});',
        f'fun f x = let fun g y = fn z => (x,y,z) in g {a} end; val y = f {b} {c};',
        f'exception E int; fun f x = (raise E x) handle E n => (n,{a}); val y = f {b};',
        f'structure S = struct datatype t = A | B int; '
        f'fun f x = case x of A => {a} | B n => n end; val y = S.f (S.B {b});',
        f'val id = fn x => x; val a = id {a}; val b = id "str"; val c = id (a,b,{b});',
        f'fun f x = case x of [] => [] | h::t => h::t; val y = f [{a},{b},{c}];',
        f'datatype tree = Leaf int | Node tree tree; '
        f'fun f x = case x of Leaf n => n | Node (Leaf n) y => n | Node x y => {a}; '
        f'val y = f (Node (Leaf {b}) (Leaf {c}));',
        f'local datatype t = A int | B in fun f x = case x of A y => y | B => {a}; val y = f (A {b}) end;',
        f'fun f (a,b,c) = fn (x,y) => (c,b,a,y,x); val y = f ({a},{b},{c}) ({b},{a});',
        f'val x = let val x = {a} in let val y = fn z => (x,z) in y {b} end end;',
        f'fun even xs = case xs of [] => True | x::rest => odd rest '
        f'and odd xs = case xs of [] => False | x::rest => even rest; '
        f'val y = if even [{a},{b},{c}] then {b} else {c};',
        f'fun make x = let fun f y z = (x,y,z) in f end; '
        f'val y = make {a} {b} {c};',
        f'datatype t = A int | B t t; '
        f'fun fold f x = case x of A n => f n | B l r => fold f l; '
        f'val y = fold (fn n => (n,{a})) (B (A {b}) (A {c}));',
        f'exception E int; exception F int; '
        f'fun f x = ((raise E x) handle E n => raise F n) '
        f'handle F n => (n,{b}); val y = f {c};',
        f'structure A = struct val x = {a}; fun f y = (x,y) end; '
        f'structure B = struct val x = A.f {b}; fun f y = (x,A.f y) end; '
        f'val y = B.f {c};',
        f'fun f xs = case xs of [] => {a} | x::rest => '
        f'(case rest of [] => x | y::tail => y); '
        f'val y = f [{a},{b},{c}];',
    ])


def backend_options(rng):
    """Combine options that influence closure, BVL and backend lowering."""
    groups = [
        ['--multi=true', '--multi=false'], ['--known=true', '--known=false'],
        ['--call=true', '--call=false'], ['--split=true', '--split=false'],
        ['--tmc=true', '--tmc=false'], ['--tailrec=true', '--tailrec=false'],
        ['--reg_alg=0', '--reg_alg=1', '--reg_alg=2', '--reg_alg=3', '--reg_alg=4'],
        ['--gc=none', '--gc=simple', '--gc=gen2,3'], ['--jump=true', '--jump=false'],
        ['--inline_size=0', '--inline_size=1', '--inline_size=5'],
        ['--exp_cut=0', '--exp_cut=1', '--exp_cut=5'],
    ]
    return [rng.choice(group) for group in rng.sample(groups, rng.randrange(1, 5))]


def config_mutations(rng):
    """Exercise configuration validation and first-occurrence precedence."""
    values = {
        'multi': ['true', 'false', 'True', '', '1'],
        'known': ['true', 'false', 'bad'], 'call': ['true', 'false', 'bad'],
        'max_app': ['0', '1', '3', 'bad', ''],
        'inline_factor': ['0', '1', '2', 'bad', ''],
        'max_body_size': ['0', '1', '2', 'bad', ''],
        'tag_bits': ['0', '1', '2', 'bad', ''],
        'len_bits': ['0', '1', '8', 'bad', ''],
        'pad_bits': ['0', '1', '2', 'bad', ''],
        'len_size': ['0', '1', '8', 'bad', ''],
        'hash_size': ['0', '1', '9', 'bad', ''],
        'gc': ['none', 'simple', 'gen', 'gen1', 'gen0,2', 'bad'],
        'reg_alg': ['0', '1', '2', '4', 'bad', ''],
        'jump': ['true', 'false', 'bad'],
        'main_return': ['true', 'false', 'bad'],
        'split': ['true', 'false', 'bad'],
        'exp_cut': ['0', '1', 'bad', ''],
        'inline_size': ['0', '1', 'bad', ''],
    }
    flags = []
    for _ in range(rng.randrange(1, 4)):
        name = rng.choice(list(values))
        flags.append(f'--{name}={rng.choice(values[name])}')
    return flags


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


def unicode_mutated_source(rng):
    """Mutate UTF-8 source at character boundaries, including error locations."""
    source = rng.choice([
        'val x = "héllo";', 'val λ = 1;', 'val x = "😀";',
        '(* áβ *) val x = 1;', 'val x = 3;\nval y = missing;',
        'fun f (x,y) = x;',
    ])
    alphabet = 'λéß😀中\r\t\\"(*):;#0129'
    for _ in range(rng.randrange(1, 4)):
        position = rng.randrange(len(source) + 1)
        char = rng.choice(alphabet)
        skip = rng.randrange(2) if position < len(source) else 0
        source = source[:position] + char + source[position + skip:]
    return source


def byte_mutated_source(rng):
    """Mutate input bytes, including malformed UTF-8 and control characters."""
    source = rng.choice([
        b'val x = "abc\\n\\000\\255";', b'val x = #"a";',
        b'(* one (* two *) *) val x = 1;',
        b'datatype t = A int | B; fun f x = case x of A a => a | B => 0;',
        b'val x : int = 5; val y = x;',
        b'structure A = struct val x = 1 end; val y = A.x;',
        b'val x = 0wx12ab;',
        b'exception E int; val x = (raise E 1) handle E x => x;',
    ])
    alphabet = b'abcdefghijklXYZ0123456789 !@#$%^&*()-_=+[]{};:\'"\\,./\n\t\r\x00\x7f\x80\xa9\xc0\xc3\xe2\xff'
    for _ in range(rng.randrange(1, 5)):
        position = rng.randrange(len(source) + 1)
        operation = rng.randrange(3)
        char = bytes([rng.choice(alphabet)])
        skip = operation != 0 and position < len(source)
        source = source[:position] + (char if operation != 1 else b'') + source[position + skip:]
    return source


def sexp_mutated_source(rng, seeds):
    """Replace one S-expression atom, including constructors and numeric fields."""
    source = rng.choice(seeds)
    atoms = list(re.finditer(rb'[^()\s]+', source))
    atom = rng.choice(atoms)
    replacement = rng.choice([
        b'0', b'1', b'99', b'999999999999999999999999999999999',
        b'Wrong', b'NONE', b'T', b'F', b'""', b'"abc"', b'()',
        b'-1', b'~1', b'(', b')', b'"\\\\"',
    ])
    return source[:atom.start()] + replacement + source[atom.end():]


def run(binary, source, timeout, exclude_prelude=False, extra_flags=()):
    flags = ['--exclude_prelude=true'] if exclude_prelude else []
    payload = source if isinstance(source, bytes) else source.encode('utf-8')
    return subprocess.run([str(binary), '--target=riscv', *flags, *extra_flags], input=payload,
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
    modes.add_argument('--unicode-mutations', action='store_true',
                       help='mutate UTF-8 source with the prelude excluded')
    modes.add_argument('--byte-mutations', action='store_true',
                       help='mutate arbitrary source bytes with the prelude excluded')
    modes.add_argument('--corpus', action='store_true',
                       help='compare fixed language-feature and standard-prelude programs')
    modes.add_argument('--structured', action='store_true',
                       help='compare accepted closure, datatype, pattern and module programs')
    modes.add_argument('--rich', action='store_true',
                       help='compare generated nested closures, bindings and patterns')
    modes.add_argument('--backend-options', action='store_true',
                       help='compare accepted programs with varied backend options')
    modes.add_argument('--config-mutations', action='store_true',
                       help='compare successful and rejected configuration combinations')
    modes.add_argument('--display-mutations', action='store_true',
                       help='compare type and S-expression display output for mutated source and bytes')
    modes.add_argument('--sexp-mutations', action='store_true',
                       help='mutate pinned-compiler S-expression AST output and compare bootstrap input')
    args = parser.parse_args()
    if args.count < 0 or args.timeout <= 0:
        parser.error('count must be nonnegative and timeout must be positive')
    version = subprocess.check_output([str(args.reference), '--version'], text=True, timeout=args.timeout)
    if f'CakeML: {CAKEML_REV}' not in version or f'HOL4:   {HOL_REV}' not in version:
        raise SystemExit('reference compiler does not report the pinned CakeML and HOL revisions')
    rng = random.Random(args.seed)
    sexp_seeds = []
    if args.sexp_mutations:
        seed_sources = [
            'datatype t = A | B int; fun f x = case x of A => 0 | B n => n;',
            "datatype 'a opt = N | S 'a; val a = S 7;",
            'structure M = struct val y = "abc"; exception E int end;',
            'val x = (1, 0w255, #"a", "abc");',
            'fun f x = let val y = x in fn z => y end;',
        ]
        for source in seed_sources:
            result = run(args.reference, source, args.timeout, True, ['--print_sexp'])
            if result.returncode != 0 or result.stdout or not result.stderr.strip():
                raise SystemExit(f'could not obtain S-expression seed from pinned compiler: {source!r}')
            sexp_seeds.append(result.stderr.strip())
    corpus = [(source, status, True) for source, status in SOURCE_CORPUS]
    corpus += [(source, 0, False) for source in BASIS_CORPUS]
    count = len(corpus) if args.corpus else args.count
    sexp_outcomes = {}
    for index in range(count):
        extra_flags = (['--sexp=true', rng.choice(['--types', '--print_sexp', '--skip_type_inference=true'])]
                       if args.sexp_mutations else backend_options(rng) if args.backend_options else
                       config_mutations(rng) if args.config_mutations else
                       rng.choice([['--types'], ['--print_sexp'], ['--types', '--print_sexp'],
                                   ['--print_sexp', '--skip_type_inference=true']])
                       if args.display_mutations else [])
        source = (sexp_mutated_source(rng, sexp_seeds) if args.sexp_mutations else
                  'val x = 1;' if args.config_mutations else
                  'fun f x y = let fun g z = (x,y,z) in g y end; val z = f 1 2;' if args.backend_options else
                  corpus[index][0] if args.corpus else
                  rng.choice([deep_mutated_source, unicode_mutated_source, byte_mutated_source])(rng) if args.display_mutations else
                  byte_mutated_source(rng) if args.byte_mutations else
                  unicode_mutated_source(rng) if args.unicode_mutations else
                  deep_mutated_source(rng) if args.deep_mutations else
                  mutated_source(rng) if args.mutations else structured_source(rng) if args.structured else
                  rich_source(rng) if args.rich else
                  'fun f x = ' + expression(rng, rng.randrange(1, 4)) + '; val _ = print_int (f 2);')
        exclude_prelude = corpus[index][2] if args.corpus else args.mutations or args.deep_mutations or args.unicode_mutations or args.byte_mutations or args.structured or args.backend_options or args.config_mutations or args.display_mutations or args.sexp_mutations
        try:
            original = run(args.reference, source, args.timeout, exclude_prelude, extra_flags)
            candidate = run(args.cake, source, args.timeout, exclude_prelude, extra_flags)
        except subprocess.TimeoutExpired as error:
            raise SystemExit(f'case {index}, seed {args.seed}, options {extra_flags}: compiler timed out: {error}\n{source}')
        expected = (original.returncode, original.stdout, original.stderr)
        actual = (candidate.returncode, candidate.stdout, candidate.stderr)
        if ((args.corpus and original.returncode != corpus[index][1]) or
                (not (args.mutations or args.deep_mutations or args.unicode_mutations or args.byte_mutations or args.config_mutations or args.display_mutations or args.sexp_mutations or args.corpus) and original.returncode != 0) or
                actual != expected):
            def describe(result):
                return (f'exit={result.returncode} stdout_sha256={hashlib.sha256(result.stdout).hexdigest()} '
                        f'stderr={result.stderr!r}')
            raise SystemExit(f'case {index}, seed {args.seed}, options {extra_flags}: output mismatch or rejection\n{source!r}\n'
                             f'original: {describe(original)}\ncandidate: {describe(candidate)}')
        if args.sexp_mutations:
            outcome = (extra_flags[-1], original.returncode)
            sexp_outcomes[outcome] = sexp_outcomes.get(outcome, 0) + 1
        print(f'case {index}: exact output matches', flush=True)
    if args.sexp_mutations:
        for (mode, status), total in sorted(sexp_outcomes.items()):
            print(f'{mode}: {total} cases with exit status {status}')
    print(f'{count} cases matched' + ('' if args.corpus else f' (seed {args.seed})'))


if __name__ == '__main__':
    main()
