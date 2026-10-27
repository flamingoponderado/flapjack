#!/usr/bin/env python3
"""Translate the pinned HOL basis AST into constructor-for-constructor Lean."""
import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / 'scripts/hol-probes/cake_basis_probe.out'
OUTPUT = ROOT / 'Flapjack/Basis/BasisProg.lean'
ARITY = {
    'Dtype': 2, 'Dlet': 3, 'Dletrec': 2, 'Dlocal': 2, 'Dmod': 2,
    'Dtabbrev': 4, 'Dexn': 3, 'Atapp': 2, 'Atfun': 2, 'Attup': 1, 'Atvar': 1,
    'Pvar': 1, 'Pcon': 2, 'Pany': 0, 'Short': 1, 'Long': 2,
    'App': 2, 'Var': 1, 'Con': 2, 'Fun': 2, 'Lit': 1, 'Let': 3,
    'Letrec': 2, 'Mat': 2, 'If': 3, 'Raise': 1, 'Handle': 2, 'Log': 3,
    'Arith': 2, 'FromTo': 2, 'Shift': 3, 'Test': 2, 'Compare': 1, 'AltCompare': 1,
    'IntLit': 1, 'StrLit': 1, 'Char': 1, 'Word8': 1, 'Word64': 1, 'Float64': 1,
    'WordT': 1, 'FFI': 1, 'SOME': 1, 'NONE': 0, 'Locs': 2, 'POSN': 2,
}
NULLARY = '''Aalloc AallocEmpty Abs Add Alength And Andalso Asr Asub Aupdate
Aw8alloc Aw8length Aw8sub Aw8update BoolT CharT ConfigGC CopyAw8Aw8 CopyAw8Str
CopyStrAw8 CopyStrStr Div Equal Equality Explode Float64T FMA Geq Gt Implode
IntT Leq ListAppend Lsl Lsr Lt Mod Mul Neg Not Opapp Opassign Opderef Opref Or
Orelse Sqrt StrT Strcat Strlen Strsub Sub UNKNOWNpt VfromList Vlength Vsub W64
W8 Xor'''.split()
ARITY.update({x: 0 for x in NULLARY})
OVERRIDE = {'Fun': '.fn', 'If': '.if_', 'Let': '.let_', 'SOME': 'some', 'NONE': 'none',
            'UNKNOWNpt': '.unknownPt', 'POSN': '.posn', 'Locs': '.locs',
            'FFI': '.ffi', 'FMA': '.fma', 'W8': '.w8', 'W64': '.w64',
            'IntT': '.intT', 'CharT': '.charT', 'BoolT': '.boolT', 'StrT': '.strT',
            'Float64T': '.float64T', 'WordT': '.wordT', 'Atapp': '.atapp', 'Atfun': '.atfun',
            'Attup': '.attup', 'Atvar': '.atvar', 'Dtabbrev': '.dtabbrev',
            'Dletrec': '.dletrec', 'Dlocal': '.dlocal', 'Dmod': '.dmod', 'Dtype': '.dtype',
            'Dexn': '.dexn', 'Dlet': '.dlet', 'Pvar': '.pvar', 'Pcon': '.pcon', 'Pany': '.pany',
            'IntLit': '.intLit', 'StrLit': '.strLit', 'Word8': '.word8', 'Word64': '.word64',
            'Float64': '.float64', 'Locs': '.locs', 'VfromList': '.vfromList',
            'CopyStrStr': '.copyStrStr', 'CopyStrAw8': '.copyStrAw8',
            'CopyAw8Str': '.copyAw8Str', 'CopyAw8Aw8': '.copyAw8Aw8',
            'ListAppend': '.listAppend', 'ConfigGC': '.configGC'}

# HOL's string printer uses SML-style escapes. Values are byte strings.
def decode(s):
    out = []
    i = 0
    escapes = {'a': 7, 'b': 8, 't': 9, 'n': 10, 'v': 11, 'f': 12, 'r': 13,
               '\\': 92, '"': 34}
    while i < len(s):
        c = s[i]; i += 1
        if c != '\\':
            if ord(c) > 255: raise ValueError('non-byte HOL character')
            out.append(ord(c)); continue
        if i >= len(s): raise ValueError('trailing string escape')
        c = s[i]; i += 1
        if c in escapes: out.append(escapes[c])
        elif c == '^':
            if i >= len(s): raise ValueError('truncated control escape')
            out.append(ord(s[i]) - 64); i += 1
        elif c.isdigit():
            digits = c + s[i:i+2]; i += 2
            if not re.fullmatch(r'\d{3}', digits): raise ValueError('bad numeric escape')
            out.append(int(digits))
        else: raise ValueError('unknown escape ' + repr(c))
    if any(not 0 <= x <= 255 for x in out): raise ValueError('character outside byte range')
    return out

def mlstring(raw):
    bs = decode(raw)
    if all(x == 9 or x == 10 or x == 13 or 32 <= x < 127 for x in bs):
        return '(ofString ' + json.dumps(bytes(bs).decode('ascii')) + ')'
    return '(MlString.implode [' + ', '.join(map(str, bs)) + '])'

TOKEN = re.compile(r'\s*(«(?:\\\^.|\\.|[^»])*»|#"(?:\\\^.|\\.|[^"\\])*"|0x[0-9A-Fa-f]+w|[0-9]+w|~?[0-9]+|[A-Za-z_][A-Za-z_0-9]*|[()\[\],;])')

def generate():
    rows = INPUT.read_text().splitlines()
    if len(rows) != 2 or rows[1] != 'length=96': raise ValueError('unexpected basis length capture')
    text = rows[0]
    if not text.startswith('basis='): raise ValueError('missing basis capture')
    text = text[len('basis='):]
    tokens = []
    while text.strip():
        m = TOKEN.match(text)
        if not m: raise ValueError('unknown HOL syntax: ' + repr(text[:100]))
        tokens.append(m.group(1)); text = text[m.end():]
    pos = 0
    def take(expected=None):
        nonlocal pos
        t = tokens[pos]; pos += 1
        if expected is not None and t != expected: raise ValueError((expected, t, pos))
        return t
    def expr():
        t = take()
        if t == '(':
            first = expr()
            if tokens[pos] == ',':
                items = [first]
                while tokens[pos] == ',': take(','); items.append(expr())
                take(')'); return '(' + ', '.join(items) + ')'
            take(')'); return first
        if t == '[':
            items = []
            if tokens[pos] != ']':
                items.append(expr())
                while tokens[pos] == ';': take(';'); items.append(expr())
            take(']'); return '[' + ', '.join(items) + ']'
        if t.startswith('«'): return mlstring(t[1:-1])
        if t.startswith('#"'):
            bs = decode(t[2:-1])
            if len(bs) != 1: raise ValueError('invalid character literal')
            return str(bs[0])
        if t.endswith('w') and (t[0].isdigit()):
            return '(BitVec.ofNat _ ' + str(int(t[:-1], 0)) + ')'
        if t[0].isdigit(): return t
        if t.startswith('~') and t[1:].isdigit(): return '(-' + t[1:] + ')'
        if t == 'unknown_loc': return 'unknownLoc'
        if t in ARITY:
            name = OVERRIDE.get(t, '.' + t[0].lower() + t[1:])
            args = [expr() for _ in range(ARITY[t])]
            return '(' + ' '.join([name] + args) + ')' if args else name
        raise ValueError(('unknown HOL constructor', t, pos))
    take('['); decls = []
    if tokens[pos] != ']':
        decls.append(expr())
        while tokens[pos] == ';': take(';'); decls.append(expr())
    take(']')
    if pos != len(tokens): raise ValueError('trailing HOL syntax')
    header = '''-- Generated from the pinned HOL basis capture by scripts/generate-cake-basis.py.\nimport Flapjack.AstHOL.Syntax\n\n/-! The original generated CakeML basis declarations in their source order. -/\nnamespace Flapjack.Basis.BasisProg\nopen Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.Misc.Location\nopen Flapjack.Basis.Pure.MlString\n\nset_option maxRecDepth 8192\nset_option maxHeartbeats 0\n\n'''
    parts = [f'private def d{i} : Dec := {d}\n' for i, d in enumerate(decls)]
    body = '''\n/-- The pinned original CakeML standard basis program. Source review of the\ngenerated declaration and its complete imported carriers remains pending. -/\n@[hol "cakeml/basis/basisProgScript.sml" "basis_def"]\ndef basis : List Dec :=\n  [''' + ', '.join(f'd{i}' for i in range(len(decls))) + ''']\n\nend Flapjack.Basis.BasisProg\n'''
    return header + ''.join(parts) + body

if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--check', action='store_true'); args = parser.parse_args()
    result = generate()
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text() != result: raise SystemExit('basis rendering is stale')
        print('CakeML basis matches the captured HOL AST')
    else: OUTPUT.write_text(result)
