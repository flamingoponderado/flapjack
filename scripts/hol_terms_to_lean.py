#!/usr/bin/env python3
"""Render exported HOL definition theorems (S-expressions) as Lean definitions.

Input: a file of `(def THY NAME DEFNAME TERM)` records written by
`scripts/l3/export_riscv_defs.sml`, where TERM is the HOL conclusion with
`(v NAME TY)`, `(c THY NAME TY)`, `(a F X)` and `(l VAR BODY)` nodes and types
`(tv NAME)` / `(ty THY OP ARGS...)`.

Output: Lean definitions over the `Flapjack/RiscV/L3/Types.lean` carriers, one per HOL
definition, in the exported (dependency) order. HOL constants outside the exported theories
are rendered by the `CONSTANTS` table below; each entry is a candidate rendering of one HOL
constant whose use must be source-reviewed. Any constant without an entry makes the definition unrenderable, and it is reported
instead of emitted. This is a transcription aid: it does not establish HOL-to-Lean
equivalence, which remains a matter of source review and parity probes.
"""
from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path

sys.setrecursionlimit(1000000)

# ---------------------------------------------------------------------------
# S-expression reader


def read_sexps(text: str):
    tokens = re.finditer(r'\(|\)|"(?:[^"\\]|\\.)*"|[^\s()]+', text)
    stack: list[list] = [[]]
    for m in tokens:
        tok = m.group()
        if tok == '(':
            stack.append([])
        elif tok == ')':
            done = stack.pop()
            stack[-1].append(tuple(done))
        elif tok.startswith('"'):
            stack[-1].append(Str(bytes(tok[1:-1], 'utf-8').decode('unicode_escape')))
        else:
            stack[-1].append(tok)
    return stack[0]


class Str(str):
    pass


# ---------------------------------------------------------------------------
# HOL types


@dataclass(frozen=True)
class Ty:
    thy: str
    op: str
    args: tuple

    def __str__(self):
        return f'{self.thy}${self.op}' + (f'({",".join(map(str, self.args))})' if self.args else '')


@dataclass(frozen=True)
class TyVar:
    name: str


def parse_ty(s) -> Ty | TyVar:
    if s[0] == 'tv':
        return TyVar(s[1])
    return Ty(s[1], s[2], tuple(parse_ty(a) for a in s[3:]))


def fcp_size(t) -> int | None:
    """The numeral denoted by an fcp index type (bit0/bit1/one), or None."""
    if not isinstance(t, Ty):
        return None
    if t.thy == 'one' and t.op == 'one':
        return 1
    if t.thy == 'fcp' and t.op in ('bit0', 'bit1'):
        inner = fcp_size(t.args[0])
        if inner is None:
            return None
        return 2 * inner + (1 if t.op == 'bit1' else 0)
    return None


def word_width(t) -> int | None:
    if isinstance(t, Ty) and t.thy == 'fcp' and t.op == 'cart' and t.args[0] == Ty('min', 'bool', ()):
        return fcp_size(t.args[1])
    return None


def fun_parts(t):
    args = []
    while isinstance(t, Ty) and t.thy == 'min' and t.op == 'fun':
        args.append(t.args[0])
        t = t.args[1]
    return args, t


KEYWORDS = {
    'done', 'at', 'by', 'fun', 'have', 'show', 'from', 'let', 'in', 'if', 'then', 'else', 'do',
    'match', 'with', 'end', 'open', 'where', 'deriving', 'structure', 'inductive', 'instance',
    'def', 'theorem', 'for', 'unless', 'return', 'try', 'catch', 'finally', 'mut', 'break',
    'continue', 'Type', 'Prop', 'Sort', 'true', 'false', 'not', 'and', 'or', 'namespace',
    'section', 'variable', 'universe', 'import', 'export', 'private', 'protected', 'partial',
    'noncomputable', 'macro', 'syntax', 'notation', 'infix', 'calc', 'suffices', 'obtain',
    'this', 'local', 'scoped', 'attribute', 'set_option', 'mod', 'λ',
}


def ident(n: str) -> str:
    if n in KEYWORDS or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", n):
        return '«' + n + '»'
    return n


class Unrenderable(Exception):
    pass


def match_ty(pattern, actual, inst):
    if isinstance(pattern, TyVar):
        inst.setdefault(pattern.name, actual)
        return
    if isinstance(actual, Ty) and pattern.thy == actual.thy and pattern.op == actual.op:
        for a, b in zip(pattern.args, actual.args):
            match_ty(a, b, inst)


def def_head_type(term):
    """The type of the defined constant of a definition theorem, and its type variables."""
    t = term
    while True:
        h, args = strip_comb(t)
        if is_const(h, 'bool', '/\\') and len(args) == 2:
            t = args[0]
            continue
        if is_const(h, 'bool', '!') and len(args) == 1 and isinstance(args[0], Lam):
            t = args[0].body
            continue
        break
    h, args = strip_comb(t)
    f, _ = strip_comb(args[0])
    return f.ty, tyvars(f.ty, [])


def tyvar_name(n: str) -> str:
    return 'T' + re.sub(r"[^A-Za-z0-9]", "", n)


def tyvars(t, acc):
    if isinstance(t, TyVar):
        if t.name not in acc:
            acc.append(t.name)
    else:
        for a in t.args:
            tyvars(a, acc)
    return acc


def ty_lean(t) -> str:
    if isinstance(t, TyVar):
        return tyvar_name(t.name)
    w = word_width(t)
    if w is not None:
        return f'(BitVec {w})'
    key = (t.thy, t.op)
    if key == ('min', 'bool'):
        return 'Bool'
    if key == ('num', 'num'):
        return 'Nat'
    if key == ('integer', 'int'):
        return 'Int'
    if key == ('one', 'one'):
        return 'Unit'
    if key == ('string', 'char'):
        return 'HolChar'
    if key == ('min', 'fun'):
        return f'({ty_lean(t.args[0])} → {ty_lean(t.args[1])})'
    if key == ('pair', 'prod'):
        return f'({ty_lean(t.args[0])} × {ty_lean(t.args[1])})'
    if key == ('option', 'option'):
        return f'(Option {ty_lean(t.args[0])})'
    if key == ('list', 'list'):
        return f'(List {ty_lean(t.args[0])})'
    if key == ('binary_ieee', 'rounding'):
        return 'HolRounding'
    if key == ('binary_ieee', 'float_compare'):
        return 'HolFloatCompare'
    if t.thy == 'riscv':
        return ident(t.op)
    raise Unrenderable(f'type {t}')


# ---------------------------------------------------------------------------
# HOL terms


@dataclass(frozen=True)
class Var:
    name: str
    ty: object


@dataclass(frozen=True)
class Const:
    thy: str
    name: str
    ty: object


@dataclass(frozen=True)
class Comb:
    f: object
    x: object


@dataclass(frozen=True)
class Lam:
    v: Var
    body: object


def parse_tm(s):
    tag = s[0]
    if tag == 'v':
        return Var(s[1], parse_ty(s[2]))
    if tag == 'c':
        return Const(s[1], s[2], parse_ty(s[3]))
    if tag == 'a':
        return Comb(parse_tm(s[1]), parse_tm(s[2]))
    if tag == 'l':
        return Lam(parse_tm(s[1]), parse_tm(s[2]))
    raise ValueError(tag)


def type_of(t):
    if isinstance(t, (Var, Const)):
        return t.ty
    if isinstance(t, Comb):
        return fun_parts(type_of(t.f))[1] if False else type_of(t.f).args[1]
    if isinstance(t, Lam):
        return Ty('min', 'fun', (t.v.ty, type_of(t.body)))
    raise TypeError(t)


def strip_comb(t):
    args = []
    while isinstance(t, Comb):
        args.append(t.x)
        t = t.f
    return t, list(reversed(args))


def is_const(t, thy, name):
    return isinstance(t, Const) and t.thy == thy and t.name == name


def numeral_value(t) -> int | None:
    """The value of a HOL numeral body built from ZERO/BIT1/BIT2."""
    if is_const(t, 'arithmetic', 'ZERO'):
        return 0
    h, args = strip_comb(t)
    if len(args) == 1 and is_const(h, 'arithmetic', 'BIT1'):
        v = numeral_value(args[0])
        return None if v is None else 2 * v + 1
    if len(args) == 1 and is_const(h, 'arithmetic', 'BIT2'):
        v = numeral_value(args[0])
        return None if v is None else 2 * v + 2
    return None


def nat_literal(t) -> int | None:
    if is_const(t, 'num', '0'):
        return 0
    h, args = strip_comb(t)
    if len(args) == 1 and is_const(h, 'arithmetic', 'NUMERAL'):
        return numeral_value(args[0])
    return None


# ---------------------------------------------------------------------------
# Rendering


class Renderer:
    def __init__(self, defined: dict[tuple[str, str], str], types: dict[str, dict]):
        self.defined = defined          # (thy, name) -> Lean name
        self.types = types              # riscv type name -> {'ctors': [...], 'fields': [...]}
        self.ctor_type = {c: tname for tname, info in types.items() for c in info.get('ctors', [])}
        self.used_names: set[str] = set()
        self.generic_types: dict = {}
        self.noncomputable = False

    # -- variables ---------------------------------------------------------
    def var(self, v: Var, env: dict) -> str:
        return env.get((v.name, v.ty), ident(v.name))

    def bind(self, v: Var, env: dict) -> tuple[str, dict]:
        base = re.sub(r"[^A-Za-z0-9_]", "_", v.name) or 'x'
        if base == '_eta' or base.startswith('_eta'):
            pass
        elif base.startswith('_'):
            base = 'u' + base
        if base[0].isdigit():
            base = 'x' + base
        name = base
        taken = set(env.values())
        k = 0
        while name in taken or name in KEYWORDS:
            k += 1
            name = f'{base}_{k}'
        env = dict(env)
        env[(v.name, v.ty)] = name
        return name, env

    # -- terms -------------------------------------------------------------
    def tm(self, t, env) -> str:
        if isinstance(t, Var):
            return self.var(t, env)
        if isinstance(t, Lam):
            return self.lam(t, env)
        head, args = strip_comb(t)
        if isinstance(head, Lam):
            # beta-redex: render as an application of the lambda
            return '(' + self.lam(head, env) + ' ' + ' '.join(self.atom(a, env) for a in args) + ')'
        if isinstance(head, Var):
            return '(' + self.var(head, env) + ''.join(' ' + self.atom(a, env) for a in args) + ')' if args else self.var(head, env)
        assert isinstance(head, Const)
        return self.const_app(head, args, env)

    def atom(self, t, env) -> str:
        s = self.tm(t, env)
        if re.fullmatch(r"[A-Za-z_«][^ ]*|\([^()]*\)|[0-9]+", s) and not s.startswith('fun '):
            return s
        return '(' + s + ')'

    def lam(self, t: Lam, env) -> str:
        name, env2 = self.bind(t.v, env)
        body = self.tm(t.body, env2)
        return f'(fun ({unused(name, body)} : {ty_lean(t.v.ty)}) => {body})'

    def eta(self, head: Const, args, env, arity: int, render):
        """Apply `render` to exactly `arity` arguments, eta-expanding or re-applying."""
        dom, _ = fun_parts(head.ty)
        if len(args) < arity:
            extra = []
            env2 = env
            for i in range(len(args), arity):
                name, env2 = self.bind(Var(f'_eta{i}', dom[i]), env2)
                extra.append((name, dom[i]))
            body = render([self.atom(a, env) for a in args] + [n for n, _ in extra], args + [None] * len(extra))
            return '(' + ''.join(f'fun ({n} : {ty_lean(d)}) => ' for n, d in extra) + body + ')'
        rendered = render([self.atom(a, env) for a in args[:arity]], args[:arity])
        rest = args[arity:]
        if rest:
            return '(' + rendered + ''.join(' ' + self.atom(a, env) for a in rest) + ')'
        return rendered

    def const_app(self, c: Const, args, env) -> str:
        key = (c.thy, c.name)
        # numerals and literals
        if key == ('arithmetic', 'NUMERAL') and len(args) == 1:
            v = numeral_value(args[0])
            if v is None:
                raise Unrenderable('NUMERAL')
            return str(v)
        if key == ('num', '0'):
            return '0'
        if key in self.defined:
            name = self.defined[key]
            generic = self.generic_types.get(key)
            if generic is not None and generic[1]:
                inst = {}
                match_ty(generic[0], c.ty, inst)
                name = '(' + name + ''.join(f' ({tyvar_name(v)} := {ty_lean(inst[v])})' for v in generic[1] if v in inst) + ')'
            return name if not args else '(' + name + ''.join(' ' + self.atom(a, env) for a in args) + ')'
        if c.thy == 'riscv':
            return self.riscv_const(c, args, env)
        if c.name.endswith('_CASE'):
            return self.case(c, args, env)
        if key in SPECIAL:
            return SPECIAL[key](self, c, args, env)
        if key in CONSTANTS:
            arity, fmt = CONSTANTS[key]
            return self.eta(c, args, env, arity,
                            lambda xs, raw: fmt(self, c, xs, raw))
        raise Unrenderable(f'constant {c.thy}${c.name}')

    # -- generated riscv constants -----------------------------------------
    def riscv_const(self, c: Const, args, env) -> str:
        n = c.name
        m = re.fullmatch(r'recordtype\.([A-Za-z_]+)\.seldef\.([A-Za-z0-9_\']+)_fupd', n)
        if m:
            field = ident(m.group(2))
            return self.eta(c, args, env, 2,
                            lambda xs, raw: f'(let r := {xs[1]}; {{ r with {field} := {xs[0]} r.{field} }})')
        m = re.fullmatch(r'recordtype\.([A-Za-z_]+)\.seldef\.([A-Za-z0-9_\']+)', n)
        if m:
            field = ident(m.group(2))
            return self.eta(c, args, env, 1, lambda xs, raw: f'{xs[0]}.{field}')
        m = re.fullmatch(r'recordtype\.([A-Za-z_]+)', n)
        if m:
            tname = m.group(1)
            arity = len(fun_parts(c.ty)[0])
            return self.eta(c, args, env, arity,
                            lambda xs, raw: f'({ident(tname)}.mk' + ''.join(' ' + x for x in xs) + ')')
        if n.endswith('_CASE'):
            return self.case(c, args, env)
        # a constructor of a riscv datatype
        _, rng = fun_parts(c.ty)
        if isinstance(rng, Ty) and rng.thy == 'riscv':
            arity = len(fun_parts(c.ty)[0])
            return self.eta(c, args, env, arity,
                            lambda xs, raw: (f'{ident(rng.op)}.{ident(n)}' if not xs else
                                             f'({ident(rng.op)}.{ident(n)}' + ''.join(' ' + x for x in xs) + ')'))
        raise Unrenderable(f'riscv constant {n}')

    def case(self, c: Const, args, env) -> str:
        """`T_CASE x f1 ... fn` as a `match` on the scrutinee."""
        dom, _ = fun_parts(c.ty)
        scrut_ty = dom[0]
        info = self.datatype_info(scrut_ty)
        if info is None or len(args) < 1 + len(info):
            raise Unrenderable(f'case {c.name}')
        scrut = self.tm(args[0], env)
        alts = []
        for (ctor, nargs), branch in zip(info, args[1:1 + len(info)]):
            names = []
            env2 = env
            b = branch
            for k in range(nargs):
                if isinstance(b, Lam):
                    name, env2 = self.bind(b.v, env2)
                    names.append(name)
                    b = b.body
                else:
                    # branch given as a function value: apply it to fresh variables
                    name, env2 = self.bind(Var(f'a{k}', None), env2)
                    names.append(name)
                    b = ('apply', b, names[:])
            if isinstance(b, tuple):
                body = '(' + self.tm(b[1], env) + ''.join(' ' + n for n in b[2]) + ')'
            else:
                body = self.tm(b, env2)
            names = [unused(n, body) for n in names]
            pat = self.pattern(scrut_ty, ctor, names)
            alts.append(f'| {pat} => {body}')
        rest = args[1 + len(info):]
        m = f'(match {scrut} with ' + ' '.join(alts) + ')'
        if rest:
            return '(' + m + ''.join(' ' + self.atom(a, env) for a in rest) + ')'
        return m

    def datatype_info(self, t):
        """[(constructor, arity)] for a case scrutinee type."""
        if isinstance(t, Ty) and t.thy == 'riscv' and t.op in self.types and 'ctors' in self.types[t.op]:
            info = self.types[t.op]
            return list(zip(info['ctors'], info['arity']))
        if isinstance(t, Ty) and t.thy == 'riscv' and t.op in self.types and 'fields' in self.types[t.op]:
            return [('mk', len(self.types[t.op]['fields']))]
        if isinstance(t, Ty) and (t.thy, t.op) in BUILTIN_CASES:
            return BUILTIN_CASES[(t.thy, t.op)]
        return None

    def pattern(self, t, ctor, names):
        if isinstance(t, Ty) and t.thy == 'riscv' and 'fields' in self.types.get(t.op, {}):
            return '⟨' + ', '.join(names) + '⟩'
        if isinstance(t, Ty) and t.thy == 'riscv':
            return f'.{ident(ctor)}' + ''.join(' ' + n for n in names)
        key = (t.thy, t.op)
        if key == ('option', 'option'):
            return 'none' if ctor == 'NONE' else f'some {names[0]}'
        if key == ('pair', 'prod'):
            return f'({names[0]}, {names[1]})'
        if key == ('list', 'list'):
            return '[]' if ctor == 'NIL' else f'{names[0]} :: {names[1]}'
        if key == ('binary_ieee', 'float_compare'):
            return f'.{ctor.lower()}'
        if key == ('min', 'bool'):
            return ctor
        raise Unrenderable(f'pattern {t}')


BUILTIN_CASES = {
    ('option', 'option'): [('NONE', 0), ('SOME', 1)],
    ('pair', 'prod'): [(',', 2)],
    ('list', 'list'): [('NIL', 0), ('CONS', 2)],
    ('binary_ieee', 'float_compare'): [('LT', 0), ('EQ', 0), ('GT', 0), ('UN', 0)],
}


def mentions(name: str, text: str) -> bool:
    return re.search(r'(?<![A-Za-z0-9_\'.«])' + re.escape(name) + r'(?![A-Za-z0-9_\'»])', text) is not None


def unused(name: str, body: str) -> str:
    return name if mentions(name, body) or name.startswith('_') else '_' + name


def unused_pattern(pattern: str, body: str) -> str:
    return re.sub(r"[A-Za-z_][A-Za-z0-9_']*", lambda m: unused(m.group(), body), pattern)


def width_of_result(c: Const) -> int:
    w = word_width(fun_parts(c.ty)[1])
    if w is None:
        raise Unrenderable(f'{c.name} result width')
    return w


def width_of_arg(c: Const, i: int) -> int:
    w = word_width(fun_parts(c.ty)[0][i])
    if w is None:
        raise Unrenderable(f'{c.name} argument width')
    return w


def bin_op(op):
    return (2, lambda r, c, xs, raw: f'({xs[0]} {op} {xs[1]})')


def fn_app(name, arity):
    return (arity, lambda r, c, xs, raw: '(' + name + ''.join(' ' + x for x in xs) + ')')


def special_cond(r, c, args, env):
    def render(xs, raw):
        return f'(if {xs[0]} then {xs[1]} else {xs[2]})'
    return r.eta(c, args, env, 3, render)


def special_let(r, c, args, env):
    """`LET f e`: a `let` for a lambda (including a tuple `UNCURRY` lambda), else `f e`."""
    if len(args) >= 2:
        f, e = args[0], args[1]
        rest = args[2:]
        value = r.tm(e, env)
        out = None
        if isinstance(f, Lam):
            name, env2 = r.bind(f.v, env)
            body = r.tm(f.body, env2)
            out = f'(let {unused(name, body)} : {ty_lean(f.v.ty)} := {value}; {body})'
        else:
            pat = uncurry_pattern(r, f, env)
            if pat is not None:
                p, env2, body = pat
                body = r.tm(body, env2)
                out = f'(match {value} with | {unused_pattern(p, body)} => {body})'
        if out is not None:
            return out if not rest else '(' + out + ''.join(' ' + r.atom(a, env) for a in rest) + ')'
    return r.eta(c, args, env, 2, lambda xs, raw: f'({xs[0]} {xs[1]})')


def uncurry_pattern(r, f, env):
    """A nested `UNCURRY (λa. ...)` lambda as a tuple pattern, its environment and body."""
    h, args = strip_comb(f)
    if is_const(h, 'pair', 'UNCURRY') and len(args) == 1 and isinstance(args[0], Lam):
        lam = args[0]
        a, env2 = r.bind(lam.v, env)
        inner = lam.body
        if isinstance(inner, Lam):
            b, env3 = r.bind(inner.v, env2)
            return f'({a}, {b})', env3, inner.body
        sub = uncurry_pattern(r, inner, env2)
        if sub is not None:
            p, env3, body = sub
            return f'({a}, {p[1:-1]})', env3, body
    return None


def special_uncurry(r, c, args, env):
    if args and uncurry_pattern(r, Comb(c, args[0]), env) is not None:
        p, env2, body = uncurry_pattern(r, Comb(c, args[0]), env)
        dom = fun_parts(type_of(Comb(c, args[0])))[0][0]
        body = r.tm(body, env2)
        fn = f'(fun (pr : {ty_lean(dom)}) => match pr with | {unused_pattern(p, body)} => {body})'
        rest = args[1:]
        return fn if not rest else '(' + fn + ''.join(' ' + r.atom(a, env) for a in rest) + ')'
    return r.eta(c, args, env, 2, lambda xs, raw: f'({xs[0]} {xs[1]}.1 {xs[1]}.2)')


def special_literal_case(r, c, args, env):
    return r.eta(c, args, env, 2, lambda xs, raw: f'({xs[0]} {xs[1]})')


def special_n2w(r, c, args, env):
    w = width_of_result(c)
    def render(xs, raw):
        if raw[0] is not None:
            v = nat_literal(raw[0])
            if v is not None:
                return f'(BitVec.ofNat {w} {v})'
        return f'(BitVec.ofNat {w} {xs[0]})'
    return r.eta(c, args, env, 1, render)


def special_word_extract(r, c, args, env):
    w = width_of_result(c)
    return r.eta(c, args, env, 3,
                 lambda xs, raw: f'(holWordExtract {w} {xs[0]} {xs[1]} {xs[2]})')


def special_word_concat(r, c, args, env):
    w = width_of_result(c)
    return r.eta(c, args, env, 2, lambda xs, raw: f'(BitVec.setWidth {w} ({xs[0]} ++ {xs[1]}))')


def special_w2w(r, c, args, env):
    w = width_of_result(c)
    return r.eta(c, args, env, 1, lambda xs, raw: f'(BitVec.setWidth {w} {xs[0]})')


def special_sw2sw(r, c, args, env):
    w = width_of_result(c)
    return r.eta(c, args, env, 1, lambda xs, raw: f'(BitVec.signExtend {w} {xs[0]})')


def special_word_replicate(r, c, args, env):
    w = width_of_result(c)
    return r.eta(c, args, env, 2, lambda xs, raw: f'(holWordReplicate {w} {xs[0]} {xs[1]})')


def special_v2w(r, c, args, env):
    w = width_of_result(c)
    return r.eta(c, args, env, 1, lambda xs, raw: f'(holV2w {w} {xs[0]})')


def special_i2w(r, c, args, env):
    w = width_of_result(c)
    return r.eta(c, args, env, 1, lambda xs, raw: f'(BitVec.ofInt {w} {xs[0]})')


def special_int_to_fp(r, c, args, env):
    """Literal machine_ieeeLib int_to_fp at both fixed formats.

    Original real_of_int arguments are covered by Rat. Preserve every generic
    rounding clause/choice, rather than the executable binary64 RTE specialization.
    """
    r.noncomputable = True
    width = width_of_result(c)
    if width == 64:
        return r.eta(c, args, env, 2,
                     lambda xs, raw: f'(holIntToFp64 {xs[0]} {xs[1]})')
    if width != 32:
        raise Unrenderable('int_to_fp requires fixed binary32 or binary64')
    return r.eta(c, args, env, 2, lambda xs, raw:
        f'((fun (a : HolFloat 23 8) => '
        f'(a.sign ++ a.exponent ++ a.significand).cast (by decide)) '
        f'(holRealToFloat {xs[0]} ({xs[1]} : Rat)))')


def special_cross_format_fp(r, c, args, env):
    """Full original machine_ieee cross-format SND wrappers."""
    r.noncomputable = True
    if width_of_result(c) == 32:
        return r.eta(c, args, env, 2,
                     lambda xs, raw: f'(holFp64ToFp32 {xs[0]} {xs[1]})')
    if width_of_result(c) == 64:
        return r.eta(c, args, env, 1,
                     lambda xs, raw: f'(holFp32ToFp64 {xs[0]})')
    raise Unrenderable('cross-format conversion requires fixed binary32/binary64')


def special_binary_fp(operation):
    def render(r, c, args, env):
        r.noncomputable = True
        width = width_of_result(c)
        if width not in (32, 64):
            raise Unrenderable('binary FP requires fixed binary32/binary64')
        return r.eta(c, args, env, 3, lambda xs, raw:
            f'(holFloatToFp{width} (holFloat{operation} {xs[0]} '
            f'(holFp{width}ToFloat {xs[1]}) (holFp{width}ToFloat {xs[2]})).2)')
    return render


def special_sqrt_fp(r, c, args, env):
    r.noncomputable = True
    width = width_of_result(c)
    if width not in (32, 64):
        raise Unrenderable('FP square root requires fixed binary32/binary64')
    return r.eta(c, args, env, 2, lambda xs, raw:
        f'(holFloatToFp{width} (holFloatSqrt {xs[0]} '
        f'(holFp{width}ToFloat {xs[1]})).2)')


def special_bit_field_insert(r, c, args, env):
    # HOL raw FCP indexing is unspecified outside the input width. Unlike
    # word_bit, bit_field_insert does not add that bound itself. Every call
    # in the pinned model has literal bounds; require their source-side
    # guarantee before using the getLsbD-based helper.
    if len(args) < 3:
        raise Unrenderable('bit_field_insert requires checked literal bounds')
    high, low = nat_literal(args[0]), nat_literal(args[1])
    width = word_width(type_of(args[2]))
    if high is None or low is None or width is None or (low <= high and high - low >= width):
        raise Unrenderable('bit_field_insert input index may exceed word width')
    return r.eta(c, args, env, 4,
                 lambda xs, raw: f'(holBitFieldInsert {xs[0]} {xs[1]} {xs[2]} {xs[3]})')


def special_word_len(r, c, args, env):
    w = width_of_arg(c, 0)
    return r.eta(c, args, env, 1, lambda xs, raw: f'{w}')


def special_arb(r, c, args, env):
    r.noncomputable = True
    t = fun_parts(c.ty)[1] if args else c.ty
    base = f'(Flapjack.holArb {ty_lean(c.ty)})'
    return base if not args else '(' + base + ''.join(' ' + r.atom(a, env) for a in args) + ')'


def special_eq(r, c, args, env):
    return r.eta(c, args, env, 2, lambda xs, raw: f'({xs[0]} == {xs[1]})')


def special_chr(r, c, args, env):
    return r.eta(c, args, env, 1, lambda xs, raw: f'(BitVec.ofNat 8 {xs[0]})')


def special_int_of_num(r, c, args, env):
    return r.eta(c, args, env, 1, lambda xs, raw: f'(Int.ofNat {xs[0]})')


SPECIAL = {
    ('machine_ieee', 'fp32_sqrt'): special_sqrt_fp,
    ('machine_ieee', 'fp64_sqrt'): special_sqrt_fp,
    ('machine_ieee', 'fp32_add'): special_binary_fp('Add'),
    ('machine_ieee', 'fp32_sub'): special_binary_fp('Sub'),
    ('machine_ieee', 'fp32_mul'): special_binary_fp('Mul'),
    ('machine_ieee', 'fp32_div'): special_binary_fp('Div'),
    ('machine_ieee', 'fp64_add'): special_binary_fp('Add'),
    ('machine_ieee', 'fp64_sub'): special_binary_fp('Sub'),
    ('machine_ieee', 'fp64_mul'): special_binary_fp('Mul'),
    ('machine_ieee', 'fp64_div'): special_binary_fp('Div'),

    ('machine_ieee', 'fp64_to_fp32'): special_cross_format_fp,
    ('machine_ieee', 'fp32_to_fp64'): special_cross_format_fp,
    ('machine_ieee', 'int_to_fp32'): special_int_to_fp,
    ('machine_ieee', 'int_to_fp64'): special_int_to_fp,
    ('bool', 'COND'): special_cond,
    ('bool', 'LET'): special_let,
    ('bool', 'ARB'): special_arb,
    ('bool', 'literal_case'): special_literal_case,
    ('min', '='): special_eq,
    ('pair', 'UNCURRY'): special_uncurry,
    ('words', 'n2w'): special_n2w,
    ('words', 'w2w'): special_w2w,
    ('words', 'sw2sw'): special_sw2sw,
    ('words', 'word_extract'): special_word_extract,
    ('words', 'word_concat'): special_word_concat,
    ('words', 'word_replicate'): special_word_replicate,
    ('words', 'bit_field_insert'): special_bit_field_insert,
    ('words', 'word_len'): special_word_len,
    ('bitstring', 'v2w'): special_v2w,
    ('integer_word', 'i2w'): special_i2w,
    ('string', 'CHR'): special_chr,
    ('integer', 'int_of_num'): special_int_of_num,
}

def ieee_codec(x: str, t: int, w: int) -> str:
    """Literal machine_ieeeLib.mk_fp_to_float fixed-width field extraction.

    Generator arguments are (fp32,23,8) and (fp64,52,11); sign is at t+w,
    exponent occupies w bits starting at t, significand occupies t low bits.
    """
    return (f"({{ sign := {x}.extractLsb' {t+w} 1, "
            f"exponent := {x}.extractLsb' {t} {w}, "
            f"significand := {x}.extractLsb' 0 {t} }} : HolFloat {t} {w})")


def uses_ieee_real_rendering(text: str) -> bool:
    # These generic original operations reach float_value/float_to_real.
    # Their real carrier is the existing rational-cut translation; do not
    # conceal it when mapping the generated machine_ieee wrappers.
    return any(re.search(r'\b' + name + r'\b', text)
               for name in ('holFloatCompare', 'holFloatIsNan', 'holFloatToInt',
                            'holRealToFloat', 'holIntToFp64', 'holFp64ToFp32', 'holFp32ToFp64',
                            'holFloatAdd', 'holFloatSub', 'holFloatMul', 'holFloatDiv', 'holFloatSqrt'))


CONSTANTS = {
    ('binary_ieee', 'roundTiesToEven'): (0, lambda r, c, xs, raw: 'HolRounding.roundTiesToEven'),
    ('binary_ieee', 'roundTowardPositive'): (0, lambda r, c, xs, raw: 'HolRounding.roundTowardPositive'),
    ('binary_ieee', 'roundTowardNegative'): (0, lambda r, c, xs, raw: 'HolRounding.roundTowardNegative'),
    ('binary_ieee', 'roundTowardZero'): (0, lambda r, c, xs, raw: 'HolRounding.roundTowardZero'),
    ('one', 'one'): (0, lambda r, c, xs, raw: '()'),
    ('bool', 'T'): (0, lambda r, c, xs, raw: 'true'),
    ('bool', 'F'): (0, lambda r, c, xs, raw: 'false'),
    ('bool', '/\\'): bin_op('&&'),
    ('bool', '\\/'): bin_op('||'),
    ('bool', '~'): (1, lambda r, c, xs, raw: f'(!{xs[0]})'),
    ('pair', ','): (2, lambda r, c, xs, raw: f'({xs[0]}, {xs[1]})'),
    ('pair', 'FST'): (1, lambda r, c, xs, raw: f'{xs[0]}.1'),
    ('pair', 'SND'): (1, lambda r, c, xs, raw: f'{xs[0]}.2'),
    ('option', 'NONE'): (0, lambda r, c, xs, raw: f'(none : {ty_lean(c.ty)})'),
    ('option', 'SOME'): (1, lambda r, c, xs, raw: f'(some {xs[0]})'),
    ('option', 'IS_SOME'): (1, lambda r, c, xs, raw: f'{xs[0]}.isSome'),
    ('option', 'THE'): (1, lambda r, c, xs, raw: f'(holThe {xs[0]})'),
    ('list', 'NIL'): (0, lambda r, c, xs, raw: f'([] : {ty_lean(c.ty)})'),
    ('list', 'CONS'): bin_op('::'),
    ('list', 'APPEND'): bin_op('++'),
    ('combin', 'K'): (2, lambda r, c, xs, raw: xs[0]),
    ('combin', 'UPDATE'): (3, lambda r, c, xs, raw: f'(holUpdate {xs[0]} {xs[1]} {xs[2]})'),
    ('arithmetic', '+'): bin_op('+'),
    ('arithmetic', '-'): bin_op('-'),
    ('arithmetic', '*'): bin_op('*'),
    ('arithmetic', 'DIV'): bin_op('/'),
    ('arithmetic', 'EXP'): bin_op('^'),
    ('arithmetic', '>'): (2, lambda r, c, xs, raw: f'(decide ({xs[0]} > {xs[1]}))'),
    ('arithmetic', '<='): (2, lambda r, c, xs, raw: f'(decide ({xs[0]} ≤ {xs[1]}))'),
    ('prim_rec', '<'): (2, lambda r, c, xs, raw: f'(decide ({xs[0]} < {xs[1]}))'),
    ('integer', 'int_neg'): (1, lambda r, c, xs, raw: f'(-{xs[0]})'),
    ('integer', 'int_sub'): bin_op('-'),
    ('integer', 'int_lt'): (2, lambda r, c, xs, raw: f'(decide ({xs[0]} < {xs[1]}))'),
    ('integer', 'int_gt'): (2, lambda r, c, xs, raw: f'(decide ({xs[0]} > {xs[1]}))'),
    ('integer', 'int_exp'): (2, lambda r, c, xs, raw: f'({xs[0]} ^ {xs[1]})'),
    ('integer_word', 'w2i'): (1, lambda r, c, xs, raw: f'{xs[0]}.toInt'),
    ('words', 'w2n'): (1, lambda r, c, xs, raw: f'{xs[0]}.toNat'),
    ('words', 'word_add'): bin_op('+'),
    ('words', 'word_sub'): bin_op('-'),
    ('words', 'word_mul'): bin_op('*'),
    ('words', 'word_and'): bin_op('&&&'),
    ('words', 'word_or'): bin_op('|||'),
    ('words', 'word_xor'): bin_op('^^^'),
    ('words', 'word_1comp'): (1, lambda r, c, xs, raw: f'(~~~{xs[0]})'),
    ('words', 'word_2comp'): (1, lambda r, c, xs, raw: f'(-{xs[0]})'),
    ('words', 'word_lsl'): (2, lambda r, c, xs, raw: f'({xs[0]} <<< {xs[1]})'),
    ('words', 'word_lsr'): (2, lambda r, c, xs, raw: f'({xs[0]} >>> {xs[1]})'),
    ('words', 'word_asr'): (2, lambda r, c, xs, raw: f'(BitVec.sshiftRight {xs[0]} {xs[1]})'),
    ('words', 'word_lsl_bv'): (2, lambda r, c, xs, raw: f'({xs[0]} <<< {xs[1]}.toNat)'),
    ('words', 'word_lsr_bv'): (2, lambda r, c, xs, raw: f'({xs[0]} >>> {xs[1]}.toNat)'),
    ('words', 'word_asr_bv'): (2, lambda r, c, xs, raw: f'(BitVec.sshiftRight {xs[0]} {xs[1]}.toNat)'),
    ('words', 'word_bit'): (2, lambda r, c, xs, raw: f'({xs[1]}.getLsbD {xs[0]})'),
    ('words', 'word_lo'): (2, lambda r, c, xs, raw: f'(BitVec.ult {xs[0]} {xs[1]})'),
    ('words', 'word_hs'): (2, lambda r, c, xs, raw: f'(!(BitVec.ult {xs[0]} {xs[1]}))'),
    ('words', 'word_lt'): (2, lambda r, c, xs, raw: f'(BitVec.slt {xs[0]} {xs[1]})'),
    ('words', 'word_le'): (2, lambda r, c, xs, raw: f'(BitVec.sle {xs[0]} {xs[1]})'),
    ('words', 'word_ge'): (2, lambda r, c, xs, raw: f'(BitVec.sle {xs[1]} {xs[0]})'),
    ('words', 'word_div'): (2, lambda r, c, xs, raw: f'(BitVec.udiv {xs[0]} {xs[1]})'),
    ('words', 'word_mod'): (2, lambda r, c, xs, raw: f'(BitVec.umod {xs[0]} {xs[1]})'),
    ('words', 'word_quot'): (2, lambda r, c, xs, raw: f'(BitVec.sdiv {xs[0]} {xs[1]})'),
    ('words', 'word_rem'): (2, lambda r, c, xs, raw: f'(BitVec.srem {xs[0]} {xs[1]})'),
    ('words', 'word_min'): (2, lambda r, c, xs, raw: f'(if BitVec.ult {xs[0]} {xs[1]} then {xs[0]} else {xs[1]})'),
    ('words', 'word_max'): (2, lambda r, c, xs, raw: f'(if BitVec.ult {xs[0]} {xs[1]} then {xs[1]} else {xs[0]})'),
    ('words', 'word_smin'): (2, lambda r, c, xs, raw: f'(if BitVec.slt {xs[0]} {xs[1]} then {xs[0]} else {xs[1]})'),
    ('words', 'word_smax'): (2, lambda r, c, xs, raw: f'(if BitVec.slt {xs[0]} {xs[1]} then {xs[1]} else {xs[0]})'),
    ('words', 'word_to_hex_string'): (1, lambda r, c, xs, raw: f'(holWordToHexString {xs[0]})'),
    ('ASCIInumbers', 'num_to_dec_string'): (1, lambda r, c, xs, raw: f'(holNumToDecString {xs[0]})'),
    ('state_transformer', 'FOR'): (1, lambda r, c, xs, raw: f'(holFor {xs[0]})'),
}


for _width, _t, _w in ((32, 23, 8), (64, 52, 11)):
    # machine_ieeeLib.lift1b applies the fixed codec to literal field predicates.
    for _classification in ('Normal', 'Subnormal'):
        CONSTANTS['machine_ieee', f'fp{_width}_is{_classification}'] = (
            1, lambda r, c, xs, raw, t=_t, w=_w, classification=_classification:
            f'(holFloatIs{classification} {ieee_codec(xs[0], t, w)})')
    CONSTANTS['machine_ieee', f'fp{_width}_posZero'] = (
        0, lambda r, c, xs, raw, width=_width: f'(BitVec.ofNat {width} 0)')
    CONSTANTS['machine_ieee', f'fp{_width}_negZero'] = (
        0, lambda r, c, xs, raw, width=_width:
        f'(BitVec.ofNat {width} {1 << (width - 1)})')
    CONSTANTS['machine_ieee', f'fp{_width}_to_int'] = (
        2, lambda r, c, xs, raw, t=_t, w=_w:
        f'(holFloatToInt {xs[0]} {ieee_codec(xs[1], t, w)})')
    CONSTANTS['machine_ieee', f'fp{_width}_compare'] = (
        2, lambda r, c, xs, raw, t=_t, w=_w:
        f'(holFloatCompare {ieee_codec(xs[0], t, w)} {ieee_codec(xs[1], t, w)})')
    CONSTANTS['machine_ieee', f'fp{_width}_isNan'] = (
        1, lambda r, c, xs, raw, t=_t, w=_w:
        f'(holFloatIsNan {ieee_codec(xs[0], t, w)})')
    # float_plus_infinity has sign0, all-ones exponent, zero significand.
    CONSTANTS['machine_ieee', f'fp{_width}_posInf'] = (
        0, lambda r, c, xs, raw, width=_width, t=_t, w=_w:
        f'(BitVec.ofNat {width} {((1 << w) - 1) << t})')
    CONSTANTS['machine_ieee', f'fp{_width}_negInf'] = (
        0, lambda r, c, xs, raw, width=_width, t=_t, w=_w:
        f'(BitVec.ofNat {width} {(1 << (width - 1)) | (((1 << w) - 1) << t)})')
for _name in ('LT', 'EQ', 'GT', 'UN'):
    CONSTANTS['binary_ieee', _name] = (
        0, lambda r, c, xs, raw, name=_name: f'HolFloatCompare.{name.lower()}')


def render_def(r: Renderer, lean_name: str, term) -> tuple[str, bool]:
    """The Lean equations of one HOL definition theorem (a conjunction of clauses)."""
    clauses = []
    def conj(t):
        h, args = strip_comb(t)
        if is_const(h, 'bool', '/\\') and len(args) == 2:
            conj(args[0]); conj(args[1])
        else:
            clauses.append(t)
    conj(term)
    out = []
    recursive = False
    for cl in clauses:
        while True:
            h, args = strip_comb(cl)
            if is_const(h, 'bool', '!') and len(args) == 1 and isinstance(args[0], Lam):
                cl = args[0].body
            else:
                break
        h, args = strip_comb(cl)
        if not (is_const(h, 'min', '=') and len(args) == 2):
            raise Unrenderable('clause is not an equation')
        lhs, rhs = args
        f, params = strip_comb(lhs)
        out.append((f, params, rhs))
    if len(out) != 1:
        raise Unrenderable(f'{len(out)} clauses')
    f, params, rhs = out[0]
    env = {}
    binders = []
    matches = []
    for k, p in enumerate(params):
        if isinstance(p, Var):
            name, env = r.bind(p, env)
            binders.append(f'({name} : {ty_lean(p.ty)})')
            continue
        pat, env = tuple_pattern(r, p, env)
        name, env = r.bind(Var(f'arg{k}', p and type_of(p)), env)
        binders.append(f'({name} : {ty_lean(type_of(p))})')
        matches.append((name, pat))
    result_ty = ty_lean(type_of(lhs))
    body = r.tm(rhs, env)
    for name, pat in reversed(matches):
        body = f'match {name} with\n  | {unused_pattern(pat, body)} =>\n  {body}'
    binders = [re.sub(r'^\(([^ ]+) :', lambda m: '(' + unused(m.group(1), body) + ' :', b) for b in binders]
    recursive = isinstance(f, Const) and (f.thy, f.name) in r.defined and \
        re.search(r'(?<![A-Za-z0-9_.«])' + re.escape(r.defined[(f.thy, f.name)]) + r'(?![A-Za-z0-9_»])', body) is not None
    tvs = tyvars(type_of(lhs), [])
    for p in params:
        tyvars(type_of(p), tvs)
    tv_binders = ''.join(f'{{{tyvar_name(v)} : Type}} [Inhabited {tyvar_name(v)}] ' for v in tvs)
    head = f'def {lean_name} ' + tv_binders + ' '.join(binders) + f' : {result_ty} :=\n  {body}'
    return head, recursive


def constants_of(t):
    out = []
    stack = [t]
    while stack:
        x = stack.pop()
        if isinstance(x, Const):
            out.append(x)
        elif isinstance(x, Comb):
            stack += [x.f, x.x]
        elif isinstance(x, Lam):
            stack.append(x.body)
    return out


def tuple_pattern(r, p, env):
    """A HOL tuple of variables (a definition parameter) as a Lean tuple pattern."""
    h, args = strip_comb(p)
    if is_const(h, 'pair', ',') and len(args) == 2:
        a, env = tuple_pattern(r, args[0], env)
        b, env = tuple_pattern(r, args[1], env)
        return f'({a}, {b})', env
    if isinstance(p, Var):
        return r.bind(p, env)
    raise Unrenderable('non-variable parameter')


def main(argv):
    sexp_path, types_lean = argv[1], argv[2]
    data = read_sexps(Path(sexp_path).read_text())
    types = parse_types(Path(types_lean).read_text())
    defined = {}
    order = []
    for rec in data:
        _, thy, name, defname, term = rec
        lean = ident(name)
        defined[(thy, name)] = lean
        order.append((thy, name, defname, parse_tm(term)))
    roots = [arg.removeprefix('--roots=') for arg in argv[3:]
             if arg.startswith('--roots=')]
    if roots:
        if len(roots) != 1:
            raise ValueError('expected at most one --roots selection')
        selected = {tuple(root.split('$', 1)) for root in roots[0].split(',')}
        if not selected or not selected <= set(defined):
            raise ValueError('unknown or empty HOL root selection')
        terms = {(thy, name): term for thy, name, _, term in order}
        todo = list(selected)
        while todo:
            for c in constants_of(terms[todo.pop()]):
                dep = (c.thy, c.name)
                if dep in terms and dep not in selected:
                    selected.add(dep)
                    todo.append(dep)
        order = [rec for rec in order if rec[:2] in selected]
    emitted, failed = [], []
    bad = set()
    noncomp = set()
    generic_types = {}
    for thy, name, defname, term in order:
        try:
            generic_types[(thy, name)] = def_head_type(term)
        except Exception:
            pass
    for thy, name, defname, term in order:
        r = Renderer({k: v for k, v in defined.items()}, types)
        r.generic_types = generic_types
        deps = {(c.thy, c.name) for c in constants_of(term)} & set(defined)
        deps.discard((thy, name))
        blocked = sorted(f'{t}${n}' for t, n in deps if (t, n) in bad)
        if blocked:
            bad.add((thy, name))
            failed.append((thy, name, 'depends on unrendered ' + ', '.join(blocked)))
            continue
        try:
            text, rec = render_def(r, defined[(thy, name)], term)
            nc = r.noncomputable or 'holThe' in text or any(d in noncomp for d in deps)
            if nc:
                noncomp.add((thy, name))
            emitted.append((thy, name, defname, text, rec, nc))
        except Unrenderable as e:
            bad.add((thy, name))
            failed.append((thy, name, str(e)))
    return emitted, failed


def parse_types(text: str) -> dict:
    """Constructor names/arity and field names from the generated Types.lean."""
    types = {}
    for m in re.finditer(r'^inductive (\S+) where\n((?:  \|[^\n]*\n)+)', text, re.M):
        name = m.group(1).strip('«»')
        ctors, arity = [], []
        for line in m.group(2).splitlines():
            cm = re.match(r'\s*\|\s*(\S+)(.*)', line)
            ctors.append(cm.group(1).strip('«»'))
            arity.append(cm.group(2).count('(a'))
        types[name] = {'ctors': ctors, 'arity': arity}
    for m in re.finditer(r'^structure (\S+) where\n((?:  [^\n]*\n)+)', text, re.M):
        name = m.group(1).strip('«»')
        fields = [re.match(r'\s*(\S+) :', l).group(1).strip('«»') for l in m.group(2).splitlines() if ' : ' in l]
        types[name] = {'fields': fields}
    return types


if __name__ == '__main__':
    emitted, failed = main(sys.argv)
    paths = dict(arg.split('=', 1) for arg in sys.argv[3:]
                 if not arg.startswith('--roots='))
    for thy, name, defname, text, rec, nc in emitted:
        if re.fullmatch(r'boolify\d+', name):
            # Generated by bitstringLib.bitify_boolify from an L3 `BL` call: no source
            # declaration to cite, so the rendering is untagged infrastructure.
            print(f'/-- HOL `{thy}${name}` (`{defname}`), generated by `bitstringLib.bitify_boolify` '
                  f'for an L3 `BL` call (no source declaration); mechanically rendered from the '
                  f'elaborated HOL definition. Flapjack infrastructure, untagged. -/')
        else:
            note = (' Uses the original fixed binary32/binary64 field codecs and generic IEEE '
                    'value/comparison operations with `(reals_as_rational_cuts)` '
                    '(docs/SOUNDNESS.md item 8). Existing model dependency/body acceptance '
                    'remains open.' if uses_ieee_real_rendering(text) else '')
            print(f'/-- HOL `{thy}${name}` (`{defname}`), mechanically rendered from the elaborated HOL definition.{note} -/')
            qualifier = ' (reals_as_rational_cuts)' if uses_ieee_real_rendering(text) else ''
            print(f'@[hol "{paths[thy]}" "{defname}"{qualifier}]')
        print(('noncomputable ' if nc else '') + text)
        if (thy, name) == ('riscv', 'walk64'):
            print('termination_by arg0.2.2.2.2.2')
            print('decreasing_by simp_wf; simp_all only [beq_iff_eq]; omega')
        print()
    print(f'-- emitted {len(emitted)}, failed {len(failed)}', file=sys.stderr)
    for f in failed:
        print('-- FAILED', *f, file=sys.stderr)
