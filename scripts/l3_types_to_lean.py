"""Render the L3 Import Construct/Record declarations of an L3 model script as Lean.

Usage: scripts/l3_types_to_lean.py MODEL_SCRIPT HOL_PATH [DECL ...] [--beq-only NAME,...]

Prints, in source order, one tagged Lean `inductive` per `Construct` type and one tagged
`structure` per `Record`, with the type renderings documented in
`Flapjack/RiscV/L3/Types.lean`. With trailing DECL arguments, only the named declarations
are emitted (used for the ARM8 state carriers, which are a subset of the model's types).
`--beq-only` lists the declarations that derive `BEq` instead of `DecidableEq`, because Lean
cannot derive `DecidableEq` for their deeply nested payloads. The committed ARM8 carriers are
reproduced by

    scripts/l3_types_to_lean.py HOL/examples/l3-machine-code/arm8/model/arm8Script.sml \
        HOL/examples/l3-machine-code/arm8/model/arm8Script.sml ProcState ... arm8_state \
        --beq-only LoadStore,Data,instruction

`scripts/tests/test_hol_l3_types_to_lean.py` checks that the committed RISC-V carriers are
exactly the full output, that the ARM8 carriers are exactly the filtered output, and that the
CLI reproduces both. This is a mechanical transcription aid; it does not establish
HOL-to-Lean equivalence.
"""
import re, sys, runpy
from pathlib import Path


def render(text: str, HOLPATH: str, only: list[str] | None = None,
           beq_only: tuple[str, ...] = ()) -> str:
    decls = runpy.run_path(str(Path(__file__).with_name('hol_sml_declarations.py')))['l3_type_declarations'](text)
    lines = text.splitlines(keepends=True)
    KW = {'done','at','by','fun','have','show','from','let','in','if','then','else','do','match','with','end',
          'open','where','deriving','structure','inductive','instance','def','theorem','for','unless','return','try','catch','finally','mut','break','continue','Type','Prop','Sort','true','false','true','not','and','or','namespace','section','variable','universe','import','export','private','protected','partial','noncomputable','macro','syntax','notation','infix','set_option','attribute','local','scoped','calc','suffices','obtain','this','fun','λ','Option','List','Nat','Bool','String'}
    def ident(n):
        return '«'+n+'»' if (n in KW or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", n)) else n
    class P:
        def __init__(s,t): s.t=t; s.i=0
        def ws(s):
            while s.i<len(s.t) and s.t[s.i].isspace(): s.i+=1
        def peek(s,x): s.ws(); return s.t.startswith(x,s.i)
        def eat(s,x):
            s.ws()
            if not s.t.startswith(x,s.i): raise Exception('expected %r at %r'%(x,s.t[s.i:s.i+40]))
            s.i+=len(x)
        def name(s):
            s.ws(); m=re.compile(r"[A-Za-z_][A-Za-z0-9_']*").match(s.t,s.i); s.i=m.end(); return m.group()
        def string(s):
            s.eat('"'); j=s.t.index('"',s.i); r=s.t[s.i:j]; s.i=j+1; return r
        def num(s):
            s.ws(); m=re.compile(r"[0-9]+").match(s.t,s.i); s.i=m.end(); return int(m.group())
        def ty(s):
            n=s.name()
            simple={'bTy':'Bool','nTy':'Nat','sTy':'List HolChar','iTy':'Int','uTy':'Unit','cTy':'HolChar','vTy':'List Bool'}
            if n in simple: return simple[n]
            m=re.fullmatch(r'F(\d+)',n)
            if m: return '(BitVec %s)'%m.group(1)
            if n=='FTy': return '(BitVec %d)'%s.num()
            if n=='CTy': return ident(s.string())
            if n in ('PTy','ATy'):
                s.eat('('); a=s.ty(); s.eat(','); b=s.ty(); s.eat(')')
                return '(%s × %s)'%(a,b) if n=='PTy' else '(%s → %s)'%(a,b)
            if n in ('OTy','LTy','STy'):
                if s.peek('('):
                    s.eat('('); a=s.ty(); s.eat(')')
                else: a=s.ty()
                return {'OTy':'(Option %s)','LTy':'(List %s)','STy':'(%s → Bool)'}[n]%a
            raise Exception('unknown type '+n)
    out=[]
    for names, start, end in decls:
        body=''.join(lines[start-1:end])
        m=re.match(r'val\s+_\s*=\s*(Construct|Record)',body); kind=m.group(1)
        p=P(body[m.end():])
        if kind=='Record':
            p.eat('('); n=p.string(); p.eat(','); p.eat('[')
            fields=[]
            while not p.peek(']'):
                p.eat('('); f=p.string(); p.eat(','); t=p.ty(); p.eat(')'); fields.append((f,t))
                if p.peek(','): p.eat(',')
            out.append(('Record',n,fields,start))
        else:
            p.eat('[')
            while not p.peek(']'):
                p.eat('('); n=p.string(); p.eat(','); p.eat('[')
                cons=[]
                while not p.peek(']'):
                    p.eat('('); c=p.string(); p.eat(','); p.eat('['); args=[]
                    while not p.peek(']'):
                        args.append(p.ty())
                        if p.peek(','): p.eat(',')
                    p.eat(']'); p.eat(')'); cons.append((c,args))
                    if p.peek(','): p.eat(',')
                p.eat(']'); p.eat(')')
                out.append(('Construct',n,cons,start))
                if p.peek(','): p.eat(',')
    def hasfun(t): return '→' in t
    script = Path(HOLPATH).name
    res=[]
    seen=set()
    for kind,n,items,start in out:
        seen.add(n)
        if only is not None and n not in only:
            continue
        tag='@[hol "%s" "%s" %d]'%(HOLPATH,n,start) if False else '@[hol "%s" "%s"]'%(HOLPATH,n)
        if kind=='Record':
            fun=any(hasfun(t) for _,t in items)
            res.append('/-- HOL L3 record `%s` (`%s:%d`). -/\n%s\nstructure %s where\n'%(n,script,start,tag,ident(n)))
            for f,t in items: res.append('  %s : %s\n'%(ident(f),t))
            res.append('  deriving Inhabited\n\n' if fun else
                       ('  deriving BEq, Repr, Inhabited\n\n' if n in beq_only else
                        '  deriving DecidableEq, Repr, Inhabited\n\n'))
        else:
            fun=any(hasfun(t) for _,a in items for t in a)
            res.append('/-- HOL L3 datatype `%s` (`%s:%d`). -/\n%s\ninductive %s where\n'%(n,script,start,tag,ident(n)))
            for c,args in items:
                res.append('  | %s%s\n'%(ident(c),''.join(' (a%d : %s)'%(k,t) for k,t in enumerate(args))))
            res.append('  deriving Inhabited\n\n' if fun else
                       ('  deriving BEq, Repr, Inhabited\n\n' if n in beq_only else
                        '  deriving DecidableEq, Repr, Inhabited\n\n'))
    unknown=[n for n in (only or ()) if n not in seen]
    if unknown:
        raise ValueError('unknown declaration(s): ' + ', '.join(unknown))
    unknown=[n for n in beq_only if n not in seen]
    if unknown:
        raise ValueError('unknown --beq-only declaration(s): ' + ', '.join(unknown))
    return ''.join(res)


if __name__ == "__main__":
    args = sys.argv[1:]
    beq_only: tuple[str, ...] = ()
    positional: list[str] = []
    i = 0
    while i < len(args):
        a = args[i]
        if a == '--beq-only':
            if i + 1 >= len(args):
                raise SystemExit('--beq-only needs a comma-separated NAME list')
            beq_only = tuple(n for n in args[i + 1].split(',') if n)
            i += 2
        elif a.startswith('--beq-only='):
            beq_only = tuple(n for n in a.split('=', 1)[1].split(',') if n)
            i += 1
        else:
            positional.append(a)
            i += 1
    if len(positional) < 2:
        raise SystemExit('usage: l3_types_to_lean.py MODEL_SCRIPT HOL_PATH [DECL ...] '
                         '[--beq-only NAME,...]')
    try:
        print(render(Path(positional[0]).read_text(), positional[1],
                     positional[2:] or None, beq_only))
    except ValueError as exc:
        raise SystemExit(str(exc)) from None
