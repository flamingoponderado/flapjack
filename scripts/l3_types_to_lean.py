"""Render the L3 Import Construct/Record declarations of an L3 model script as Lean.

Usage: scripts/l3_types_to_lean.py MODEL_SCRIPT HOL_PATH [RESTRICTION_JSON]

Prints, in source order, one tagged Lean `inductive` per `Construct` type and one tagged
`structure` per `Record`, with the type renderings documented in
`Flapjack/RiscV/L3/Types.lean`. `scripts/tests/test_hol_l3_types_to_lean.py` checks that the
committed RISC-V carriers are exactly this output. This is a mechanical transcription aid;
it does not establish HOL-to-Lean equivalence.

With a restriction (the riscv-mi `scripts/l3/riscv-mi-restriction.json` `types`
section), whole types, constructors and record fields named there are omitted and the
reduced types, plus any explicitly listed additional types, are emitted without their
`@[hol]` tag. Every named entry must exist in the model script; a reduced type that is
not listed as untagged is rejected.
"""
import re, sys, runpy
from pathlib import Path


def render(text: str, HOLPATH: str, restriction: dict | None = None) -> str:
    decls = runpy.run_path(str(Path(__file__).with_name('hol_sml_declarations.py')))['l3_type_declarations'](text)
    lines = text.splitlines(keepends=True)
    KW = {'done','at','by','fun','have','show','from','let','in','if','then','else','do','match','with','end',
          'open','where','deriving','structure','inductive','instance','def','theorem','for','unless','return','try','catch','finally','mut','break','continue','Type','Prop','Sort','true','false','true','not','and','or','namespace','section','variable','universe','import','export','private','protected','partial','noncomputable','macro','syntax','notation','infix','set_option','attribute','local','scoped','calc','suffices','obtain','this','fun','λ','Option','List','Nat','Bool','String'}
    def ident(n):
        return '«'+n+'»' if (n in KW or "'" in n) else n
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
    if restriction is not None:
        out=restrict(out, restriction)
    untagged=set() if restriction is None else set(restriction['untagged'])
    def hasfun(t): return '→' in t
    res=[]
    for kind,n,items,start in out:
        tag='@[hol "%s" "%s" %d]'%(HOLPATH,n,start) if False else '@[hol "%s" "%s"]'%(HOLPATH,n)
        if n in untagged:
            tag=None
        if kind=='Record':
            fun=any(hasfun(t) for _,t in items)
            res.append('/-- HOL L3 record `%s` (`riscvScript.sml:%d`). -/\n%sstructure %s where\n'%(n,start,tag+'\n' if tag else '',ident(n)))
            for f,t in items: res.append('  %s : %s\n'%(ident(f),t))
            res.append('  deriving Inhabited\n\n' if fun else '  deriving DecidableEq, Repr, Inhabited\n\n')
        else:
            fun=any(hasfun(t) for _,a in items for t in a)
            res.append('/-- HOL L3 datatype `%s` (`riscvScript.sml:%d`). -/\n%sinductive %s where\n'%(n,start,tag+'\n' if tag else '',ident(n)))
            for c,args in items:
                res.append('  | %s%s\n'%(ident(c),''.join(' (a%d : %s)'%(k,t) for k,t in enumerate(args))))
            res.append('  deriving Inhabited\n\n' if fun else '  deriving DecidableEq, Repr, Inhabited\n\n')
    return ''.join(res)


def restrict(out, restriction):
    """Apply a fail-closed type restriction to parsed declarations."""
    keys={'removed','removed_constructors','removed_fields','untagged','review_note'}
    if set(restriction)!=keys:
        raise ValueError('type restriction keys: '+repr(sorted(set(restriction)^keys)))
    kinds={n:kind for kind,n,_,_ in out}
    items={n:[i for i,_ in its] for _,n,its,_ in out}
    removed=set(restriction['removed'])
    ctors=restriction['removed_constructors']
    fields=restriction['removed_fields']
    untagged=set(restriction['untagged'])
    for n in removed|set(ctors)|set(fields)|untagged:
        if n not in kinds:
            raise ValueError('restriction names unknown L3 type: '+n)
    for table,kind in ((ctors,'Construct'),(fields,'Record')):
        for n,names in table.items():
            if kinds[n]!=kind or n in removed or not names or len(set(names))!=len(names):
                raise ValueError('invalid restriction entry: '+n)
            if not set(names)<set(items[n]):
                raise ValueError('restriction removes unknown or all members of '+n)
    if removed&untagged:
        raise ValueError('removed type listed as untagged')
    if not (set(ctors)|set(fields))<=untagged:
        raise ValueError('reduced type keeps its exact @[hol] tag: '+repr(sorted((set(ctors)|set(fields))-untagged)))
    result=[]
    for kind,n,its,start in out:
        if n in removed:
            continue
        drop=set(ctors.get(n,[]))|set(fields.get(n,[]))
        result.append((kind,n,[i for i in its if i[0] not in drop],start))
    return result


if __name__ == "__main__":
    import json
    restriction=json.loads(Path(sys.argv[3]).read_text())['types'] if len(sys.argv)>3 else None
    print(render(Path(sys.argv[1]).read_text(), sys.argv[2], restriction))
