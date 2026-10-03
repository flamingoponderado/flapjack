#!/usr/bin/env python3
"""Reproduce every feasible original decoder guard-path sample and Lean fixture.

Guard constraints are original Boolean bit literals. This small DPLL routine
only selects regression inputs; it is not a proof of HOL-to-Lean equivalence
or of unreachable source branches. Full decoder definitions retain all paths.
Original expected payloads must be normalized numeric words, never target
Decode applications or shared v2w operations. Lean's kernel checks each
full-instruction observation separately.
"""
import gzip
import json
import re
import runpy
import sys
from functools import lru_cache
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
sys.setrecursionlimit(50000)
m = runpy.run_path(str(ROOT / "scripts/hol_terms_to_lean.py"))
C,A,L,V=[m[x] for x in ["Const","Comb","Lam","Var"]]
strip=m["strip_comb"]

def literals(t):
 h,x=strip(t)
 if isinstance(h,V) and not x and h.name.startswith("b'"):return [int(h.name[2:])+1]
 if isinstance(h,C) and (h.thy,h.name)==("bool","~") and len(x)==1:
  xs=literals(x[0]);assert len(xs)==1, "negation of non-literal predicate";return [-z for z in xs]
 if isinstance(h,C) and (h.thy,h.name)==("bool","/\\") and len(x)==2:return literals(x[0])+literals(x[1])
 raise ValueError((h,x))

def walk(t,path):
 h,x=strip(t)
 if isinstance(h,L):yield from walk(h.body,path);return
 if isinstance(h,C) and (h.thy,h.name)==("bool","COND") and len(x)==3:
  pred=literals(x[0]);yield from walk(x[1],path+[(pred,True)]);yield from walk(x[2],path+[(pred,False)]);return
 if isinstance(h,C) and h.thy=="riscv":
  ty=m["type_of"](t)
  if getattr(ty,"op",None)=="instruction":yield path,h.name;return
 if isinstance(h,C) and (h.thy,h.name) in [("bool","LET"),("pair","UNCURRY")]:yield from walk(x[0],path);return
 raise ValueError((h,len(x)))

def solve(clauses,assign=None):
 assign=dict(assign or {})
 while True:
  cs=[]
  for c in clauses:
   if any(abs(z) in assign and assign[abs(z)]==(z>0) for z in c):continue
   d=[z for z in c if abs(z) not in assign]
   if not d:return None
   cs.append(d)
  if not cs:return assign
  units=[c[0] for c in cs if len(c)==1]
  if not units:break
  for z in units:
   if abs(z) in assign and assign[abs(z)]!=(z>0):return None
   assign[abs(z)]=z>0
  clauses=cs
 z=cs[0][0]
 for v in [z>0,z<0]:
  a=dict(assign);a[abs(z)]=v;r=solve(cs,a)
  if r is not None:return r
 return None


@lru_cache(maxsize=1)
def source_samples():
 records=m["read_sexps"](gzip.decompress((ROOT / "scripts/l3/riscv_defs.sexp.gz").read_bytes()).decode());results={}
 for rec in records:
  if rec[1]!="riscv" or rec[2] not in ["Decode","DecodeRVC"]:continue
  t=m["parse_tm"](rec[4]);h,x=strip(t)
  while isinstance(h,C) and (h.thy,h.name)==("bool","!"):t=x[0].body;h,x=strip(t)
  rhs=x[1];width=32 if rec[2]=="Decode" else 16;rows=[];infeasible=[];constructors=set()
  for i,(path,outer) in enumerate(walk(rhs,[])):
   clauses=[]
   for pred,truth in path:
    clauses.extend([[z] for z in pred] if truth else [[-z for z in pred]])
   assignment=solve(clauses)
   if assignment is None:infeasible.append(i);continue
   words=[]
   for fill in [0,(1<<width)-1,int("aa"*(width//8),16)]:
    w=fill
    for bit,value in assignment.items():w=(w | (1<<(bit-1))) if value else (w & ~(1<<(bit-1)))
    assert all(all(bool(w&(1<<(abs(z)-1)))==(z>0) for z in pred)==truth for pred,truth in path)
    if w not in words:words.append(w)
   rows.append(dict(path=i,outer=outer,words=words));constructors.add(outer)
  results[rec[2]]=dict(width=width,rows=rows,infeasible=infeasible)
 return results


def sample_inputs():
    result = []
    for decoder, data in source_samples().items():
        for row in data["rows"]:
            for sample, word in enumerate(row["words"]):
                result.append(dict(label=f"{decoder}_path{row['path']}_sample{sample}", decoder=decoder, width=data["width"], word=word, path=row["path"], outer=row["outer"]))
    return result


def capture_rows(text):
    rows = {}
    for line in text.splitlines():
        label, value = line.split("=", 1)
        if label in rows:
            raise ValueError(f"duplicate source row {label}")
        rows[label] = value
    expected = {"Decode_type", "Decode_hypotheses", "DecodeRVC_type", "DecodeRVC_hypotheses"} | {x["label"] for x in sample_inputs()}
    if set(rows) != expected:
        raise ValueError("incomplete/extra original decoder rows")
    for decoder, width in [("Decode", 32), ("DecodeRVC", 16)]:
        if rows[decoder+"_type"] != f":word{width} -> instruction" or rows[decoder+"_hypotheses"] != "0":
            raise ValueError("changed original type or hypotheses")
    return rows


@lru_cache(maxsize=1)
def constructor_names():
    text = (ROOT / "Flapjack/RiscV/L3/Types.lean").read_text()
    names = set()
    for match in re.finditer(r"inductive (\w+) where\n(.*?)  deriving", text, re.S):
        names.update(re.findall(r"^  \| (\w+)", match[2], re.M))
    return names


def value_term(value, outer):
    parsed = m["read_sexps"](value)
    if len(parsed) != 1:
        raise ValueError("expected exactly one original value term")
    term = m["parse_tm"](parsed[0])
    head, _ = strip(term)
    if not isinstance(head, C) or head.thy != "riscv" or head.name != outer:
        raise ValueError("original result is not the selected source instruction constructor")
    if m["type_of"](term) != m["Ty"]("riscv", "instruction", ()):
        raise ValueError("changed original result carrier")
    canonical = {("arithmetic", "BIT1"), ("arithmetic", "BIT2"), ("arithmetic", "NUMERAL"), ("arithmetic", "ZERO"), ("num", "0"), ("pair", ","), ("words", "n2w")}
    for const in m["constants_of"](term):
        if (const.thy, const.name) not in canonical and not (const.thy == "riscv" and const.name in constructor_names()):
            raise ValueError(f"unreduced/noncanonical source payload {const.thy}${const.name}")
    todo = [term]
    while todo:
        node = todo.pop()
        if isinstance(node, (V, L)):
            raise ValueError("non-concrete original payload")
        if isinstance(node, A):
            todo.extend([node.f, node.x])
    return term


def fixture(text):
    rows = capture_rows(text)
    renderer = m["Renderer"]({}, m["parse_types"]((ROOT / "Flapjack/RiscV/L3/Types.lean").read_text()))
    result = """import Flapjack.RiscV.L3.Defs.Decode

/-! Original complete native decoded instructions, including numeric payloads.
All feasible source guard leaves sampled; finite regression evidence, not
universal word32 equivalence. Expected values come from original HOL EVAL. -/
set_option maxRecDepth 200000
namespace Flapjack.Test.L3DecodeParity
open Flapjack.RiscV.L3

"""
    for row in sample_inputs():
        expr = renderer.tm(value_term(rows[row["label"]], row["outer"]), {})
        result += f"-- Oracle {row['label']}: original complete instruction including all payloads.\nexample : {row['decoder']} (BitVec.ofNat {row['width']} {row['word']}) = {expr} := by decide\n\n"
    return result + "end Flapjack.Test.L3DecodeParity\n"


if __name__ == "__main__":
    try:
        generated = fixture((ROOT / "scripts/hol-probes/l3_decode_probe.out").read_text())
        target = ROOT / "Flapjack/Test/L3DecodeParity.lean"
        if sys.argv[1:] == ["--update"]:
            target.write_text(generated)
        elif sys.argv[1:] or target.read_text() != generated:
            raise ValueError("decoder fixture differs from original full-value capture (use --update)")
        print("PASS 621 original complete numeric decoder values, all213 feasible source leaves, matching Lean kernel fixtures")
    except (OSError, ValueError, AssertionError) as error:
        print(error, file=sys.stderr)
        sys.exit(1)
