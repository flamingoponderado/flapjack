#!/usr/bin/env python3
"""Generate the Lean ports of word_bignumProof's derive_corr_thm theorems.

HOL's derive_corr_thm saves, for each to_deep code constant NAME_code, a
theorem NAME_corr_thm relating the deep program to the shallow function NAME
through Corr. This script reads their untyped conclusions from the pinned
capture scripts/hol-probes/bignum_code_defs_probe.out, renders each statement
in Lean term by term, and emits a uniform proof script: non-recursive programs
are executed symbolically against the unfolded shallow definition; loops use
CorrSupport.corr_loop_of_step with the shallow step function. The statement
rendering is the part a reviewer compares against HOL; the proof scripts are
checked by Lean.
"""
import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CAPTURE = ROOT / "scripts/hol-probes/bignum_code_defs_probe.out"
OUT_DIR = ROOT / "Flapjack/Compiler/Backend/WordBignum/Proofs/Corr"
HOL_PATH = "cakeml/compiler/backend/proofs/word_bignumProofScript.sml"

ARRAYS = {"In1": ".in1", "In2": ".in2", "Out": ".out"}


def camel(hol):
    head, *rest = hol.split("_")
    return head + "".join(p[:1].upper() + p[1:] for p in rest)


def matching(text, i):
    """Index of the parenthesis closing the one at text[i]."""
    depth = 0
    for j in range(i, len(text)):
        if text[j] == "(":
            depth += 1
        elif text[j] == ")":
            depth -= 1
            if depth == 0:
                return j
    raise ValueError("unbalanced parentheses")


def strip_parens(text):
    text = text.strip()
    while text.startswith("(") and matching(text, 0) == len(text) - 1:
        text = text[1:-1].strip()
    return text


def split_top(text, sep):
    parts, depth, cur = [], 0, ""
    for ch in text:
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        if ch == sep and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    parts.append(cur)
    return [p.strip() for p in parts]


def render_atom(text):
    """Render a HOL value expression of the statements in Lean."""
    t = text
    t = re.sub(r"s\.regs⟨(\d+)⟩", r"(holFapply s.regs \1)", t)
    t = re.sub(r"s\.arrays (In1|In2|Out)", lambda m: f"(s.arrays {ARRAYS[m.group(1)]})", t)
    t = t.replace("s.clock − 1", "s.clock - 1")
    t = re.sub(r"\bmc_[a-z0-9_]+", lambda m: camel(m.group(0)), t)
    t = re.sub(r"\((\w+) \(", r"(\1 (", t)
    t = re.sub(r",(?! )", ", ", t)
    if "−" in t or "⟨" in t:
        raise ValueError(f"unrendered term {text}")
    return t


def parse_body(text):
    """delete_vars [ns] W, with W nested writes ending in s."""
    text = strip_parens(text)
    m = re.match(r"delete_vars \[([0-9; ]*)\] (.*)$", text, re.S)
    if not m:
        raise ValueError(f"unexpected body {text[:80]}")
    dels = [int(x) for x in m.group(1).replace(" ", "").split(";") if x]
    writes = []
    rest = strip_parens(m.group(2))
    while rest != "s":
        if rest.startswith("clock_write "):
            arg, rest = take_arg(rest[len("clock_write "):])
            writes.append(("clock", None, arg))
        elif rest.startswith("reg_write "):
            n, rest2 = rest[len("reg_write "):].split(" ", 1)
            arg, rest = take_arg(rest2)
            arg = strip_parens(arg)
            if not arg.startswith("SOME "):
                raise ValueError(f"unexpected register value {arg}")
            writes.append(("reg", int(n), arg[len("SOME "):]))
        elif rest.startswith("array_write "):
            a, rest2 = rest[len("array_write "):].split(" ", 1)
            arg, rest = take_arg(rest2)
            writes.append(("array", a, arg))
        else:
            raise ValueError(f"unexpected write {rest[:80]}")
        rest = strip_parens(rest)
    return dels, writes


def take_arg(text):
    text = text.strip()
    if text.startswith("("):
        j = matching(text, 0)
        return text[: j + 1], text[j + 1:].strip()
    arg, _, rest = text.partition(" ")
    return arg, rest.strip()


def render_writes(dels, writes, base):
    out = base
    for kind, key, value in reversed(writes):
        v = render_atom(strip_parens(value))
        v = f"({v})" if " " in v else v
        if kind == "clock":
            out = f"clockWrite {v} ({out})" if out != base else f"clockWrite {v} {base}"
        elif kind == "reg":
            out = f"regWrite {key} (some {v}) ({out})" if out != base else f"regWrite {key} (some {v}) {base}"
        else:
            out = (f"arrayWrite {ARRAYS[key]} {v} ({out})" if out != base
                   else f"arrayWrite {ARRAYS[key]} {v} {base}")
    return f"deleteVars [{', '.join(map(str, dels))}] ({out})" if out != base else f"deleteVars [{', '.join(map(str, dels))}] {base}"


def parse_statement(name, text):
    m = re.match(r"Corr (mc_[a-z0-9_]+_code) s \(INR (.*)\) (\(.*\)|[^()].*)$", text, re.S)
    head = f"Corr {name[:-len('_corr_thm')]}_code s (INR "
    if not text.startswith(head):
        raise ValueError(f"{name}: unexpected head")
    j = text.index("(INR ")
    k = matching(text, j)
    result = text[j + len("(INR "):k].strip()
    guard = text[k + 1:].strip()
    info = {"code": name[: -len("_corr_thm")] + "_code"}
    result = strip_parens(result)
    if result.startswith("(λ("):
        lam_end = matching(result, 0)
        lam = result[1:lam_end]
        call = strip_parens(result[lam_end + 1:])
        mm = re.match(r"λ\(([^)]*)\)\. (.*)$", lam, re.S)
        outs = [v.strip() for v in mm.group(1).split(",")]
        dels, writes = parse_body(mm.group(2))
        fm = re.match(r"(mc_[a-z0-9_]+) (.*)$", call, re.S)
        func, args = fm.group(1), strip_parens(fm.group(2))
        info.update(kind="tuple", outs=outs, dels=dels, writes=writes, func=func,
                    args=split_top(args, ","))
        body = render_writes(dels, writes, "s")
        lean_result = (f"match {camel(func)} ({', '.join(render_atom(a) for a in info['args'])}) with\n"
                       f"          | ({', '.join(outs)}) =>\n            {body}")
    else:
        dels, writes = parse_body(result)
        info.update(kind="single", dels=dels, writes=writes)
        lean_result = render_writes(dels, writes, "s")
    info["result"] = lean_result
    info["guard"] = render_guard(guard)
    info["guard_hol"] = guard
    return info


def render_guard(guard):
    g = guard
    g = re.sub(r"(\d+) ∈ FDOM s\.regs", r"\1 ∈ s.regs.dom", g)
    return render_atom(g)



def input_binders(args):
    """Fresh binder names for a step input tuple, with their state source."""
    names = []
    for idx, a in enumerate(args):
        a = a.strip()
        m = re.match(r"s\.regs⟨(\d+)⟩$", a)
        if a in ("s.clock − 1", "s.clock"):
            names.append(("in_l", "clock", None))
        elif m:
            names.append((f"in_r{m.group(1)}", "reg", int(m.group(1))))
        elif re.match(r"s\.arrays (In1|In2|Out)$", a):
            arr = a.split()[1]
            names.append((f"in_{arr.lower()}", "array", arr))
        else:
            raise ValueError(f"unexpected input {a}")
    return names


def encode(binders, base):
    out = base
    for name, kind, key in reversed(binders):
        if kind == "clock":
            out = f"clockWrite {name} ({out})"
        elif kind == "reg":
            out = f"regWrite {key} (some {name}) ({out})"
        else:
            out = f"arrayWrite {ARRAYS[key]} {name} ({out})"
    return out


def guard_doms(guard_hol):
    return [int(n) for n in re.findall(r"(\d+) ∈ FDOM s\.regs", guard_hol)]


def callee_step(callee, infos):
    info = infos[callee + "_corr_thm"]
    func = camel(info["func"]) if info["kind"] == "tuple" else None
    lemma = f"{callee}_corr_thm"
    if info["kind"] == "tuple":
        pat = ", ".join(f"o{i}" for i in range(len(info["outs"])))
        return (f"((refine ev_seq_corr ({lemma} (width := width) _) ?_ ?_ <;> try corr_side); (try corr_simp); "
                f"generalize_app {func} as res; obtain ⟨{pat}⟩ := res)")
    fname = re.search(r"\b(mc_[a-z0-9_]+) ", info_single_func(info)).group(1)
    return (f"((refine ev_seq_corr ({lemma} (width := width) _) ?_ ?_ <;> try corr_side); (try corr_simp); "
            f"generalize_app {camel(fname)} as res)")


def info_single_func(info):
    return " ".join(v for _k, _n, v in info["writes"]) + " "


def emit_theorem(name, info, code_rhs, infos):
    code = info["code"]
    callees = sorted(set(re.findall(r"mc_[a-z0-9_]+_code", code_rhs)))
    steps = [callee_step(c[: -len("_code")], infos) for c in callees]
    extra = " | ".join(steps) if steps else "fail"
    exec_tac = f"corr_exec_with (first | {extra})" if steps else "corr_exec"
    doms = guard_doms(info["guard_hol"])
    lean_name = name
    stmt = (f"theorem {lean_name} {{width : Nat}} [NeZero width] (s : MiniState width) :\n"
            f"    Corr ({camel(code)} width) s\n"
            f"      (.inr ({info['result']}))\n"
            f"      {info['guard']} := by\n")
    loop = re.match(r"Loop F \[([0-9; ]*)\] ", code_rhs)
    if loop:
        vs = [int(x) for x in loop.group(1).replace(" ", "").split(";") if x]
        binders = input_binders(info["args"])
        func = camel(info["func"])
        base = f"deleteVars [{', '.join(map(str, vs))}] (decClock s)"
        enc = encode(binders, base)
        outs = ", ".join(info["outs"])
        body = info["result"].split("=>", 1)[1].strip()
        x0 = "(" + ", ".join(render_atom(a) for a in info["args"]) + ")"
        inpat = ", ".join(b[0] for b in binders)
        dompat = ", ".join(f"d{n}" for n in doms)
        lookups = "\n".join(f"    have l{n} := lookup_of_dom d{n}" for n in doms)
        proof = (f"  refine corr_loop_of_step _ [{', '.join(map(str, vs))}] s {func}Step\n"
                 f"    (fun x => match x with | ({inpat}) => {enc})\n"
                 f"    (fun y => match y with | ({outs}) => {body})\n"
                 f"    ?_ {x0} _ rfl _ ?_\n"
                 f"  · rintro ⟨{inpat}⟩ hc\n"
                 f"    simp only [{func}Step] at hc ⊢\n"
                 f"    (try split_ifs at hc ⊢) <;> (try dsimp only at hc ⊢) <;> {exec_tac}\n"
                 f"  · rintro ⟨⟨{dompat}, hpre⟩, hcl⟩\n"
                 f"    refine ⟨hpre, hcl, ?_⟩\n"
                 f"{lookups}\n"
                 f"    corr_state_eq\n")
    else:
        func = camel(info["func"]) if info["kind"] == "tuple" else camel(
            re.search(r"\b(mc_[a-z0-9_]+) ", info_single_func(info)).group(1))
        dompat = ", ".join(f"d{n}" for n in doms)
        lookups = "\n".join(f"  have l{n} := lookup_of_dom d{n}" for n in doms)
        proof = (f"  rintro ⟨{dompat}, hpre⟩\n"
                 f"{lookups}\n"
                 f"  rw [{func}_def]\n"
                 f"  rw [{func}Pre_def] at hpre\n"
                 f"  simp only [{camel(code)}]\n"
                 f"  (try split_ifs at hpre ⊢) <;> (try dsimp only at hpre ⊢) <;> {exec_tac}\n")
    doc = (f"/-- HOL `{name}`, saved by `derive_corr_thm` for `{code}`: the deep\n"
           f"program computes the shallow `{code[:-len('_code')]}`. -/\n")
    tag = (f"@[hol \"{HOL_PATH}\" \"{name}\"\n"
           f"  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]\n")
    return doc + tag + stmt + proof


def render_module(names, rows, module, imports):
    infos = {label: parse_statement(label, text) for label, text in rows.items()
             if label.endswith("_corr_thm")}
    blocks = []
    for name in names:
        code = infos[name]["code"]
        blocks.append(emit_theorem(name, infos[name], rows[code + "_def"], infos))
    imps = "\n".join(f"public import {m}" for m in imports)
    return f'''-- Generated by scripts/generate-bignum-corr.py from
-- scripts/hol-probes/bignum_code_defs_probe.out; do not edit.
module

{imps}

@[expose] public section

/-! Ports of `word_bignumProof`'s `derive_corr_thm` theorems (see
`scripts/generate-bignum-corr.py`). -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Flapjack.Compiler.Backend.WordBignum

open Flapjack
open Flapjack.Misc.Multiword
open Flapjack.Compiler.Backend.WordBignum.CorrSupport

namespace {module}Witness

/-- Same-module canonical finite-support witness for the `regs` field named by
the theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {{width : Nat}} [NeZero width] :
    (∀ s : MiniStateBroad width, (MiniState.ofBroad s).toBroad = s) ∧
      (∀ s : MiniState width, MiniState.ofBroad s.toBroad = s) :=
  Flapjack.Compiler.Backend.WordBignum.holFmapAsFiniteSupportWitness

end {module}Witness

{chr(10).join(blocks)}
end Flapjack.Compiler.Backend.WordBignum
'''


GROUPS = [
    ("Compare", ("mc_cmp", "mc_compare")),
    ("Div", ("mc_idiv",)),
    ("AddSub", ("mc_iadd",)),
    ("Mul", ("mc_imul",)),
    ("Iop", ("mc_iop",)),
]
BASE_IMPORTS = [
    "Flapjack.Compiler.Backend.WordBignum.Proofs.CorrTactic",
    "Flapjack.Compiler.Backend.WordBignum.GeneratedMini",
    "Flapjack.Misc.Multiword.Mc.Basics",
]


def plan(rows):
    """Group the corr theorems by the top-level to_deep call that created
    their code constant, ordered so that callees come first."""
    deps = {k[: -len("_def")]: set(re.findall(r"mc_[a-z0-9_]+_code", v))
            for k, v in rows.items() if k.endswith("_code_def")}
    corr = {k[: -len("_corr_thm")] + "_code" for k in rows if k.endswith("_corr_thm")}
    seen, modules = set(), []
    for module, roots in GROUPS:
        order = []

        def visit(c):
            if c in seen:
                return
            seen.add(c)
            for d in sorted(deps[c]):
                visit(d)
            if c in corr:
                order.append(c[: -len("_code")] + "_corr_thm")

        for root in roots:
            visit(root + "_code")
        modules.append((module, order))
    missing = corr - {n[: -len("_corr_thm")] + "_code" for _m, o in modules for n in o}
    if missing:
        raise ValueError(f"corr theorems outside every group: {sorted(missing)}")
    return modules


def write_all(check):
    rows = dict(line.split("=", 1) for line in CAPTURE.read_text().splitlines())
    imports = list(BASE_IMPORTS)
    stale = []
    for module, names in plan(rows):
        path = OUT_DIR / f"{module}.lean"
        text = render_module(names, rows, module, imports)
        if check:
            if not path.exists() or path.read_text() != text:
                stale.append(str(path))
        else:
            OUT_DIR.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        imports = imports + [f"Flapjack.Compiler.Backend.WordBignum.Proofs.Corr.{module}"]
    if stale:
        raise SystemExit("stale generated corr modules: " + ", ".join(stale))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("names", nargs="*")
    parser.add_argument("--emit", metavar="OUT")
    parser.add_argument("--module", default="Corr")
    parser.add_argument("--imports", default="")
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.write or args.check:
        write_all(args.check)
        return
    if args.emit:
        rows = dict(line.split("=", 1) for line in CAPTURE.read_text().splitlines())
        imports = [m for m in args.imports.split(",") if m]
        Path(args.emit).write_text(render_module(args.names, rows, args.module, imports))
        return
    rows = dict(line.split("=", 1) for line in CAPTURE.read_text().splitlines())
    for label, text in rows.items():
        if not label.endswith("_corr_thm"):
            continue
        if args.names and label not in args.names:
            continue
        info = parse_statement(label, text)
        print(label, info["kind"], "|", info["result"][:200].replace("\n", " "), "|", info["guard"][:200])


if __name__ == "__main__":
    main()
