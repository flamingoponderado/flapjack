#!/usr/bin/env python3
"""Generate a complete Lean word-program pattern from the pinned HOL capture."""
import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CASES = tuple(
    (ROOT / f"scripts/hol-probes/{name}_cake_word_probe.out",
     ROOT / f"Flapjack/Test/{title}CakeWordOracle.lean", f"{title}CakeWordOracle", 64)
    for name, title in (("empty", "Empty"), ("reference", "Reference"), ("match", "Match"))
) + ((ROOT / "scripts/hol-probes/byte_copy_word_probe.out",
      ROOT / "Flapjack/Test/ByteCopyWordOracle.lean", "ByteCopyWordOracle", 64),
     (ROOT / "scripts/hol-probes/from_list_word_probe.out",
      ROOT / "Flapjack/Test/FromListWordOracle.lean", "FromListWordOracle", 64),
     (ROOT / "scripts/hol-probes/append_word_probe.out",
      ROOT / "Flapjack/Test/AppendWordOracle.lean", "AppendWordOracle", 64),
     (ROOT / "scripts/hol-probes/install_xor_word_probe.out",
      ROOT / "Flapjack/Test/InstallXorWordOracle.lean", "InstallXorWordOracle", 64),
     (ROOT / "scripts/hol-probes/compare_equal_word_probe.out",
      ROOT / "Flapjack/Test/CompareEqualWordOracle.lean", "CompareEqualWordOracle", 64),
     (ROOT / "scripts/hol-probes/longdiv_word_probe.out",
      ROOT / "Flapjack/Test/LongDivWordOracle.lean", "LongDivWordOracle", 64),
     (ROOT / "scripts/hol-probes/any_arith_word_probe.out",
      ROOT / "Flapjack/Test/AnyArithWordOracle.lean", "AnyArithWordOracle", 64),
     (ROOT / "scripts/hol-probes/ref_byte_64_word_probe.out",
      ROOT / "Flapjack/Test/RefByte64WordOracle.lean", "RefByte64WordOracle", 64),
     (ROOT / "scripts/hol-probes/ref_byte_32_word_probe.out",
      ROOT / "Flapjack/Test/RefByte32WordOracle.lean", "RefByte32WordOracle", 32),
     (ROOT / "scripts/hol-probes/data_to_word_fp64_probe.out",
      ROOT / "Flapjack/Test/DataToWordFp64Oracle.lean", "DataToWordFp64Oracle", 64),
     (ROOT / "scripts/hol-probes/data_to_word_fp32_probe.out",
      ROOT / "Flapjack/Test/DataToWordFp32Oracle.lean", "DataToWordFp32Oracle", 32),
     (ROOT / "scripts/hol-probes/fixed_stubs_word_probe.out",
      ROOT / "Flapjack/Test/FixedStubsWordOracle.lean", "FixedStubsWordOracle", 64),
     (ROOT / "scripts/hol-probes/bignum_word_probe.out",
      ROOT / "Flapjack/Test/BignumWordOracle.lean", "BignumWordOracle", 64),
     (ROOT / "scripts/hol-probes/full_cake_word_probe.out",
      ROOT / "Flapjack/Test/FullCakeWordOracle.lean", "FullCakeWordOracle", 64),
     (ROOT / "scripts/hol-probes/full_inline_cake_word_probe.out",
      ROOT / "Flapjack/Test/FullInlineCakeWordOracle.lean", "FullInlineCakeWordOracle", 64),
     (ROOT / "scripts/hol-probes/full_mti_inline_cake_word_probe.out",
      ROOT / "Flapjack/Test/FullMtiInlineCakeWordOracle.lean", "FullMtiInlineCakeWordOracle", 64),
     (ROOT / "scripts/hol-probes/full_bvl_optimized_cake_word_probe.out",
      ROOT / "Flapjack/Test/FullBvlOptimizedCakeWordOracle.lean", "FullBvlOptimizedCakeWordOracle", 64),
     (ROOT / "scripts/hol-probes/full_clos_call_cake_word_probe.out",
      ROOT / "Flapjack/Test/FullClosCallCakeWordOracle.lean", "FullClosCallCakeWordOracle", 64),
     (ROOT / "scripts/hol-probes/full_clos_known_cake_word_probe.out",
      ROOT / "Flapjack/Test/FullClosKnownCakeWordOracle.lean", "FullClosKnownCakeWordOracle", 64),
     (ROOT / "scripts/hol-probes/full_default_frontend_word_probe.out",
      ROOT / "Flapjack/Test/FullDefaultFrontendWordOracle.lean", "FullDefaultFrontendWordOracle", 64),
     (ROOT / "scripts/hol-probes/mti_ops_word_probe.out",
      ROOT / "Flapjack/Test/MtiOpsWordOracle.lean", "MtiOpsWordOracle", 64),
     (ROOT / "scripts/hol-probes/tmc_ops_word_probe.out",
      ROOT / "Flapjack/Test/TmcOpsWordOracle.lean", "TmcOpsWordOracle", 64),
     (ROOT / "scripts/hol-probes/tmc_program_word_probe.out",
      ROOT / "Flapjack/Test/TmcProgramWordOracle.lean", "TmcProgramWordOracle", 64))
CONSTRUCTORS = {
    "Seq": (".seq", 2), "Assign": (".assign", 2), "Const": (".const", 1), "Load": (".load", 1),
    "If": (".ite", 5), "Test": (".test", 0), "NotTest": (".notTest", 0),
    "NotLess": (".notLess", 0), "NotEqual": (".notEqual", 0), "Equal": (".equal", 0), "Less": (".less", 0), "Imm": (".imm", 1),
    "Skip": (".skip", 0), "Alloc": (".alloc", 2), "Var": (".var", 1),
    "Lsr": (".lsr", 0), "Lsl": (".lsl", 0), "Asr": (".asr", 0), "Lower": (".lower", 0),
    "Op": (".op", 2), "Add": (".add", 0), "Sub": (".sub", 0), "Or": (".or", 0), "And": (".and", 0), "Xor": (".xor", 0),
    "Lookup": (".lookup", 1), "TriggerGC": (".triggerGC", 0),
    "NextFree": (".nextFree", 0), "CurrHeap": (".currHeap", 0), "EndOfHeap": (".endOfHeap", 0), "OtherHeap": (".otherHeap", 0),
    "Reg": (".reg", 1), "MustTerminate": (".mustTerminate", 1),
    "Call": (".call", 4), "SOME": ("some", 1), "NONE": ("none", 0),
    "Store": (".store", 2), "Set": (".set", 2), "Get": (".get", 2), "Globals": (".globals", 0), "Move": (".move", 2),
    "Inst": (".inst", 1), "Arith": (".arith", 1), "AddOverflow": (".addOverflow", 4),
    "SubOverflow": (".subOverflow", 4), "Mem": (".mem", 3), "Load8": (".load8", 0),
    "AddCarry": (".addCarry", 4), "LongDiv": (".longDiv", 5), "LongMul": (".longMul", 4), "Div": (".div", 3),
    "Store8": (".store8", 0), "Addr": (".addr", 2),
    "Install": (".install", 5), "CodeBufferWrite": (".codeBufferWrite", 2),
    "DataBufferWrite": (".dataBufferWrite", 2), "BitmapBuffer": (".bitmapBuffer", 0),
    "FP": (".fp", 1), "FPMovFromReg": (".fpMovFromReg", 3), "FPMovToReg": (".fpMovToReg", 3),
    "FPLess": (".fpLess", 3), "FPLessEqual": (".fpLessEqual", 3), "FPEqual": (".fpEqual", 3),
    "FPAdd": (".fpAdd", 3), "FPSub": (".fpSub", 3), "FPMul": (".fpMul", 3), "FPDiv": (".fpDiv", 3),
    "FPAbs": (".fpAbs", 2), "FPNeg": (".fpNeg", 2), "FPSqrt": (".fpSqrt", 2), "FPFma": (".fpFma", 3),
    "CodeBuffer": (".codeBuffer", 0),
    "GlobReal": (".globReal", 0), "Temp": (".temp", 1), "Return": (".return", 2), "LocValue": (".locValue", 2), "LN": (".ln", 0),
    "FALSE_CONST": ("(.const 2)", 0), "TRUE_CONST": ("(.const 18)", 0),
}


def parse_entries(input_path, fragments=None):
    raw = input_path.read_text().strip()
    if not raw.startswith("entry="):
        raise ValueError("missing HOL entry row")
    source = raw[6:]
    tokens = re.findall(r"-1w|0x[0-9A-Fa-f]+w|[0-9]+w|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[][(),;⦕⦖]", source)
    if "".join(tokens) != re.sub(r"\s+", "", source):
        raise ValueError("unexpected character in HOL output")
    pos = 0
    sets = []
    words = []

    def parse():
        nonlocal pos
        if pos >= len(tokens):
            raise ValueError("unexpected end of HOL output")
        token = tokens[pos]
        pos += 1
        if token == "-1w":
            name = f"word{len(words)}"
            words.append(name)
            return name
        if token.endswith("w") and (token[0].isdigit()):
            return str(int(token[:-1], 0) if token.startswith("0x") else int(token[:-1]))
        if token.isdigit():
            return token
        if token == "⦕":
            keys = []
            while tokens[pos] != "⦖":
                if not tokens[pos].isdigit():
                    raise ValueError("non-numeric live-set element")
                keys.append(tokens[pos])
                pos += 1
                if tokens[pos] == ";":
                    pos += 1
                elif tokens[pos] != "⦖":
                    raise ValueError("expected live-set separator")
            pos += 1
            name = f"live{len(sets)}"
            sets.append((name, keys))
            return name
        if token == "[":
            items = []
            while tokens[pos] != "]":
                items.append(parse())
                if tokens[pos] == ";":
                    pos += 1
                elif tokens[pos] != "]":
                    raise ValueError("expected list separator")
            pos += 1
            return "[" + ", ".join(items) + "]"
        if token == "(":
            items = [parse()]
            while tokens[pos] == ",":
                pos += 1
                items.append(parse())
            if tokens[pos] != ")":
                raise ValueError("expected closing parenthesis")
            pos += 1
            return "(" + ", ".join(items) + ")"
        if token == "ShiftN":
            op, exp, amount = parse(), parse(), parse()
            return f"(.shift {op} {exp} (.const {amount}))"
        if token == "Move0":
            return f"(.move 0 {parse()})"
        if token not in CONSTRUCTORS:
            raise ValueError(f"unsupported HOL constructor {token!r}")
        name, arity = CONSTRUCTORS[token]
        args = [parse() for _ in range(arity)]
        if token == "Seq" and fragments is not None:
            for index, arg in enumerate(args):
                if len(arg) > 1000:
                    fragment = f"fragment{len(fragments)}"
                    fragments.append((fragment, arg))
                    args[index] = fragment
        return "(" + " ".join([name, *args]) + ")" if args else name

    if tokens[pos] != "[":
        raise ValueError("expected a list of HOL functions")
    pos += 1
    entries = []
    while tokens[pos] != "]":
        set_start, word_start = len(sets), len(words)
        pattern = parse()
        entries.append((pattern, sets[set_start:], words[word_start:]))
        if tokens[pos] == ";":
            pos += 1
        elif tokens[pos] != "]":
            raise ValueError("expected function separator")
    pos += 1
    if pos != len(tokens):
        raise ValueError("trailing HOL output")
    return entries


def render_parts(input_path, namespace, width):
    fragments = []
    entries = parse_entries(input_path, fragments if namespace in ("BignumWordOracle", "FullCakeWordOracle", "FullInlineCakeWordOracle", "FullMtiInlineCakeWordOracle", "FullBvlOptimizedCakeWordOracle", "FullClosCallCakeWordOracle", "FullClosKnownCakeWordOracle", "FullDefaultFrontendWordOracle") else None)
    all_sets = {name: keys for _, sets, _ in entries for name, keys in sets}
    all_words = {name for _, _, words in entries for name in words}

    def pattern_checks(pattern):
        checks = []
        for name in dict.fromkeys(re.findall(r"\blive\d+\b", pattern)):
            checks.append(f"decide ({name} = Flapjack.sptListInsert [{', '.join(all_sets[name])}] .ln)")
        for name in dict.fromkeys(re.findall(r"\bword\d+\b", pattern)):
            if name not in all_words:
                raise ValueError("unknown word binder")
            checks.append(f"{name} == (-1 : BitVec {width})")
        for name in dict.fromkeys(re.findall(r"\bfragment\d+\b", pattern)):
            checks.append(f"matches_{name} {name}")
        return " &&\n      ".join(checks) or "true"

    fragment_defs = []
    for name, pattern in fragments:
        checks = pattern_checks(pattern)
        fragment_defs.append((f"matches_{name}", f'''private def matches_{name} (entry : Flapjack.WordLangProgHOL (BitVec {width})) : Bool :=
  match entry with
  | {pattern} =>
      {checks}
  | _ => false'''))
    match_defs = []
    for index, (pattern, _, _) in enumerate(entries):
        checks = pattern_checks(pattern)
        match_defs.append((f"matches{index}", f'''private def matches{index} (entry : Nat × Nat × (Flapjack.WordLangProgHOL (BitVec {width}) × Nat)) : Bool :=
  match entry with
  | {pattern} =>
      {checks}
  | _ => false'''))
    entry_names = ", ".join(f"entry{index}" for index in range(len(entries)))
    entry_checks = " &&\n      ".join(f"matches{index} entry{index}" for index in range(len(entries))) or "true"
    if len(entries) > 32:
        checks = " &&\n    ".join(
            f"(match code[{index}]? with | some entry => matches{index} entry | none => false)"
            for index in range(len(entries))
        )
        body = f"  code.length == {len(entries)} &&\n    {checks}"
    else:
        body = f"  match code with\n  | [{entry_names}] =>\n      {entry_checks}\n  | _ => false"
    return fragment_defs, match_defs, body


HELPER_NAME = re.compile(r"\b(matches_fragment\d+|matches\d+)\b")


def rewrite(text, mapping):
    return HELPER_NAME.sub(lambda m: mapping.get(m.group(0), m.group(0)), text)


def helper_defs(parts):
    return parts[0] + parts[1]


def assemble(namespace, width, definitions, body, shared):
    imports = "import Flapjack.Pancake.WordLang\n"
    head = ""
    if shared:
        imports += "import Flapjack.Test.CakeWordOracleHelpers\n"
        head = "open Flapjack.Test.CakeWordOracleHelpers\n\n"
    text = "\n\n".join(definition for _, definition in definitions)
    body_block = f"{text}\n\n" if text else ""
    return f'''-- Generated from the pinned original HOL compiler; do not edit.
{imports}
namespace Flapjack.Test.{namespace}

{head}{body_block}/-- Match every captured function, including every live set and next label. -/
def matchesCaptured (code : List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec {width}) × Nat))) : Bool :=
{body}

end Flapjack.Test.{namespace}
'''


def render(input_path, namespace, width):
    return assemble(namespace, width, helper_defs(render_parts(input_path, namespace, width)), render_parts(input_path, namespace, width)[2], False)


def share(parts_by_module):
    """Share helper definitions whose text and dependency closure are identical.

    Returns the canonical name of every shareable text, its occurrences, the
    per-module definitions and the first-occurrence order."""
    defs = {ns: helper_defs(parts) for ns, parts in parts_by_module.items()}
    bytext = {}
    order = []
    for ns in parts_by_module:
        for name, text in defs[ns]:
            if text not in bytext:
                bytext[text] = []
                order.append(text)
            bytext[text].append((ns, name))
    candidates = {text for text, occurrences in bytext.items() if len(occurrences) > 1}
    changed = True
    while changed:
        changed = False
        for text in list(candidates):
            modules = {ns for ns, _ in bytext[text]}
            ok = True
            for ref in set(HELPER_NAME.findall(text)):
                texts = set()
                for ns in modules:
                    found = [value for (name, value) in defs[ns] if name == ref]
                    if not found:
                        ok = False
                        break
                    texts.add(found[0])
                if not ok:
                    break
                if len(texts) != 1 or next(iter(texts)) not in candidates:
                    ok = False
                    break
            if not ok:
                candidates.discard(text)
                changed = True
    canonical = {}
    used = set()
    for text in order:
        if text not in candidates:
            continue
        base = "shared_" + bytext[text][0][1]
        name = base
        suffix = 2
        while name in used:
            name = f"{base}_{suffix}"
            suffix += 1
        used.add(name)
        canonical[text] = name
    return canonical, bytext, defs, order


def shared_module_render(canonical, bytext, defs, order):
    definitions = []
    for text in order:
        if text not in canonical:
            continue
        name = canonical[text]
        module, original = bytext[text][0]
        refs = {}
        for ref in set(HELPER_NAME.findall(text)) - {original}:
            ref_text = [value for (n, value) in defs[module] if n == ref][0]
            refs[ref] = canonical[ref_text]
        rewritten = text.replace(f"private def {original} ", f"def {name} ", 1)
        rewritten = rewrite(rewritten, refs)
        definitions.append((name, rewritten))
    return f'''-- Generated shared oracle helpers from the pinned original HOL compiler; do not edit.
import Flapjack.Pancake.WordLang

namespace Flapjack.Test.CakeWordOracleHelpers

{"\n\n".join(d for _, d in definitions)}

end Flapjack.Test.CakeWordOracleHelpers
'''


def module_with_sharing(namespace, width, parts, canonical, defs):
    mapping = {name: canonical[text] for name, text in defs[namespace] if text in canonical}
    definitions = [(name, rewrite(text, mapping)) for name, text in defs[namespace] if text not in canonical]
    body = rewrite(parts[2], mapping)
    return assemble(namespace, width, definitions, body, bool(mapping))


def normalize(text, namespace):
    """Erase the namespace so identical captures can share one generated module."""
    return text.replace(f"namespace Flapjack.Test.{namespace}", "namespace Flapjack.Test.<NS>").replace(
        f"end Flapjack.Test.{namespace}", "end Flapjack.Test.<NS>")


def alias_render(canonical, alias):
    return f'''-- Generated alias from the pinned original HOL compiler; do not edit.
-- This configuration's captured output is identical to `{canonical}`.
import Flapjack.Test.{canonical}

namespace Flapjack.Test.{alias}

/-- Alias of `{canonical}.matchesCaptured`; the captured output is identical. -/
abbrev matchesCaptured := Flapjack.Test.{canonical}.matchesCaptured

end Flapjack.Test.{alias}
'''


def expected_modules():
    """Group identical captures onto one module and share identical helper rows."""
    parts = {}
    widths = {}
    for input_path, _, namespace, width in CASES:
        parts[namespace] = render_parts(input_path, namespace, width)
        widths[namespace] = width
    canonical = {}
    for input_path, _, namespace, width in CASES:
        text = assemble(namespace, width, helper_defs(parts[namespace]), parts[namespace][2], False)
        canonical.setdefault(normalize(text, namespace), namespace)
    full = set(canonical.values())
    shared_names, bytext, defs, order = share({namespace: parts[namespace] for _, _, namespace, _ in CASES if namespace in full})
    plan = []
    if shared_names:
        plan.append((ROOT / "Flapjack/Test/CakeWordOracleHelpers.lean",
                     shared_module_render(shared_names, bytext, defs, order)))
    for _, output_path, namespace, width in CASES:
        text = assemble(namespace, width, helper_defs(parts[namespace]), parts[namespace][2], False)
        shared = canonical[normalize(text, namespace)]
        if shared != namespace:
            plan.append((output_path, alias_render(shared, namespace)))
        else:
            plan.append((output_path, module_with_sharing(namespace, width, parts[namespace], shared_names, defs)))
    return plan


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    plan = expected_modules()
    if args.check:
        for output_path, expected in plan:
            if not output_path.exists() or output_path.read_text() != expected:
                raise SystemExit(f"{output_path} is stale; regenerate it from the HOL capture")
            print(f"{output_path.name} matches the captured HOL output")
    else:
        for output_path, expected in plan:
            output_path.write_text(expected)


if __name__ == "__main__":
    main()
