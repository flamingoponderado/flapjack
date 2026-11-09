"""Fail-closed shape checks for the closure-annotation list-relation witness.

This is a prerequisite for a representation qualifier, not an authorization
to tag a declaration. The caller must strip Lean comments before invoking it;
source review and the Lean kernel remain responsible for correspondence and
proof checking. Only the currently reviewed relation shape is recognized.
The checker does not validate all ValueRel or EnvOk premises, resolve imported
names, check proof dependencies, or authorize a tag. Those checks and source
review are required before wiring this into an attribute gate.
"""

import re


def _compact(text: str) -> str:
    return re.sub(r"\s+", "", text)


def nested_relation_errors(source: str) -> list[str]:
    """Check the concrete FunctionsRel factoring and its unconditional witness."""
    errors = []
    blocks = list(re.finditer(r"(?ms)^mutual\s*$.*?^end\s*$", source))
    blocks = [m.group() for m in blocks if re.search(r"\binductive\s+ValueRel\b", m.group())]
    if len(blocks) != 1:
        return ["expected one mutual block containing ValueRel"]
    block = blocks[0]
    names = re.findall(r"(?m)^inductive\s+(\w+)", block)
    if names != ["ValueRel", "FunctionsRel", "EnvOk"]:
        errors.append("the three relation inductives must share one mutual block")
    aux = re.search(r"(?ms)^inductive\s+FunctionsRel\b(.*?)(?=^inductive\s+EnvOk\b)", block)
    if not aux:
        return errors + ["missing auxiliary relation"]
    aux_text = aux.group()
    if re.findall(r"(?m)^\s*\|\s*(\w+)", aux_text) != ["nil", "cons"]:
        errors.append("auxiliary relation must have exactly nil and cons constructors")
    nil_match = re.search(r"(?ms)^\s*\|\s*nil\b(.*?)(?=^\s*\|\s*cons\b)", aux_text)
    aux_compact = _compact(aux_text)
    expected_type = (
        "inductiveFunctionsRel:ListValue→ListValue→Nat→"
        "List(Nat×ClosLang.Exp)→List(Nat×ClosLang.Exp)→Propwhere"
    )
    if not aux_compact.startswith(expected_type):
        errors.append("unexpected auxiliary relation parameters or list indices")
    nil = "|nil(envnextEnv:ListValue)(count:Nat):FunctionsRelenvnextEnvcount[][]"
    tail = "FunctionsRelenvnextEnvcountfunctionsnextFunctions→"
    cons = ("FunctionsRelenvnextEnvcount((arity,body)::functions)"
            "((arity,nextBody)::nextFunctions)")
    if (not nil_match or _compact("| nil" + nil_match.group(1)) != nil or
            tail + cons not in aux_compact or
            not aux_compact.endswith(cons)):
        errors.append("auxiliary constructors must preserve parameters and unroll both lists")
    if len(re.findall(r"\bFunctionsRel\b", aux_text)) != 4:
        errors.append("unexpected auxiliary recursion or occurrence")
    if len(re.findall(r"\bFunctionsRel\b", block)) != 5:
        errors.append("unexpected auxiliary use in the mutual block")
    value_part = block[:aux.start()]
    env_part = block[aux.end():]
    if re.findall(r"(?m)^\s*\|\s*(\w+)", value_part) != [
        "number", "word64", "block", "byteVector", "refPtr", "closure", "recclosure"
    ]:
        errors.append("ValueRel must have the reviewed constructor list")
    if re.findall(r"(?m)^\s*\|\s*(\w+)", env_part) != ["outside", "local", "captured"]:
        errors.append("EnvOk must have the reviewed constructor list")
    value_compact = _compact(value_part)
    env_compact = _compact(env_part)
    if "|number(value:Int):ValueRel(.numbervalue)(.numbervalue)" not in value_compact:
        errors.append("the number constructor must relate identical numbers")
    if "everyFnVarsNone[body]→env.length=m→" not in _compact(value_part):
        errors.append("the closure must retain the source safety and length premises")
    if "shiftSource(altFreeSource[body]).1marityindex=[nextBody]→" not in value_compact:
        errors.append("the closure must retain the source shift premise")
    if "List.Forall₂ValueRelargsnextArgs→index<functions.length→" not in value_compact:
        errors.append("the recursive closure must retain the index bound")
    if "l+m≤n→EnvOkmlindexenvnextEnvn" not in env_compact:
        errors.append("the outside environment rule must retain its bound")
    if (env_compact.count("ValueRel(@Flapjack.holElValue⟨unitValue⟩nenv)") != 2):
        errors.append("the two tracked environment rules must relate source values")
    if "l≤n→n<l+m→n<l+m→sptLookup" not in env_compact:
        errors.append("the captured environment rule must retain both bounds")
    for name in ("Value", "Exp", "Spt", "shiftSource", "altFreeSource", "altFvSource",
                 "everyFnVarsNone"):
        if re.search(rf"(?m)^\s*(?:def|abbrev|structure|inductive|class|opaque|axiom)\s+{name}\b", source):
            errors.append(f"local declaration shadows reviewed dependency {name}")
    if re.search(r'(?m)^\s*(?:local\s+)?notation\s+"(?:Value|Exp|Spt)"', source):
        errors.append("local notation may shadow reviewed carriers")
    uses = re.findall(r"\bFunctionsRel\b", value_part)
    rec = re.search(r"(?ms)^\s*\|\s*recclosure\b(.*)$", value_part)
    if len(uses) != 1 or not rec or (
        ":FunctionsRelenvnextEnvfunctions.lengthfunctionsnextFunctions→"
        not in _compact(rec.group())
    ) or (
        "ValueRel(.recclosurelocationargsenvfunctionsindex)"
        "(.recclosurelocationnextArgsnextEnvnextFunctionsindex)"
        not in _compact(rec.group())
    ):
        errors.append("ValueRel must use the auxiliary relation as the recursive-closure premise")
    witness = list(re.finditer(r"(?ms)^theorem\s+functionsRel_iff\b(.*?)(?=:=\s*by\b)", source))
    if len(witness) != 1:
        return errors + ["missing or ambiguous functionsRel_iff witness"]
    signature = _compact(witness[0].group())
    prefix = (
        "theoremfunctionsRel_iff(envnextEnv:ListValue)(count:Nat)"
        "(functionsnextFunctions:List(Nat×ClosLang.Exp)):"
        "FunctionsRelenvnextEnvcountfunctionsnextFunctions↔"
        "List.Forall₂(funleftright=>∃mi,"
    )
    if not signature.startswith(prefix) or not signature.endswith(")functionsnextFunctions"):
        errors.append("witness must be unconditional and compare the same lists with Forall₂")
    body = signature[len(prefix):-len(")functionsnextFunctions")] if signature.startswith(prefix) else ""
    required = (
        "right.1=left.1∧",
        "shiftSource(altFreeSource[left.2]).1m(count+left.1)i=[right.2]∧",
        "(∀n,altFvSourcen[left.2]=true∧left.1+count≤n→"
        "EnvOkm0ienvnextEnv(n-(left.1+count)))∧",
        "everyFnVarsNone[left.2]∧env.length=m",
    )
    if body != "".join(required):
        errors.append("witness lambda must retain the complete reviewed recursive-function relation")
    return errors
