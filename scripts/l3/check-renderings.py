#!/usr/bin/env python3
"""Compare every delivered native definition with the pinned HOL term rendering.

This is a transcription drift gate, not a HOL-to-Lean equivalence proof.
Whitespace/comments and the explicitly recorded computability annotations are
ignored; handwritten equations have individual two-sided hashes and notes.
"""
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
LOCK = ROOT / "scripts/l3/rendering-coverage.json"
START = re.compile(r"^(?:noncomputable )?def (\S+)", re.M)
END = re.compile(r"^(?:@\[|(?:noncomputable )?(?:def|theorem|abbrev|opaque)|end\b|namespace\b|attribute\b|termination_by\b|decreasing_by\b)", re.M)

def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    value = importlib.util.module_from_spec(spec)
    sys.modules[name] = value
    spec.loader.exec_module(value)
    return value

def normalize(text):
    # Preserve quoted strings and identifiers; only exterior whitespace disappears.
    return "".join(re.findall(r'"(?:\\.|[^"\\])*"|«[^»]*»|\S', text))

def digest(text):
    return hashlib.sha256(normalize(text).encode()).hexdigest()

ARM8_DIR = "Flapjack/Compiler/Encoders/Arm8/L3"


def sources(root=ROOT):
    trust = module("l3_drift_comments", root / "scripts/check-native-trust.py")
    result = {}
    paths = [p for p in sorted((root / "Flapjack/RiscV/L3").rglob("*.lean"))
             if p.name == "Defs.lean" or "Defs" in p.parts or "Step" in p.parts]
    paths += [p for p in sorted((root / ARM8_DIR).rglob("*.lean")) if p.name == "Defs.lean"]
    for path in paths:
        text = trust.without_comments(path.read_text())
        for start in START.finditer(text):
            end = END.search(text, start.end())
            body = text[start.start():end.start() if end else len(text)].strip()
            key = str(path.relative_to(root)) + ":" + start.group(1)
            if key in result:
                raise ValueError("duplicate native definition: " + key)
            result[key] = body
    return result

def renderings(root=ROOT):
    renderer = module("l3_drift_renderer", root / "scripts/hol_terms_to_lean.py")
    with tempfile.NamedTemporaryFile(mode="w") as export:
        export.write(gzip.decompress((root / "scripts/l3/riscv_defs.sexp.gz").read_bytes()).decode())
        export.flush()
        emitted, failed = renderer.main(["renderer", export.name, str(root / "Flapjack/RiscV/L3/Types.lean")])
    if failed:
        raise ValueError("unrendered original definitions: " + repr(failed))
    return {(thy, name): (body, nc) for thy, name, _, _, body, _, nc in emitted}


def lean_decl_names(emitted):
    """The Lean declaration name each emitted definition was rendered under.

    This is the name `hol_terms_to_lean.main` chose (including its
    theory-prefix disambiguation for a constant defined in two theories), not a
    rule re-implemented here.
    """
    return {(thy, name): lean for thy, name, lean, *_ in emitted}


def arm8_renderings(root=ROOT):
    renderer = module("l3_drift_renderer_arm8", root / "scripts/hol_terms_to_lean.py")
    with tempfile.NamedTemporaryFile(mode="w") as export:
        export.write(gzip.decompress((root / "scripts/l3/arm8_defs.sexp.gz").read_bytes()).decode())
        export.flush()
        emitted, failed = renderer.main(["renderer", export.name,
                                         str(root / ARM8_DIR / "Types.lean"), "--thy=arm8"])
    if failed:
        raise ValueError("unrendered original ARM8 definitions: " + repr(failed))
    names = lean_decl_names(emitted)
    result = {}
    for thy, name, _, _, body, _, nc in emitted:
        key = names[(thy, name)].strip("«»")
        if key in result:
            raise ValueError("ambiguous ARM8 Lean declaration name: " + key)
        result[key] = (body, nc)
    return result

def rendered_for(key, generated):
    path, name = key.split(":", 1)
    thy = "riscv_step" if "/Step/" in path else "riscv"
    entry = generated.get((thy, name.strip("«»")))
    if entry is None:
        return None
    body, nc = entry
    # The combined export disambiguates the two Fetch roots by theory.
    if thy == "riscv_step" or name == "Fetch":
        body = body.replace(thy + "_Fetch", "Fetch")
    return body, nc

def check(actual, generated, lock, arm8=None):
    if set(actual) != set(lock["definitions"]):
        raise ValueError("native definition coverage changed: " + repr(sorted(set(actual) ^ set(lock["definitions"]))))
    overrides = set()
    for key, source in actual.items():
        if key.startswith(ARM8_DIR + "/"):
            entry = arm8.get(key.split(":", 1)[1].strip("«»")) if arm8 is not None else None
        else:
            entry = rendered_for(key, generated)
        nc = source.startswith("noncomputable ")
        source = source.removeprefix("noncomputable ")
        exception = lock["exceptions"].get(key)
        if exception:
            original = None if entry is None else digest(entry[0])
            if digest(source) != exception["lean_sha256"] or original != exception["rendered_sha256"]:
                raise ValueError("handwritten native equation drift: " + key)
            if not exception["review_note"]:
                raise ValueError("missing native exception source review: " + key)
        elif entry is None or normalize(source) != normalize(entry[0]):
            raise ValueError("original native rendering drift: " + key)
        if entry is not None and nc != entry[1]:
            overrides.add(key)
    if overrides != set(lock["noncomputable_overrides"]):
        raise ValueError("unrecorded native computability annotation drift")
    if not set(lock["exceptions"]) <= set(actual):
        raise ValueError("stale native rendering exception")

if __name__ == "__main__":
    lock = json.loads(LOCK.read_text())
    check(sources(), renderings(), lock, arm8_renderings())
    print(f"native rendering drift PASS: {len(lock['definitions'])} whole definitions, {len(lock['exceptions'])} explicit two-sided/manual exceptions")
