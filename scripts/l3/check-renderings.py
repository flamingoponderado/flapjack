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

def sources(root=ROOT):
    trust = module("l3_drift_comments", root / "scripts/check-native-trust.py")
    result = {}
    for path in sorted((root / "Flapjack/RiscV/L3").rglob("*.lean")):
        if not (path.name == "Defs.lean" or "Defs" in path.parts or "Step" in path.parts):
            continue
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
    return {(thy, name): (body, nc) for thy, name, _, body, _, nc in emitted}

def rendered_for(key, generated):
    path, name = key.split(":", 1)
    thy = "riscv_step" if "/Step/" in path else "riscv"
    entry = generated.get((thy, name.strip("«»")))
    if entry is None:
        return None
    body, nc = entry
    # The combined export disambiguates the two Fetch roots by theory.
    if name == "Fetch":
        body = body.replace(thy + "_Fetch", "Fetch")
    return body, nc

def check(actual, generated, lock):
    if set(actual) != set(lock["definitions"]):
        raise ValueError("native definition coverage changed: " + repr(sorted(set(actual) ^ set(lock["definitions"]))))
    overrides = set()
    for key, source in actual.items():
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
    check(sources(), renderings(), lock)
    print(f"native rendering drift PASS: {len(lock['definitions'])} whole definitions, {len(lock['exceptions'])} explicit two-sided/manual exceptions")
