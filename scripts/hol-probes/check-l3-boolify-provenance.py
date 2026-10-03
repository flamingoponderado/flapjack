#!/usr/bin/env python3
"""Check exact original generated equations, types, zero hypotheses and proofs."""
from pathlib import Path
import re

path = Path(__file__).with_name("l3_boolify_provenance_probe.out")
rows = re.findall(r"^(boolify[A-Za-z0-9_]+)=(.*)$", path.read_text(), re.M)
expected = {}
for width in (8, 16, 32):
    prefix = f"boolify{width}"
    bits = ",".join(f"word_bit {i} w" for i in range(width - 1, -1, -1))
    expected[f"{prefix}_definition"] = f"∀w. {prefix} w = ({bits})"
    expected[f"{prefix}_type"] = f":word{width} -> " + " # ".join(["bool"] * width)
    expected[f"{prefix}_hypotheses"] = "0"
    expected[f"{prefix}_full_equation"] = "T"
if len(rows) != len(expected) or dict(rows) != expected:
    raise SystemExit("FAIL incomplete or changed original boolify declaration/type/proof")
print("PASS three full fixed-width boolify definitions/types/zero-hypothesis proofs")
