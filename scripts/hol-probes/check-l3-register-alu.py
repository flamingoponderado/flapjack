#!/usr/bin/env python3
"""Require the complete independent original register arithmetic/bitwise guard set."""
from pathlib import Path
expected = {f"register_alu_{op}_{case}_{rd}" for op in ("ADD","SUB","AND","OR","XOR") for case in range(8) for rd in (0,1,2,7)}
rows = {}
for line in Path(__file__).with_name("l3_register_alu_probe.out").read_text().splitlines():
    if line.startswith("register_alu_") and not line.startswith("register_alu_definition_"):
        key, value = line.split("=", 1)
        if key in rows:
            raise SystemExit(f"duplicate original fixture: {key}")
        rows[key] = value
if set(rows) != expected:
    raise SystemExit(f"fixture mismatch: missing {expected-set(rows)}, extra {set(rows)-expected}")
if any(value != "T" for value in rows.values()):
    raise SystemExit("original equations did not all reduce to T")
print(f"PASS {len(rows)} original whole-state register arithmetic/bitwise equations")
