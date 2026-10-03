#!/usr/bin/env python3
"""Require the complete independent original immediate arithmetic/bitwise guard set."""
from pathlib import Path
expected = {f"immediate_alu_{op}_{case}_{rd}" for op in ("ADDI","ANDI","ORI","XORI") for case in range(10) for rd in (0,1,7)}
rows = {}
for line in Path(__file__).with_name("l3_immediate_alu_probe.out").read_text().splitlines():
    if line.startswith("immediate_alu_") and not line.startswith("immediate_alu_definition_"):
        key, value = line.split("=", 1)
        if key in rows:
            raise SystemExit(f"duplicate original fixture: {key}")
        rows[key] = value
if set(rows) != expected:
    raise SystemExit(f"fixture mismatch: missing {expected-set(rows)}, extra {set(rows)-expected}")
if any(value != "T" for value in rows.values()):
    raise SystemExit("original equations did not all reduce to T")
print(f"PASS {len(rows)} original whole-state immediate arithmetic/bitwise equations")
