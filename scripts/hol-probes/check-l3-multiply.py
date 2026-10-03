#!/usr/bin/env python3
"""Require the complete independent original multiply guard set."""
from pathlib import Path
expected = {f"multiply_{op}_{mode}_{case}_{rd}" for op in ("MUL","MULH","MULHU","MULHSU","MULW") for mode in (0,2,3) for case in range(12) for rd in (0,1,2,7)}
expected |= {f"multiply_symbolic_{op}_{prior}" for op in ("MUL","MULH","MULHU","MULHSU","MULW") for prior in (0,1)}
rows = {}
for line in Path(__file__).with_name("l3_multiply_probe.out").read_text().splitlines():
    if line.startswith("multiply_") and not line.startswith("multiply_definition_"):
        key, value = line.split("=", 1)
        if key in rows:
            raise SystemExit(f"duplicate original fixture: {key}")
        rows[key] = value
if set(rows) != expected:
    raise SystemExit(f"fixture mismatch: missing {expected-set(rows)}, extra {set(rows)-expected}")
if any(value != "T" for value in rows.values()):
    raise SystemExit("original equations did not all reduce to T")
print(f"PASS {len(rows)} original whole-state multiply equations")
