#!/usr/bin/env python3
"""Require the complete independent original register-shift guard set."""
from pathlib import Path
expected = {f"register_shift_{op}_{mode}_{case}_{rd}" for op in ("SLL","SLLW","SRL","SRLW","SRA","SRAW") for mode in (0,2,3) for case in range(10) for rd in (0,1,2,7)}
expected |= {f"register_shift_symbolic_{op}" for op in ("SLLW","SRLW","SRAW")}
expected |= {f"register_shift_invalid_{op}_{prior}_{rd}" for op in ("SLL","SRL","SRA") for prior in (0,1) for rd in (0,1)}
rows = {}
for line in Path(__file__).with_name("l3_register_shift_probe.out").read_text().splitlines():
    if line.startswith("register_shift_") and not line.startswith("register_shift_definition_"):
        key, value = line.split("=", 1)
        if key in rows:
            raise SystemExit(f"duplicate original fixture: {key}")
        rows[key] = value
if set(rows) != expected:
    raise SystemExit(f"fixture mismatch: missing {expected-set(rows)}, extra {set(rows)-expected}")
if any(value != "T" for value in rows.values()):
    raise SystemExit("original equations did not all reduce to T")
print(f"PASS {len(rows)} original whole-state register-shift equations")
