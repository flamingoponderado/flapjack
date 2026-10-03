#!/usr/bin/env python3
"""Require the complete independent original immediate-shift guard set."""
from pathlib import Path
expected = {f"immediate_shift_{op}_{mode}_{case}_{rd}" for op in ("SLLI","SLLIW","SRLI","SRLIW","SRAI","SRAIW") for mode in (0,2,3) for case in range(10) for rd in (0,1,7)}
expected |= {f"immediate_shift_symbolic_{op}" for op in ("SLLI","SLLIW","SRLI","SRLIW","SRAI","SRAIW")}
expected |= {f"immediate_shift_invalid_{op}_{prior}_{rd}" for op in ("SLLI","SRLI","SRAI") for prior in (0,1) for rd in (0,1)}
rows = {}
for line in Path(__file__).with_name("l3_immediate_shift_probe.out").read_text().splitlines():
    if line.startswith("immediate_shift_") and not line.startswith("immediate_shift_definition_"):
        key, value = line.split("=", 1)
        if key in rows:
            raise SystemExit(f"duplicate original fixture: {key}")
        rows[key] = value
if set(rows) != expected:
    raise SystemExit(f"fixture mismatch: missing {expected-set(rows)}, extra {set(rows)-expected}")
if any(value != "T" for value in rows.values()):
    raise SystemExit("original equations did not all reduce to T")
print(f"PASS {len(rows)} original whole-state immediate-shift equations")
