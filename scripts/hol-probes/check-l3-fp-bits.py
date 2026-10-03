#!/usr/bin/env python3
"""Require the complete independent original fp_bits guard set."""
from pathlib import Path
expected = {f"fp_bits_{op}_{mode}_{case}_{rd}" for op in ("FSGNJ_S","FSGNJ_D","FSGNJN_S","FSGNJN_D","FSGNJX_S","FSGNJX_D","FMV_X_S","FMV_S_X","FMV_X_D","FMV_D_X") for mode in (0,1,2,3) for case in range(12) for rd in (0,1,2,7)}
rows = {}
for line in Path(__file__).with_name("l3_fp_bits_probe.out").read_text().splitlines():
    if line.startswith("fp_bits_") and not line.startswith("fp_bits_definition_"):
        key, value = line.split("=", 1)
        if key in rows:
            raise SystemExit(f"duplicate original fixture: {key}")
        rows[key] = value
if set(rows) != expected:
    raise SystemExit(f"fixture mismatch: missing {expected-set(rows)}, extra {set(rows)-expected}")
if any(value != "T" for value in rows.values()):
    raise SystemExit("original equations did not all reduce to T")
print(f"PASS {len(rows)} original whole-state fp_bits equations")
