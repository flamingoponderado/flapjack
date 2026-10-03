#!/usr/bin/env python3
"""Fail closed on complete independent original conditional-branch guards."""
from pathlib import Path
OPS = ("BEQ", "BNE", "BLT", "BGE", "BLTU", "BGEU")
expected = {f"conditional_branch_{op}_{mode}_{case}" for op in OPS for mode in (0,2,3) for case in range(8)}
expected |= {f"conditional_branch_invalid_{op}_{prior}" for op in OPS for prior in (0,1)}
rows = {}
for line in Path(__file__).with_name("l3_conditional_branch_probe.out").read_text().splitlines():
    if line.startswith("conditional_branch_") and not line.startswith("conditional_branch_definition_"):
        key, value = line.split("=", 1)
        if key in rows:
            raise SystemExit(f"duplicate original fixture: {key}")
        rows[key] = value
if set(rows) != expected:
    raise SystemExit(f"fixture mismatch: missing {expected-set(rows)}, extra {set(rows)-expected}")
if any(value != "T" for value in rows.values()):
    raise SystemExit("original conditional branch equations did not all reduce to T")
print(f"PASS {len(rows)} original whole-state conditional branch equations")
