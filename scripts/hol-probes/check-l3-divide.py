#!/usr/bin/env python3
"""Require the complete independent original divide guard set."""
from pathlib import Path
expected = {f"divide_{op}_{mode}_{case}_{rd}" for op in ("DIV","REM","DIVU","REMU","DIVW","REMW","DIVUW","REMUW") for mode in (0,2,3) for case in range(15) for rd in (0,1,2,7)}
expected |= {f"divide_symbolic_{op}_{prior}" for op in ("DIV","REM","DIVU","REMU","DIVW","REMW","DIVUW","REMUW") for prior in (0,1)}
rows = {}
for line in Path(__file__).with_name("l3_divide_probe.out").read_text().splitlines():
    if line.startswith("divide_") and not line.startswith("divide_definition_"):
        key, value = line.split("=", 1)
        if key in rows:
            raise SystemExit(f"duplicate original fixture: {key}")
        rows[key] = value
if set(rows) != expected:
    raise SystemExit(f"fixture mismatch: missing {expected-set(rows)}, extra {set(rows)-expected}")
if any(value != "T" for value in rows.values()):
    raise SystemExit("original equations did not all reduce to T")
print(f"PASS {len(rows)} original whole-state divide equations")
