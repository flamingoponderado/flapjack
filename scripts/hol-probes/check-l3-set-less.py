#!/usr/bin/env python3
"""Require the complete independent original set-less-than guard set."""
from pathlib import Path
expected = {f"set_less_{op}_{mode}_{case}_{rd}" for op in ("SLT","SLTU") for mode in (0,2,3) for case in range(10) for rd in (0,1,2,7)}
expected |= {f"set_less_{op}_{mode}_{case}_{rd}" for op in ("SLTI","SLTIU") for mode in (0,2,3) for case in range(10) for rd in (0,1,7)}
expected |= {f"set_less_invalid_{op}_{prior}_{rd}" for op in ("SLT","SLTU","SLTI","SLTIU") for prior in (0,1) for rd in (0,1)}
rows = {}
for line in Path(__file__).with_name("l3_set_less_probe.out").read_text().splitlines():
    if line.startswith("set_less_") and not line.startswith("set_less_definition_"):
        key, value = line.split("=", 1)
        if key in rows:
            raise SystemExit(f"duplicate original fixture: {key}")
        rows[key] = value
if set(rows) != expected:
    raise SystemExit(f"fixture mismatch: missing {expected-set(rows)}, extra {set(rows)-expected}")
if any(value != "T" for value in rows.values()):
    raise SystemExit("original equations did not all reduce to T")
print(f"PASS {len(rows)} original whole-state set-less-than equations")
