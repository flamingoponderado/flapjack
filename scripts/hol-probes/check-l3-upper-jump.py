#!/usr/bin/env python3
"""Require the complete independent original upper-immediate/jump guard set."""
from pathlib import Path
expected = {f"upper_jump_{op}_{case}_{rd}" for op in ("LUI","AUIPC","JAL","JALR") for case in range(5) for rd in (0,1,7)}
expected |= {f"upper_jump_zero_JALR_{imm}_{rd}" for imm in (0,1,4095) for rd in (0,1,7)}
expected |= {"upper_jump_helper_Skip", "upper_jump_helper_branchTo"}
rows = {}
for line in Path(__file__).with_name("l3_upper_jump_probe.out").read_text().splitlines():
    if line.startswith("upper_jump_") and not line.startswith("upper_jump_definition_"):
        key, value = line.split("=", 1)
        if key in rows:
            raise SystemExit(f"duplicate original fixture: {key}")
        rows[key] = value
if set(rows) != expected:
    raise SystemExit(f"fixture mismatch: missing {expected-set(rows)}, extra {set(rows)-expected}")
if any(value != "T" for value in rows.values()):
    raise SystemExit("original equations did not all reduce to T")
print(f"PASS {len(rows)} original whole-state upper-immediate/jump equations")
