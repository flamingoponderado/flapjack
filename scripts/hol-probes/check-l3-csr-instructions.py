#!/usr/bin/env python3
"""Fail closed on the independently stated original instruction equations."""
from pathlib import Path
OPS = ("CSRRW", "CSRRS", "CSRRC", "CSRRWI", "CSRRSI", "CSRRCI")
expected = {f"csr_instruction_{op}_{v}_{rd}" for op in OPS for v in (0,1) for rd in (0,1,7)}
expected |= {f"csr_instruction_{kind}_{op}_{v}_{rd}" for kind in ("readonly","privilege") for op in OPS for v in (0,1) for rd in (0,7)}
expected |= {f"csr_instruction_mode{mode}_{op}" for mode in (0,1,3) for op in OPS}
rows = {}
for line in Path(__file__).with_name("l3_csr_instruction_probe.out").read_text().splitlines():
    if line.startswith("csr_instruction_") and not line.startswith("csr_instruction_definition_"):
        key, value = line.split("=", 1)
        if key in rows:
            raise SystemExit(f"duplicate original fixture: {key}")
        rows[key] = value
if set(rows) != expected:
    raise SystemExit(f"original fixture mismatch: missing {expected-set(rows)}, extra {set(rows)-expected}")
if any(value != "T" for value in rows.values()):
    raise SystemExit("original instruction equations did not all reduce to T")
print(f"PASS {len(rows)} original whole-state instruction equations")
