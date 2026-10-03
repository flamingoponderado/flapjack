#!/usr/bin/env python3
"""Require the complete independent original word-arithmetic guard set."""
from pathlib import Path
expected = {f"word_arithmetic_{op}_{mode}_{case}_{rd}" for op in ("ADDIW","ADDW","SUBW") for mode in (0,2,3) for case in range(10) for rd in (0,1,2,7)}
expected |= {f"word_arithmetic_symbolic_{op}" for op in ("ADDIW","ADDW","SUBW")}
rows = {}
for line in Path(__file__).with_name("l3_word_arithmetic_probe.out").read_text().splitlines():
    if line.startswith("word_arithmetic_") and not line.startswith("word_arithmetic_definition_"):
        key, value = line.split("=", 1)
        if key in rows:
            raise SystemExit(f"duplicate original fixture: {key}")
        rows[key] = value
if set(rows) != expected:
    raise SystemExit(f"fixture mismatch: missing {expected-set(rows)}, extra {set(rows)-expected}")
if any(value != "T" for value in rows.values()):
    raise SystemExit("original equations did not all reduce to T")
print(f"PASS {len(rows)} original whole-state word-arithmetic equations")
