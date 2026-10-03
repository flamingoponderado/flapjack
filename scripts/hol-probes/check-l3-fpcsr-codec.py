#!/usr/bin/env python3
"""Independently check full FPCSR field/packing rows from the original model.

Expectations use literal bit positions at riscvScript.sml:867-892, rather
than the renderer or Lean implementation. All rows must evaluate concretely.
"""
from pathlib import Path
import re

values = [0, 2**32-1, 0xAAAAAAAA, 0x55555555, 0x01234567, 0xFEDCBA98]
values += [1 << i for i in range(32)]
capture = Path(__file__).with_name("l3_fpcsr_codec_probe.out").read_text()

def normalize(text):
    text = re.sub(r"0x([0-9A-Fa-f]+)w", lambda m: str(int(m[1], 16))+"w", text)
    return re.sub(r"\s+", "", text)

for i, value in enumerate(values):
    fields = [bool(value & 8), (value >> 5) & 7, bool(value & 16),
              bool(value & 1), bool(value & 4), bool(value & 2), value >> 8]
    words = [(("T" if field else "F") if isinstance(field, bool)
              else str(field)+"w") for field in fields]
    expected = {f"fpcsr_decode_{i}": "("+",".join(words)+")",
                f"fpcsr_encode_{i}": str(value)+"w"}
    for label, result in expected.items():
        rows = re.findall(r"^"+re.escape(label)+r"=(.*)$", capture, re.M)
        if len(rows) != 1 or normalize(rows[0]) != normalize(result):
            raise SystemExit(f"{label}: expected {result}, got {rows}")
print("76 independent original FPCSR field/packing comparisons passed")
