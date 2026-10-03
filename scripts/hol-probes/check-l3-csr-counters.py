#!/usr/bin/env python3
"""Independent arithmetic check of literal L3 CSR counter observations.
High reads sign-extend the upper32 bits. High writes shift a word32 by32,
yielding zero, so insertion clears high32 while preserving old low32.
"""
from pathlib import Path
import re
MASK = 2**64-1
bases = [0, MASK, 0x7FFFFFFF00000000, 0x8000000000000000,
         0xFFFFFFFF00000000, 0x123456789ABCDEF0]
low = {3072:0,2304:0,3073:1,2305:1,3074:2,2306:2,
       3329:3,2561:3,3585:4,2817:4,1793:5}
high = {3200:0,2432:0,3201:1,2433:1,3202:2,2434:2,
        3457:3,2689:3,3713:4,2945:4,1857:5}
write_low = {2304:0,2305:1,2306:2,1793:5,2817:4}
write_high = {2432:0,2433:1,2434:2,1857:5,2945:4}
capture = Path(__file__).with_name("l3_csr_counter_probe.out").read_text()
expected = {}
for i, base in enumerate(bases):
    delta = (0x87654321FEDCBA98+i) & MASK
    value = (0xABCDEF1234567890+19*i) & MASK
    clocks = [(base+11)&MASK,base,(base+23)&MASK,base,base,base]
    sums = [(clocks[j]+delta+j+1)&MASK for j in range(6)]
    for csr,j in low.items():
        expected[f"counter_read_{i}_{csr}"] = sums[j]
    for csr,j in high.items():
        upper = sums[j] >> 32
        expected[f"counter_read_{i}_{csr}"] = (upper if upper < 2**31
                                               else upper+2**64-2**32)
    for csr,j in write_low.items():
        expected[f"counter_write_{i}_{csr}"] = (value-clocks[j])&MASK
    for csr,j in write_high.items():
        expected[f"counter_write_{i}_{csr}"] = (delta+j+1)&(2**32-1)
for label, value in expected.items():
    rows = re.findall(r"^"+re.escape(label)+r"=(.*)$", capture, re.M)
    match = re.fullmatch(r"(?:0x([0-9A-Fa-f]+)|(\d+))w", rows[0]) if len(rows)==1 else None
    actual = (int(match[1],16) if match[1] else int(match[2])) if match else None
    if actual != value:
        raise SystemExit(f"{label}: expected {value}, got {rows}")
print("192 independent original CSR counter comparisons passed")
