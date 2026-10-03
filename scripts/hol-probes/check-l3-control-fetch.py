#!/usr/bin/env python3
"""Require complete original control/fetch whole-state regression coverage."""
from pathlib import Path
import re
expected = set(['control_scsr_0', 'control_mrts_0_0', 'control_mrts_0_1', 'control_mrts_0_2', 'control_mrts_0_3', 'control_FETCH_MISALIGNED_0_0', 'control_FETCH_MISALIGNED_0_1', 'control_FETCH_MISALIGNED_0_2', 'control_FETCH_MISALIGNED_0_3', 'control_FETCH_FAULT_0_0', 'control_FETCH_FAULT_0_1', 'control_FETCH_FAULT_0_2', 'control_FETCH_FAULT_0_3', 'control_scsr_7', 'control_mrts_7_0', 'control_mrts_7_1', 'control_mrts_7_2', 'control_mrts_7_3', 'control_FETCH_MISALIGNED_7_0', 'control_FETCH_MISALIGNED_7_1', 'control_FETCH_MISALIGNED_7_2', 'control_FETCH_MISALIGNED_7_3', 'control_FETCH_FAULT_7_0', 'control_FETCH_FAULT_7_1', 'control_FETCH_FAULT_7_2', 'control_FETCH_FAULT_7_3', 'control_scsr_255', 'control_mrts_255_0', 'control_mrts_255_1', 'control_mrts_255_2', 'control_mrts_255_3', 'control_FETCH_MISALIGNED_255_0', 'control_FETCH_MISALIGNED_255_1', 'control_FETCH_MISALIGNED_255_2', 'control_FETCH_MISALIGNED_255_3', 'control_FETCH_FAULT_255_0', 'control_FETCH_FAULT_255_1', 'control_FETCH_FAULT_255_2', 'control_FETCH_FAULT_255_3'])
p = Path(__file__).with_name("l3_control_fetch_probe.out")
rows = re.findall(r"^(control_[A-Za-z0-9_]+)=(.*)$", p.read_text(), re.M)
assert len(rows) == len(expected), "duplicate/missing rows"
assert {k for k,v in rows} == expected, "coverage mismatch"
assert all(v.strip() == "T" for k,v in rows), "original HOL regression failed"
print(f"PASS {len(rows)} original whole-state control/fetch equations")
