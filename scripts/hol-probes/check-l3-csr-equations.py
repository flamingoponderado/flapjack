#!/usr/bin/env python3
"""Require concrete truth/error observations from the complete native CSR probes.
These checks are regression evidence; source review remains necessary.
"""
from pathlib import Path
import re
root = Path(__file__).parent
for filename, pattern, count in [
 ("l3_csr_read_value_probe.out",r"csr_read_value_\d+",44),
 ("l3_csr_direct_write_probe.out",r"csr_direct_(?:write|delta)_\d+",30),
 ("l3_csr_special_write_probe.out",r"csr_(?:special_write_\d+|ipi_equation|ipi_write|fp_write_\d+|ipi_boundary_\d+_\d+)",47),
]:
 rows = re.findall(r"^"+pattern+r"=(.*)$",(root/filename).read_text(),re.M)
 if len(rows)!=count or any(row!="T" for row in rows):
  raise SystemExit(f"{filename}: expected {count} concrete true equations")
s = (root/"l3_csr_unknown_probe.out").read_text()
for key in [0,773,1922,4095]:
 for op in ["read","write"]:
  kind = "UNDEFINED" if op=="read" else "INTERNAL_ERROR"
  text = f"unexpected CSR read at {key:X}" if op=="read" else f"unexpected CSR write to {key:X}"
  expected = {f"csr_unknown_{op}_{key}":f'{kind} "{text}"',f"csr_prior_{op}_{key}":"T"}
  if op=="read":expected[f"csr_arb_{key}"]="T"
  for label,value in expected.items():
   rows=re.findall(r"^"+re.escape(label)+r"=(.*)$",s,re.M)
   if rows != [value]:raise SystemExit(f"{label}: expected {value}, got {rows}")
print("121 CSR state/value equations and20 unknown-CSR observations passed")
