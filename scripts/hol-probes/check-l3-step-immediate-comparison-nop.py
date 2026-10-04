#!/usr/bin/env python3
"""Reviewed NOP statement/capture regression; manual source review and Lake remain required."""
from pathlib import Path
import hashlib
import sys
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts/l3'))
from lean_contracts import check_declaration
CHECKS = {'scripts/hol-probes/l3_step_immediate_comparison_nop_probeScript.sml': '2b9ff0cd4b1ad01e240dd779a66bd997776a1364039fbf8eb2bf7aadc210419e', 'scripts/hol-probes/l3_step_immediate_comparison_nop_probe.out': '95bb445bf838a84330b94e3b3d8854f685f64405df35a304ed57f9d769d631ae'}
MODULE = 'Flapjack/RiscV/L3/Step/ImmediateComparisonNop.lean'
def check(root=ROOT):
    for path, expected in CHECKS.items():
        if hashlib.sha256((root / path).read_bytes()).hexdigest() != expected:
            raise ValueError('Original NOP capture drift: ' + path)
    text = (root / MODULE).read_text()
    for name, op in [('dfnSltINop', 'SLTI'), ('dfnSltIUNop', 'SLTIU')]:
        expected = f"""theorem {name} (rd rs1 : BitVec 5) (imm : BitVec 12) (s : riscv_state)
    (h : rd = 0#5) (arch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2) :
    «dfn'{op}» (rd, rs1, imm) s = s"""
        check_declaration(text, 'theorem', name, expected, statement=True)
    rows = (root / 'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10), ' ').splitlines()
    rows = [r for r in rows if r.startswith('run_probe l3_step_immediate_comparison_nop_probeScript.sml ')]
    if len(rows) != 1:
        raise ValueError('NOP capture registration missing/duplicated')
    for op in ['slti_nop', 'sltiu_nop']:
        for suffix in ['statement', 'types', 'source_hypotheses', 'proved']:
            if op+'_'+suffix not in rows[0].split():
                raise ValueError('Original NOP sentinel missing')
    return True
if __name__ == '__main__':
    check()
    print('Exact native SLTI_NOP/SLTIU_NOP statements/captures PASS')
