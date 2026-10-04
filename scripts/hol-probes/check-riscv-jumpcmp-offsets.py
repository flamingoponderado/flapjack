#!/usr/bin/env python3
"""Original JumpCmp payload/PC arithmetic regression guard; not equivalence proof."""
from pathlib import Path
import hashlib
ROOT=Path(__file__).resolve().parents[2]
CHECKS={'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Arithmetic.lean': 'd4a85dfc0b1c86d028c6c12e0c80f24c0edd0c6cb5678c1351b6761d17394492', 'scripts/hol-probes/riscv_jumpcmp_offsets_probeScript.sml': '0b3d21b1571298bf69b7dd2f43ab2f1c072f7808ae3522b72f4da461d43903fa', 'scripts/hol-probes/riscv_jumpcmp_offsets_probe.out': 'e20d9acbd02e2ebb498235d988bbc57b344e564c3452ae7be44034f108e6fe8b', 'cakeml/compiler/encoders/riscv/riscv_targetScript.sml': 'e87d7e7b67bae40f96ac966209786bcaf4094df86abaa80552c22e6ecb533926'}
LABELS=['near0_statement', 'near0_types', 'near0_hypotheses', 'near0_proved', 'near0_boundary0', 'near0_boundary1', 'near0_boundary2', 'near0_boundary3', 'near0_boundary4', 'near4_statement', 'near4_types', 'near4_hypotheses', 'near4_proved', 'near4_boundary0', 'near4_boundary1', 'near4_boundary2', 'near4_boundary3', 'near4_boundary4', 'far4_statement', 'far4_types', 'far4_hypotheses', 'far4_proved', 'far4_boundary0', 'far4_boundary1', 'far4_boundary2', 'far4_boundary3', 'far4_boundary4', 'far8_statement', 'far8_types', 'far8_hypotheses', 'far8_proved', 'far8_boundary0', 'far8_boundary1', 'far8_boundary2', 'far8_boundary3', 'far8_boundary4', 'pc_bias_statement', 'pc_bias_hypotheses', 'pc_bias_proved', 'reg_equal_source', 'reg_equal_hypotheses', 'reg_test_source', 'reg_test_hypotheses', 'imm_equal_source', 'imm_equal_hypotheses', 'imm_test_source', 'imm_test_hypotheses']
def check(root=ROOT):
    for name,digest in CHECKS.items():
        if hashlib.sha256((root/name).read_bytes()).hexdigest()!=digest:
            raise ValueError('original offset arithmetic/source/evidence drift: '+name)
    if 'import Flapjack.RiscV.CorrectnessEncoding.JumpCmp.Arithmetic' not in (root/'Flapjack.lean').read_text().splitlines():
        raise ValueError('missing arithmetic root import')
    commands=(root/'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10),' ').splitlines()
    registered=[c for c in commands if c.startswith('run_probe riscv_jumpcmp_offsets_probeScript.sml ')]
    if len(registered)!=1:
        raise ValueError('must register one complete original offset capture')
    rows=dict(line.split('=',1) for line in (root/'scripts/hol-probes/riscv_jumpcmp_offsets_probe.out').read_text().splitlines())
    for label in LABELS:
        if label not in registered[0] or not rows.get(label):
            raise ValueError('missing original offset evidence: '+label)
        if label.endswith('_hypotheses') and rows[label]!='0':
            raise ValueError('original offset proof assumptions: '+label)
        if ('_boundary' in label or label.endswith('_proved')) and rows[label]!='T':
            raise ValueError('unproved original offset evidence: '+label)
    return True
if __name__=='__main__':
    check()
    print('Original JumpCmp shifted payload and PC equations/source/evidence PASS')
