#!/usr/bin/env python3
"""Conditional byte-driven full Next regression guard; not cross-language proof."""
from pathlib import Path
import hashlib
ROOT=Path(__file__).resolve().parents[2]
CHECKS={'Flapjack/RiscV/CorrectnessEncoding/JumpCmp/Native.lean': '96c1ba6baa1b7195b126346f1fd8a39c2c0ff43dafbe733d9d84492601de96cd', 'scripts/hol-probes/riscv_conditional_next_probeScript.sml': '0ad98483ca9e9521a8bd94ce92e809340ef99ed61fb5154e56bcf7aa1f3445a1'}
CHECKS['scripts/hol-probes/riscv_conditional_next_probe.out']='21d65648e3422dd77b3c36cbada1bbce4e141e2f67f35e80f16788bab4775bd5'
OPS=('beq','bne','blt','bltu','bge','bgeu')
SUFFIXES=('zero','alias_sign','odd_taken','odd_reverse','signed_boundary')
def check(root=ROOT):
    for name, digest in CHECKS.items():
        if hashlib.sha256((root/name).read_bytes()).hexdigest()!=digest:
            raise ValueError('conditional full transition/evidence drift: '+name)
    if 'import Flapjack.RiscV.CorrectnessEncoding.JumpCmp.Native' not in (root/'Flapjack.lean').read_text().splitlines():
        raise ValueError('missing root import')
    commands=(root/'scripts/hol-probes/regenerate.sh').read_text().replace(chr(92)+chr(10),' ').splitlines()
    registered=[c for c in commands if c.startswith('run_probe riscv_conditional_next_probeScript.sml ')]
    if len(registered)!=1:
        raise ValueError('must have one complete native Next registration')
    rows=dict(line.split('=',1) for line in (root/'scripts/hol-probes/riscv_conditional_next_probe.out').read_text().splitlines() if '=' in line)
    for op in OPS:
        for suffix in SUFFIXES:
            label=op+'_next_'+suffix
            if label not in registered[0] or rows.get(label)!='T':
                raise ValueError('missing/false original Next evidence: '+label)
    for name in (*OPS,'next'):
        for suffix in ('source','hypotheses','typed_source'):
            if name+'_'+suffix not in registered[0] or name+'_'+suffix not in rows:
                raise ValueError('missing original typed source: '+name+'_'+suffix)
        if rows[name+'_hypotheses']!='0':
            raise ValueError('original source assumptions: '+name)
        if ':' not in rows[name+'_typed_source']:
            raise ValueError('missing original source carrier types: '+name)
    return True
if __name__=='__main__':
    check()
    print('Six full byte-driven conditional native transitions/evidence PASS')
