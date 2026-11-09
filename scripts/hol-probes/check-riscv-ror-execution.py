#!/usr/bin/env python3
"""Pin actual Ror list iteration/interference and original assertion shape.
Syntactic regression only; kernel proof checking and source review are separate.
"""
from pathlib import Path
import hashlib
ROOT=Path(__file__).resolve().parents[2]
# Ror's pin was refreshed after the PR1213 stale-status documentation repair.
# Only its two doc comments changed; statements and proof bodies are unchanged.
CHECKS={'Flapjack/RiscV/CorrectnessEncoding/RorExecution.lean': '588f30e516b4a52b31b88954b2462e0902719da0db953758d542848b69d640f4', 'Flapjack/RiscV/CorrectnessEncoding/ConstExecution.lean': '9913b30a287b7d5c176d44484e545b03063b62efa6e7057dfa4899a540779d32'}
def check(root=ROOT):
    for name,expected in CHECKS.items():
        if hashlib.sha256((root/name).read_bytes()).hexdigest()!=expected:
            raise ValueError('actual Ror list execution/assertion drift: '+name)
    return True
if __name__=='__main__':
    check()
    print('Actual native Ror list execution/interference/asserts2 PASS')
