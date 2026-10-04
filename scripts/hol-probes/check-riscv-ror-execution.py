#!/usr/bin/env python3
"""Pin actual Ror list iteration/interference and original assertion shape.
Syntactic regression only; kernel proof checking and source review are separate.
"""
from pathlib import Path
import hashlib
ROOT=Path(__file__).resolve().parents[2]
CHECKS={'Flapjack/RiscV/CorrectnessEncoding/RorExecution.lean': '5ee51e63422ca0e8a32e681707dc772ce3a806ef3f2d39a94f3021a62f44a503', 'Flapjack/RiscV/CorrectnessEncoding/ConstExecution.lean': '8ccc2e226b846fe9046546c3f7c6604bd299d8a54b1921e18bc0e336a8db3d40'}
def check(root=ROOT):
    for name,expected in CHECKS.items():
        if hashlib.sha256((root/name).read_bytes()).hexdigest()!=expected:
            raise ValueError('actual Ror list execution/assertion drift: '+name)
    return True
if __name__=='__main__':
    check()
    print('Actual native Ror list execution/interference/asserts2 PASS')
