#!/usr/bin/env python3
"""Full original native target validity replay guard; not equivalence evidence."""
from pathlib import Path
import hashlib
import re
import shlex
ROOT=Path(__file__).resolve().parents[2]
EXPECTED='riscv_target_ok_statement=target_ok riscv_target\nriscv_target_ok_types=:(64, riscv_state, word5 # word2 # TransferControl option # exception # (word5 -> word64) # (word64 # word8 -> bool) # word64) target\nriscv_target_ok_hypotheses=0\nriscv_target_ok_proved=T\n'
DIGEST='0e5eb0dabfa2d1036591e7db50b657dfbd3dd40fa1ecf37e3b4a6f1b18fe4dd3'
def check(output,source,probe,lean,driver):
    if output!=EXPECTED:raise ValueError("full target validity capture drift")
    a=re.search(r"Theorem riscv_target_ok\[local\]:\s*(.*?)\nProof\s*(.*?)\nQED",source,re.S)
    b=re.search(r"val riscv_target_ok = prove \(``(.*?)``,\s*(.*?)\);\nval _",probe,re.S)
    for m in (a,b):
        if not m or hashlib.sha256("".join("".join(m.groups()).split()).encode()).hexdigest()!=DIGEST:
            raise ValueError("literal original full target validity proof drift")
    m=re.search(r"theorem riscv_target_ok\b(.*?) := by",lean,re.S)
    if not m or "".join(m[1].split())!=":targetOkriscvTarget":
        raise ValueError("unrestricted full target validity conclusion drift")
    commands=[shlex.split(line) for line in driver.replace("\\\n"," ").splitlines()
              if line.startswith("run_probe riscv_target_ok_probeScript.sml ")]
    expected=["run_probe","riscv_target_ok_probeScript.sml","riscv_target_ok_probe.out"]+[
        r.split("=",1)[0] for r in EXPECTED.splitlines()]+[
        "$cake_dir/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml","$cake_dir/compiler/encoders/riscv/proofs"]
    if commands!=[expected]:raise ValueError("complete original target validity registration drift")
def inputs():
    return [(ROOT/p).read_text() for p in (
        "scripts/hol-probes/riscv_target_ok_probe.out",
        "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml",
        "scripts/hol-probes/riscv_target_ok_probeScript.sml",
        "Flapjack/RiscV/CorrectnessEncoding/TargetOk.lean",
        "scripts/hol-probes/regenerate.sh")]
if __name__=="__main__":
    check(*inputs())
    print("PASS full original native target validity proof, type, zero hypotheses, Lean conclusion and registration")
