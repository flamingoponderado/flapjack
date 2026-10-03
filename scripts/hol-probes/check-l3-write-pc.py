"""Reject drift in original HOL universal equation captures."""
from pathlib import Path
EXPECTED = ['writePC_type=:word64 -> riscv_state -> riscv_state', 'writePC_hypotheses=0', "writePC_fullRecord_equation=∀v s. write'PC v s = s with c_PC := s.c_PC⦇s.procID ↦ v⦈", 'writePC_fullRecord_proof=T', "writePC_allKeys_equation=∀v s k. (write'PC v s).c_PC k = if k = s.procID then v else s.c_PC k", 'writePC_allKeys_proof=T', "writePC_current_equation=∀v s. PC (write'PC v s) = v", 'writePC_current_proof=T']

def check(text):
    if text.splitlines() != EXPECTED:
        raise ValueError("original HOL equation capture differs from reviewed full statements")

if __name__ == "__main__":
    check(Path(__file__).with_name("l3_write_pc_probe.out").read_text())
    print("write_pc: exact original HOL types, hypotheses and universal equations PASS")
