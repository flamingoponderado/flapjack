"""Reject drift in original HOL universal equation captures."""
from pathlib import Path
EXPECTED = ['updatePC_type=:word64 -> riscv_state -> riscv_state option', 'updatePC_hypotheses=0', "updatePC_some_equation=∀v s. update_pc v s = SOME (write'PC v s)", 'updatePC_some_proof=T', 'updatePC_fullRecord_equation=∀v s. update_pc v s = SOME (s with c_PC := s.c_PC⦇s.procID ↦ v⦈)', 'updatePC_fullRecord_proof=T']

def check(text):
    if text.splitlines() != EXPECTED:
        raise ValueError("original HOL equation capture differs from reviewed full statements")

if __name__ == "__main__":
    check(Path(__file__).with_name("l3_update_pc_probe.out").read_text())
    print("update_pc: exact original HOL types, hypotheses and universal equations PASS")
