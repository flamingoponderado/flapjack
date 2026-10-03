"""Reject drift in original HOL universal equation captures."""
from pathlib import Path
EXPECTED = ['NextRISCV_type=:riscv_state -> riscv_state option', 'NextRISCV_hypotheses=0', 'NextRISCV_equation=∀s. NextRISCV s =', '    (let', '       (f,s) = Fetch s;', '       s = Run (DecodeAny f) s', '     in', '       if s.exception ≠ NoException then NONE', '       else', '         (let', '            pc = PC s', '          in', '            case NextFetch s of', '              NONE => update_pc (pc + Skip s) s', "            | SOME (BranchTo a) => update_pc a (write'NextFetch NONE s)", '            | SOME Ereturn => NONE', '            | SOME Mrts => NONE', '            | SOME (Trap v5) => NONE))', 'NextRISCV_proof=T']

def check(text):
    if text.splitlines() != EXPECTED:
        raise ValueError("original HOL equation capture differs from reviewed full statements")

if __name__ == "__main__":
    check(Path(__file__).with_name("l3_next_step_probe.out").read_text())
    print("next_step: exact original HOL types, hypotheses and universal equations PASS")
