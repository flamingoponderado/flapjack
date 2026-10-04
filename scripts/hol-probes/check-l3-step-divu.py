"""Reject drift in original HOL DIVU step captures."""
from pathlib import Path

EXPECTED = [
    'divu_hypotheses=((s :riscv_state).c_MCSR s.procID).mcpuid.ArchBase ≠ (1w :word2)',
    '(rd :word5) ≠ (0w :word5)',
    "divu_statement=dfn'DIVU ((rd :word5),(rs1 :word5),(rs2 :word5)) (s :riscv_state) =",
    's with',
    'c_gpr :=',
    '  s.c_gpr⦇',
    '    s.procID ↦',
    '      (s.c_gpr s.procID)⦇',
    '        rd ↦',
    '          (if',
    '             if rs2 = (0w :word5) then T',
    '             else if (s.c_MCSR s.procID).mcpuid.ArchBase = (0w :word2) then',
    '               (w2w',
    '                  (((31 :num) >< (0 :num)) (s.c_gpr s.procID rs2) :word32) :',
    '                word64) =',
    '               (0w',
    '                 :word64)',
    '             else s.c_gpr s.procID rs2 = (0w :word64)',
    '           then',
    '             (0xFFFFFFFFFFFFFFFFw :word64)',
    '           else',
    '             (if rs1 = (0w :word5) then (0w :word64)',
    '              else if (s.c_MCSR s.procID).mcpuid.ArchBase = (0w :word2) then',
    '                (w2w',
    '                   (((31 :num) >< (0 :num)) (s.c_gpr s.procID rs1) :word32) :',
    '                 word64)',
    '              else s.c_gpr s.procID rs1) //',
    '             (if rs2 = (0w :word5) then (0w :word64)',
    '              else if (s.c_MCSR s.procID).mcpuid.ArchBase = (0w :word2) then',
    '                (w2w',
    '                   (((31 :num) >< (0 :num)) (s.c_gpr s.procID rs2) :word32) :',
    '                 word64)',
    '              else s.c_gpr s.procID rs2))',
    '      ⦈',
    '  ⦈',
    'divu_nop_hypotheses=((s :riscv_state).c_MCSR s.procID).mcpuid.ArchBase ≠ (1w :word2)',
    '(rd :word5) = (0w :word5)',
    "divu_nop_statement=dfn'DIVU ((rd :word5),(rs1 :word5),(rs2 :word5)) (s :riscv_state) = s",
    "source=HOL riscv_stepScript.sml:881 DIVU = arithr [] over dfn'DIVU_def with the rd = 0w companion avoided; per-theorem Thm.hyp captured above; the 64/32-bit widening is unconditional (avoid []), so the sole write hypothesis is rd <> 0w and the DIVU_NOP companion adds rd = 0w",
]


def check(text):
    if text.splitlines() != EXPECTED:
        raise ValueError("original HOL DIVU capture differs from reviewed statement")


if __name__ == "__main__":
    check(Path(__file__).with_name("l3_step_divu_probe.out").read_text())
    print("step_divu: exact original HOL statement, hypotheses and types PASS")
