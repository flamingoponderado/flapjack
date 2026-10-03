#!/usr/bin/env python3
"""Complete original encoding contract replay guard; not cross-language equivalence."""
from pathlib import Path
import re
import shlex
ROOT=Path(__file__).resolve().parents[2]
EXPECTED=['length_riscv_encode_statement=∀i. LENGTH (riscv_encode i) = 4', 'length_riscv_encode_types=i : :instruction', 'length_riscv_encode_hypotheses=0', 'length_riscv_encode_proved=T', 'riscv_encode_not_nil_statement=∀i. riscv_encode i ≠ []', 'riscv_encode_not_nil_types=i : :instruction', 'riscv_encode_not_nil_hypotheses=0', 'riscv_encode_not_nil_proved=T', 'riscv_encoding_statement=∀i. LENGTH (LIST_BIND (riscv_ast i) riscv_encode) MOD 4 = 0 ∧ LIST_BIND (riscv_ast i) riscv_encode ≠ []', 'riscv_encoding_types=i : :64 asm', 'riscv_encoding_hypotheses=0', 'riscv_encoding_proved=T']
HOL={'length_riscv_encode': ('!i. LENGTH (riscv_encode i) = 4', 'rw [riscv_encode_def]'), 'riscv_encode_not_nil': ('!i. riscv_encode i <> []', 'simp_tac std_ss [length_riscv_encode, GSYM listTheory.LENGTH_NIL]'), 'riscv_encoding': 'Q.prove (\n   `!i. let l = riscv_enc i in (LENGTH l MOD 4 = 0) /\\ l <> []`,\n   strip_tac\n   \\\\ asmLib.asm_cases_tac `i`\n   \\\\ rw [riscv_enc_def, riscv_const32_def, riscv_encode_fail_def,\n          length_riscv_encode, riscv_encode_not_nil, riscv_ast_def]\n   \\\\ REPEAT CASE_TAC\n   \\\\ rw [length_riscv_encode, riscv_encode_not_nil]\n   )\n   |> SIMP_RULE (srw_ss()++boolSimps.LET_ss) [riscv_enc_def]'}
LEAN={'length_riscv_encode': ' (i : instruction) : (riscvEncode i).length = 4', 'riscv_encode_not_nil': ' (i : instruction) : riscvEncode i ≠ []', 'riscv_encoding': ' (i : HolAsm 64) :\n    (riscvEnc i).length % 4 = 0 ∧ riscvEnc i ≠ []'}
def check(output,source,probe,lean,driver):
    if output.splitlines()!=EXPECTED:raise ValueError("original full encoding contract capture drift")
    for n in ("length_riscv_encode","riscv_encode_not_nil"):
        a=re.search(r"Theorem "+n+r"\[local\]:\s*(.*?)\nProof\s*(.*?)\nQED",source,re.S)
        b=re.search(r"val "+n+r" = prove \(``(.*?)``,\s*(.*?)\);\nval",probe,re.S)
        for m in (a,b):
            if not m or any("".join(x.split())!="".join(y.split()) for x,y in zip(m.groups(),HOL[n])):
                raise ValueError("literal original instruction proof drift")
    a=re.search(r"val riscv_encoding = (.*?)\n\nTheorem riscv_target_ok",source,re.S)
    b=re.search(r"val riscv_encoding = (.*?);\nval _",probe,re.S)
    for m in (a,b):
        if not m or "".join(m[1].split())!="".join(HOL["riscv_encoding"].split()):
            raise ValueError("literal original full ASM Q.prove/SIMP_RULE drift")
    for n,expected in LEAN.items():
        m=re.search(r"theorem "+n+r"\b(.*?) := by",lean,re.S)
        if not m or "".join(m[1].split())!="".join(expected.split()):
            raise ValueError("full unrestricted Lean contract drift")
    commands=[shlex.split(line) for line in driver.replace("\\\n"," ").splitlines()
              if line.startswith("run_probe riscv_target_length_probeScript.sml ")]
    expected=["run_probe","riscv_target_length_probeScript.sml","riscv_target_length_probe.out"]+[
        r.split("=",1)[0] for r in EXPECTED]+[
        "$cake_dir/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml","$cake_dir/compiler/encoders/riscv/proofs"]
    if commands!=[expected]:raise ValueError("complete encoding contract registration drift")
if __name__=="__main__":
    check(Path(__file__).with_name("riscv_target_length_probe.out").read_text(),
          (ROOT/"cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml").read_text(),
          Path(__file__).with_name("riscv_target_length_probeScript.sml").read_text(),
          (ROOT/"Flapjack/RiscV/CorrectnessEncoding/Length.lean").read_text(),
          Path(__file__).with_name("regenerate.sh").read_text())
    print("PASS all three unrestricted original instruction/ASM length-nonempty proofs and driver")
