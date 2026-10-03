#!/usr/bin/env python3
"""Full original signed immediate reconstruction regression, not equivalence proof."""
from pathlib import Path
import re,hashlib,shlex
ROOT=Path(__file__).resolve().parents[2]
EXPECTED="lem4_statement=∀c. 0xFFFFFFFFFFFFF800w ≤ c ∧ c ≤ 2047w ⇒ sw2sw (v2w [c ' 11; c ' 10; c ' 9; c ' 8; c ' 7; c ' 6; c ' 5; c ' 4; c ' 3; c ' 2; c ' 1; c ' 0]) = c\nlem4_types=c : :word64\nlem4_hypotheses=0\nlem4_proved=T\nlem12b_statement=∀c. 0xFFFFFFFF80000000w ≤ c ∧ c ≤ 0x7FFFF7FFw ∧ (1 >< 0) c = 0w ⇒ sw2sw ((31 >< 12) (c + -1w * sw2sw ((11 >< 0) c)) @@ 0w) + sw2sw ((11 >< 0) c && ¬2w) = c\nlem12b_types=c : :word64\nlem12b_hypotheses=0\nlem12b_proved=T\nlem12b_intermediate_types=(11 >< 0) c : :word12; sw2sw ((11 >< 0) c && ¬2w) : :word64; (11 >< 0) c : :word12; sw2sw ((11 >< 0) c) : :word64; (31 >< 12) (c + -1w * sw2sw ((11 >< 0) c)) : :word20; (31 >< 12) (c + -1w * sw2sw ((11 >< 0) c)) @@ 0w : :word32; sw2sw ((31 >< 12) (c + -1w * sw2sw ((11 >< 0) c)) @@ 0w) : :word64; (1 >< 0) c : :word64\n"
HASHES={'lem4': '1f261145ec96a48e0170cf482cb00bc7daf163217813eba98e27b12c9f11cd36', 'lem12b': '89540569248ec7abe74b139347408546dcfebecf1375669686d4190e502390e9'}
SIGNATURES={'signed_twelve_bit_reconstruction': '(c:BitVec64)(h:(0xFFFFFFFFFFFFF800:BitVec64).slec=true∧c.sle0x7FF=true):(holV2w12[c.getLsbD11,c.getLsbD10,c.getLsbD9,c.getLsbD8,c.getLsbD7,c.getLsbD6,c.getLsbD5,c.getLsbD4,c.getLsbD3,c.getLsbD2,c.getLsbD1,c.getLsbD0]).signExtend64=c', 'split_immediate_reconstruction': "(c:BitVec64)(h:(0xFFFFFFFF80000000:BitVec64).slec=true∧c.sle0x7FFFF7FF=true∧(BitVec.extractLsb'02c).setWidth64=0):((BitVec.extractLsb'1220(c+(-1:BitVec64)*(BitVec.extractLsb'012c).signExtend64)).append(0:BitVec12)).signExtend64+((BitVec.extractLsb'012c)&&&~~~(2:BitVec12)).signExtend64=c"}
def check(output,source,probe,lean,driver):
    if output!=EXPECTED:raise ValueError("full original immediate capture/carriers drift")
    if "val () = wordsLib.guess_lengths();" not in probe:
        raise ValueError("original intermediate word-length inference missing")
    for n,digest in HASHES.items():
        for text in (source,probe):
            m=re.search(r"val "+n+r" =\s*(blastLib.BBLAST_PROVE\s*``.*?``)",text,re.S)
            if not m or hashlib.sha256("".join(m[1].split()).encode()).hexdigest()!=digest:
                raise ValueError("literal original signed reconstruction proof drift")
    for n,expected in SIGNATURES.items():
        m=re.search(r"theorem "+n+r"\b(.*?) := by",lean,re.S)
        if not m or "".join(m[1].split())!=expected:
            raise ValueError("full signed immediate bounds/conclusion/carriers drift")
    commands=[shlex.split(line) for line in driver.replace("\\\n"," ").splitlines()
              if line.startswith("run_probe riscv_target_immediate_probeScript.sml ")]
    expected=["run_probe","riscv_target_immediate_probeScript.sml","riscv_target_immediate_probe.out"]+[
        r.split("=",1)[0] for r in EXPECTED.splitlines()]+[
        "$cake_dir/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml","$cake_dir/compiler/encoders/riscv/proofs"]
    if commands!=[expected]:raise ValueError("complete original immediate registration drift")
def inputs():
    return [(ROOT/p).read_text() for p in (
        "scripts/hol-probes/riscv_target_immediate_probe.out",
        "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml",
        "scripts/hol-probes/riscv_target_immediate_probeScript.sml",
        "Flapjack/RiscV/CorrectnessEncoding/Immediate.lean",
        "scripts/hol-probes/regenerate.sh")]
if __name__=="__main__":
    check(*inputs())
    print("PASS two full original signed immediate proofs, types, zero hypotheses, Lean contracts and whole registration")
