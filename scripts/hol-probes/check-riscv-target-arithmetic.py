#!/usr/bin/env python3
"""Strict original proof replay evidence; not a cross-language equivalence check."""
from pathlib import Path
import re
ROOT = Path(__file__).resolve().parents[2]
EXPECTED = ["arithmetic_lem5_statement=∀c. aligned 2 c ⇒ ¬c ' 1", 'arithmetic_lem5_types=c : :word64', 'arithmetic_lem5_hypotheses=0', 'arithmetic_lem5_proved=T', 'arithmetic_lem8_statement=∀y x b. (if b then 1w else 0w) = v2w [x] ‖ v2w [y] ⇔ (b ⇔ x ∨ y)', 'arithmetic_lem8_types=y : :bool, x : :bool, b : :bool', 'arithmetic_lem8_hypotheses=0', 'arithmetic_lem8_proved=T', 'arithmetic_lem9_statement=∀r2 r3. (18446744073709551616 ≤ w2n r2 + (w2n r3 + 1) ⇔ 0x10000000000000000w ≤₊ w2w r2 + w2w r3 + 1w) ∧ (18446744073709551616 ≤ w2n r2 + w2n r3 ⇔ 0x10000000000000000w ≤₊ w2w r2 + w2w r3)', 'arithmetic_lem9_types=r2 : :word64, r3 : :word64', 'arithmetic_lem9_sum_type=:65 word', 'arithmetic_lem9_hypotheses=0', 'arithmetic_lem9_proved=T']

def check(text):
    if text.splitlines() != EXPECTED:
        raise ValueError("original complete arithmetic statement/type/hypothesis/kernel row drift")

def check_replay(original, probe):
    for name in ("lem5", "lem8", "lem9"):
        source = re.search(r"Theorem " + name + r"\[local\]:\s*(.*?)\nProof\s*(.*?)\nQED", original, re.S)
        replay = re.search(r"val " + name + r" = prove \(``(.*?)``,\s*(.*?)\);\nval _", probe, re.S)
        if not source or not replay or any("".join(a.split()) != "".join(b.split())
                for a, b in zip(source.groups(), replay.groups())):
            raise ValueError("original literal arithmetic proof replay drift: " + name)

if __name__ == "__main__":
    check(Path(__file__).with_name("riscv_target_arithmetic_probe.out").read_text())
    check_replay((ROOT / "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml").read_text(),
                 Path(__file__).with_name("riscv_target_arithmetic_probeScript.sml").read_text())
    print("PASS three complete original fixed64/65 arithmetic proof replays, full types and zero hypotheses")
