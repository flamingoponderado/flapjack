#!/usr/bin/env python3
"""Strict original proof replay evidence; not a cross-language equivalence check."""
from pathlib import Path
import re
ROOT = Path(__file__).resolve().parents[2]
EXPECTED = ['wide_mul_long_statement=∀a b. n2w (w2n a * w2n b DIV 18446744073709551616) = (127 >< 64) (w2w a * w2w b)', 'wide_mul_long_types=a : :word64, b : :word64', 'wide_mul_long_hypotheses=0', 'wide_mul_long_proved=T', 'wide_product_type=:word128', 'wide_slice_type=:word64', 'wide_ror_statement=∀w n. n < 64 ⇒ w ≪ (64 − n) ‖ w ⋙ n = w ⇄ n', 'wide_ror_types=w : :word64, n : :num', 'wide_ror_hypotheses=0', 'wide_ror_proved=T']

def check(text):
    if text.splitlines() != EXPECTED:
        raise ValueError("original complete arithmetic statement/type/hypothesis/kernel row drift")

def check_replay(original, probe):
    for name in ("mul_long", "ror"):
        source = re.search(r"Theorem " + name + r"\[local\]:\s*(.*?)\nProof\s*(.*?)\nQED", original, re.S)
        replay = re.search(r"val " + name + r" = prove \(``(.*?)``,\s*(.*?)\);\nval _", probe, re.S)
        if not source or not replay or any("".join(a.split()) != "".join(b.split())
                for a, b in zip(source.groups(), replay.groups())):
            raise ValueError("original literal arithmetic proof replay drift: " + name)

if __name__ == "__main__":
    check(Path(__file__).with_name("riscv_target_wide_arithmetic_probe.out").read_text())
    check_replay((ROOT / "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml").read_text(),
                 Path(__file__).with_name("riscv_target_wide_arithmetic_probeScript.sml").read_text())
    print("PASS two complete original fixed64/128 high-product/rotate proof replays, full types and zero hypotheses")
