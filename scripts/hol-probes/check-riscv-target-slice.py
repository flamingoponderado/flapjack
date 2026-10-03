#!/usr/bin/env python3
"""Complete original lem6 replay guard; not cross-language equivalence."""
from pathlib import Path
import re
import shlex
ROOT = Path(__file__).resolve().parents[2]
EXPECTED = ["slice_statement=∀c. ((31 >< 0) c ' 11 ⇔ c ' 11) ∧ ((63 >< 32) c ' 11 ⇔ c ' 43) ∧ ((¬(63 >< 32) c) ' 11 ⇔ ¬c ' 43)", 'slice_types=c : :word64', 'slice_hypotheses=0', 'slice_proved=T']

def check(text, original, probe, driver):
    if text.splitlines() != EXPECTED:
        raise ValueError("full slice statement/type/hypothesis/proof drift")
    pattern = r"val lem6 = blastLib.BBLAST_PROVE\s*``(.*?)``"
    a, b = re.search(pattern, original, re.S), re.search(pattern, probe, re.S)
    if not a or not b or "".join(a[1].split()) != "".join(b[1].split()):
        raise ValueError("literal original slice proof replay drift")
    commands = [shlex.split(line) for line in driver.replace("\\\n", " ").splitlines()
                if line.startswith("run_probe riscv_target_slice_probeScript.sml ")]
    expected = ["run_probe", "riscv_target_slice_probeScript.sml", "riscv_target_slice_probe.out"] + [
        row.split("=", 1)[0] for row in EXPECTED] + [
        "$cake_dir/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml",
        "$cake_dir/compiler/encoders/riscv/proofs"]
    if commands != [expected]:
        raise ValueError("missing/duplicate/incomplete slice replay registration")

if __name__ == "__main__":
    check(Path(__file__).with_name("riscv_target_slice_probe.out").read_text(),
          (ROOT / "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml").read_text(),
          Path(__file__).with_name("riscv_target_slice_probeScript.sml").read_text(),
          Path(__file__).with_name("regenerate.sh").read_text())
    print("PASS full original three-conjunct slice theorem, literal replay and complete driver")
