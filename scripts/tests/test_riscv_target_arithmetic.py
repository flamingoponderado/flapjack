import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("target_arithmetic", ROOT / "scripts/hol-probes/check-riscv-target-arithmetic.py")
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)


class TargetArithmeticTests(unittest.TestCase):
    def test_complete_original_kernel_replays(self):
        M.check((ROOT / "scripts/hol-probes/riscv_target_arithmetic_probe.out").read_text())
        M.check_replay(
            (ROOT / "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml").read_text(),
            (ROOT / "scripts/hol-probes/riscv_target_arithmetic_probeScript.sml").read_text())

    def test_rejects_statement_type_and_proof_drift(self):
        text = "\n".join(M.EXPECTED)
        for old, new in [("aligned 2", "aligned 1"), ("¬c ' 1", "¬c ' 0"),
                         ("∀y x b.", "∀x b."), ("x ∨ y", "x ∧ y"),
                         ("word64", "word32"), ("r2 r3.", "r2."),
                         ("w2n r3 + 1", "w2n r3 + 2"), ("≤₊", "≤"),
                         ("_hypotheses=0", "_hypotheses=1"), ("_proved=T", "_proved=F")]:
            with self.subTest(old=old), self.assertRaises(ValueError):
                M.check(text.replace(old, new))
        for changed in ["\n".join(M.EXPECTED[:-1]), "\n".join(reversed(M.EXPECTED)), text + "\nextra=T"]:
            with self.assertRaises(ValueError):
                M.check(changed)

    def test_rejects_changed_source_replay(self):
        original = (ROOT / "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml").read_text()
        probe = (ROOT / "scripts/hol-probes/riscv_target_arithmetic_probeScript.sml").read_text()
        for old, new in [("aligned 2", "aligned 1"), ("x \\/ y", "x /\\ y"),
                         ("w2n r3 + 1", "w2n r3 + 2"), ("word_ls_n2w", "word_lo_n2w")]:
            with self.subTest(old=old), self.assertRaises(ValueError):
                M.check_replay(original, probe.replace(old, new))


if __name__ == "__main__":
    unittest.main()
