import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("target_wide_arithmetic", ROOT / "scripts/hol-probes/check-riscv-target-wide-arithmetic.py")
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)


class TargetWideArithmeticTests(unittest.TestCase):
    def test_driver_retains_both_complete_registrations(self):
        text = (ROOT / "scripts/hol-probes/regenerate.sh").read_text()
        M.check_driver(text)
        for stem in ("riscv_target_arithmetic", "riscv_target_wide_arithmetic"):
            start = text.index("run_probe " + stem + "_probeScript.sml ")
            end = text.find("\n\n", start)
            if end == -1:
                end = len(text)
            block = text[start:end]
            label = "arithmetic_lem9_sum_type" if stem == "riscv_target_arithmetic" else "wide_slice_type"
            for changed in (text[:start] + text[end:], text + "\n" + block,
                            text.replace(label, ""), text.replace(block, block.splitlines()[0].rstrip("\\"))):
                with self.subTest(stem=stem), self.assertRaises(ValueError):
                    M.check_driver(changed)

    def test_full_original_proofs(self):
        M.check((ROOT / "scripts/hol-probes/riscv_target_wide_arithmetic_probe.out").read_text())
        M.check_replay(
            (ROOT / "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml").read_text(),
            (ROOT / "scripts/hol-probes/riscv_target_wide_arithmetic_probeScript.sml").read_text())

    def test_rejects_statement_carrier_or_hypothesis_drift(self):
        text = "\n".join(M.EXPECTED)
        for old, new in [("∀a b.", "∀a."), ("DIV", "MOD"), ("127", "126"),
                         ("word128", "word64"), ("word64", "word32"),
                         ("n < 64", "n ≤ 64"), ("64 − n", "63 − n"),
                         ("_hypotheses=0", "_hypotheses=1"), ("_proved=T", "_proved=F")]:
            with self.subTest(old=old), self.assertRaises(ValueError):
                M.check(text.replace(old, new))
        for changed in ["\n".join(M.EXPECTED[:-1]), "\n".join(reversed(M.EXPECTED)), text + "\nextra=T"]:
            with self.assertRaises(ValueError):
                M.check(changed)

    def test_rejects_altered_original_proof_replay(self):
        source = (ROOT / "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml").read_text()
        probe = (ROOT / "scripts/hol-probes/riscv_target_wide_arithmetic_probeScript.sml").read_text()
        for old, new in [("DIV", "MOD"), ("word128", "word64"), ("n < 64n", "n <= 64n"),
                         ("word_lsr_def", "word_asr_def")]:
            with self.subTest(old=old), self.assertRaises(ValueError):
                M.check_replay(source, probe.replace(old, new))


if __name__ == "__main__":
    unittest.main()
