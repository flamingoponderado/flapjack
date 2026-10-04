"""Negative drift checks, not a HOL-to-Lean equivalence proof."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("complete_guard", ROOT / "scripts/hol-probes/check-riscv-target-complete.py")
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)

class CompleteEncoderTests(unittest.TestCase):
    def mutate(self, name, old, new):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for source in [*guard.CHECKS, "scripts/hol-probes/regenerate.sh"]:
                p = root / source
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text((ROOT / source).read_text())
            p = root / name
            text = p.read_text()
            self.assertIn(old, text)
            p.write_text(text.replace(old, new, 1))
            with self.assertRaises(ValueError):
                guard.check(root)
    def test_original(self):
        self.assertTrue(guard.check())
    def test_no_target_execution_premise(self):
        self.mutate("Flapjack/RiscV/CorrectnessEncoding/Complete.lean",
                    ": encoderCorrect riscvTarget", "(assumed : encoderCorrect riscvTarget) : encoderCorrect riscvTarget")
    def test_all_environment_retained(self):
        self.mutate("Flapjack/Compiler/Encoders/AsmProps/EncoderCorrect.lean",
                    "∀ env : Nat → β → β", "∃ env : Nat → β → β")
    def test_full_target_ok_retained(self):
        self.mutate("Flapjack/Compiler/Encoders/AsmProps/EncoderCorrect.lean", "targetOk t ∧", "True ∧")
    def test_second_assertion_retained(self):
        self.mutate("Flapjack/Compiler/Encoders/AsmProps/EncoderCorrect.lean", "asserts2 (n + 1)", "asserts2 n")
    def test_original_hypotheses(self):
        self.mutate("scripts/hol-probes/riscv_target_complete_probe.out",
                    "riscv_encoder_correct_hypotheses=0", "riscv_encoder_correct_hypotheses=1")
    def test_original_full_expansion(self):
        self.mutate("scripts/hol-probes/riscv_target_complete_probe.out",
                    "riscv_encoder_correct_expanded=", "omitted_expansion=")
    def test_required_registration(self):
        self.mutate("scripts/hol-probes/regenerate.sh",
                    "riscv_encoder_correct_statement riscv_encoder_correct_expanded riscv_encoder_correct_hypotheses riscv_encoder_correct_proved",
                    "riscv_encoder_correct_statement riscv_encoder_correct_hypotheses riscv_encoder_correct_proved")

if __name__ == "__main__":
    unittest.main()
