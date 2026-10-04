"""Regression mutations for full original JumpCmp guard/effect/evidence preservation."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("full_jumpcmp_guard", ROOT / "scripts/hol-probes/check-riscv-target-jumpcmp.py")
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)

class FullJumpCmpGuard(unittest.TestCase):
    def fixture(self, directory):
        root = Path(directory)
        for name in [*guard.CHECKS, "scripts/hol-probes/regenerate.sh"]:
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes((ROOT / name).read_bytes())
        return root

    def mutate(self, name, before, after, after_marker=None):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory)
            path = root / name
            text = path.read_text()
            self.assertIn(before, text)
            if after_marker is None:
                path.write_text(text.replace(before, after, 1))
            else:
                prefix, rest = text.split(after_marker, 1)
                self.assertIn(before, rest)
                path.write_text(prefix + after_marker + rest.replace(before, after, 1))
            with self.assertRaises(ValueError):
                guard.check(root)

    def test_complete_original(self):
        self.assertTrue(guard.check())

    def test_no_added_near_range_premise(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp.lean', '(a : BitVec 64)', '(a : BitVec 64) (near : a.toInt ≤ 4095)', after_marker='theorem riscv_encoder_correct_jumpCmp')

    def test_no_assumed_target_poststate(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp.lean', '(ms : riscv_state)', '(ms : riscv_state) (desired : targetStateRel riscvTarget s2 ms)', after_marker='theorem riscv_encoder_correct_jumpCmp')

    def test_all_original_environments_retained(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp.lean', '∀ env : Nat → riscv_state → riscv_state,', '∃ env : Nat → riscv_state → riscv_state,', after_marker='theorem riscv_encoder_correct_jumpCmp')

    def test_code_byte_equality_retained(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp.lean', "riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc", 'True', after_marker='theorem riscv_encoder_correct_jumpCmp')

    def test_outside_domain_assertion_retained(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/JumpCmp.lean', '¬ s1.memDomain x', 's1.memDomain x', after_marker='theorem riscv_encoder_correct_jumpCmp')

    def test_actual_original_hypotheses_capture(self):
        self.mutate('scripts/hol-probes/riscv_target_jumpcmp_probe.out', 'riscv_encoder_correct_jumpcmp_hypotheses=0', 'riscv_encoder_correct_jumpcmp_hypotheses=1')

    def test_full_carrier_evidence_registered(self):
        self.mutate('scripts/hol-probes/regenerate.sh', 'riscv_encoder_correct_jumpcmp_types', '')
