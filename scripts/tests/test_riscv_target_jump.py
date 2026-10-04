"""Regression mutations for full original Jump guard/effect/evidence preservation."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("full_jump_guard", ROOT / "scripts/hol-probes/check-riscv-target-jump.py")
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)

class FullJumpGuard(unittest.TestCase):
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
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/Jump.lean', '(c : BitVec 64)', '(c : BitVec 64) (near : c.toInt ≤ 1048575)', after_marker='theorem riscv_encoder_correct_jump')

    def test_no_assumed_target_poststate(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/Jump.lean', '(ms : riscv_state)', '(ms : riscv_state) (desired : targetStateRel riscvTarget s2 ms)', after_marker='theorem riscv_encoder_correct_jump')

    def test_all_original_environments_retained(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/Jump.lean', '∀ env : Nat → riscv_state → riscv_state,', '∃ env : Nat → riscv_state → riscv_state,', after_marker='theorem riscv_encoder_correct_jump')

    def test_code_byte_equality_retained(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/Jump.lean', "riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc", 'True', after_marker='theorem riscv_encoder_correct_jump')

    def test_outside_domain_assertion_retained(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/Jump.lean', '¬ s1.memDomain x', 's1.memDomain x', after_marker='theorem riscv_encoder_correct_jump')

    def test_actual_original_hypotheses_capture(self):
        self.mutate('scripts/hol-probes/riscv_target_jump_probe.out', 'riscv_encoder_correct_jump_hypotheses=0', 'riscv_encoder_correct_jump_hypotheses=1')

    def test_full_carrier_evidence_registered(self):
        self.mutate('scripts/hol-probes/regenerate.sh', 'riscv_encoder_correct_jump_types', '')

    def test_actual_auipc_prefix_retained(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/Jump/Far.lean', 'let a := riscvEncode (.ArithI (.AUIPC (31#5,high c)))', 'let a := ([] : List (BitVec 8))')

    def test_original_scratch_projection_retained(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/Jump/Far.lean', 'fun p : RiscVProjection => p.2.2.2.2.1', 'fun p : RiscVProjection => p.2.2.2.2.2')

    def test_original_arithmetic_shift_retained(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/Jump/Near.lean', 'c.sshiftRight 1', 'c >>> (1 : Nat)')

if __name__ == '__main__':
    unittest.main()
