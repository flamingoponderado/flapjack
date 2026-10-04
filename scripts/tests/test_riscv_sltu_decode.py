"""Regression mutations for full original register comparison guard/effect/evidence preservation."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("sltu_decode_guard", ROOT / "scripts/hol-probes/check-riscv-sltu-decode.py")
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)

class SltuDecodeGuard(unittest.TestCase):
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

    def test_no_extra_register_guard(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/DecodeSltu.lean', '(rd rs1 rs2 : BitVec 5) :', '(rd rs1 rs2 : BitVec 5) (h : rd ≠ 0#5) :')

    def test_intrinsic_register_width_preserved(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/DecodeSltu.lean', '(rd rs1 rs2 : BitVec 5)', '(rd rs1 rs2 : BitVec 4)')

    def test_register_order_preserved(self):
        self.mutate('Flapjack/RiscV/CorrectnessEncoding/DecodeSltu.lean', '.SLTU (rd, rs1, rs2)', '.SLTU (rd, rs2, rs1)')

    def test_full_universal_hol_proof_capture(self):
        self.mutate('scripts/hol-probes/riscv_sltu_decode_probe.out', 'sltu_decode_hypotheses=0', 'sltu_decode_hypotheses=1')

    def test_false_original_high_bit(self):
        self.mutate('scripts/hol-probes/riscv_sltu_decode_probe.out', 'sltu_decode_high_bit=T', 'sltu_decode_high_bit=F')

    def test_missing_universal_evidence(self):
        self.mutate('scripts/hol-probes/regenerate.sh', 'sltu_decode_universal', '')

if __name__ == '__main__':
    unittest.main()
