"""Regression mutations for full original AddCarry guard/effect/evidence preservation."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("asm_ok_guard", ROOT / "scripts/hol-probes/check-riscv-asm-ok-rewrites.py")
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)

class FullAsmOkGuard(unittest.TestCase):
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

    def test_no_added_source_alias_premise(self):
        self.mutate('Flapjack/Compiler/Encoders/RiscV/Target/AsmOkRewrites.lean',
                    '(r r1 r2 r3 r4 r5 d d1 d2 d3 : Nat)',
                    '(r r1 r2 r3 r4 r5 d d1 d2 d3 : Nat) (extra : r1 ≠ r2)')

    def test_strict_sub_lower_bound(self):
        self.mutate('Flapjack/Compiler/Encoders/RiscV/Target/AsmOkRewrites.lean',
                    'if b = .sub then (-2048 : BitVec 64).toInt < w.toInt',
                    'if b = .sub then (-2048 : BitVec 64).toInt ≤ w.toInt')

    def test_all_memory_forms(self):
        self.mutate('Flapjack/Compiler/Encoders/RiscV/Target/AsmOkRewrites.lean',
                    '.mem .load16 r1', '.mem .load8 r1')

    def test_fp_fma_rejection(self):
        self.mutate('Flapjack/Compiler/Encoders/RiscV/Target/AsmOkRewrites.lean',
                    '(.inst (.fp (.fpFma d1 d2 d3))) riscvConfig = true ↔ False',
                    '(.inst (.fp (.fpFma d1 d2 d3))) riscvConfig = true ↔ True')

    def test_cjump_exact_lower_endpoint(self):
        self.mutate('Flapjack/Compiler/Encoders/RiscV/Target/AsmOkRewrites.lean',
                    '(-1048576+8 : BitVec 64)', '(-1048576 : BitVec 64)')

    def test_original41_conjunct_count(self):
        self.mutate('scripts/hol-probes/riscv_asm_ok_rewrites_probe.out',
                    'riscv_asm_ok_full_conjuncts=41', 'riscv_asm_ok_full_conjuncts=40')

    def test_actual_zero_hypotheses(self):
        self.mutate('scripts/hol-probes/riscv_asm_ok_rewrites_probe.out',
                    'riscv_asm_ok_full_hypotheses=0', 'riscv_asm_ok_full_hypotheses=1')

    def test_full_carriers_registered(self):
        self.mutate('scripts/hol-probes/regenerate.sh', 'riscv_asm_ok_full_types', '')

if __name__ == '__main__':
    unittest.main()
