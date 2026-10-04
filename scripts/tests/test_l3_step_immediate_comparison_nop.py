import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('comparison_guard', ROOT / 'scripts/hol-probes/check-l3-step-immediate-comparison-nop.py')
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)
class ComparisonGuard(unittest.TestCase):
    def mutate(self, name, old, new):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for path in list(guard.CHECKS) + [guard.MODULE] + ['scripts/hol-probes/regenerate.sh']:
                p = root / path
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_bytes((ROOT / path).read_bytes())
            p = root / name
            text = p.read_text()
            self.assertIn(old, text)
            p.write_text(text.replace(old, new))
            with self.assertRaises(ValueError):
                guard.check(root)
    def test_original(self):
        self.assertTrue(guard.check())
    def test_narrowed_mode_premise(self):
        self.mutate('Flapjack/RiscV/L3/Step/ImmediateComparisonNop.lean',
                    '(arch : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2)',
                    '(arch : (s.c_MCSR s.procID).mcpuid.ArchBase = 2#2)')
    def test_wrong_original_hypothesis_count(self):
        self.mutate('scripts/hol-probes/l3_step_immediate_comparison_nop_probe.out',
                    'slti_nop_source_hypotheses=2', 'slti_nop_source_hypotheses=1')
    def test_dropped_destination_hypothesis(self):
        self.mutate(guard.MODULE, '(h : rd = 0#5)', '')
    def test_changed_result(self):
        self.mutate(guard.MODULE, '(rd, rs1, imm) s = s', '(rd, rs1, imm) s = {s with c_PC := fun _ => 0#64}')
    def test_missing_typed_sentinel(self):
        self.mutate('scripts/hol-probes/regenerate.sh', 'sltiu_nop_types', '')
if __name__ == '__main__':
    unittest.main()
