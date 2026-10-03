"""AMO coverage cleanup must retain each distinct destination alias row."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('amo_alias_guard',ROOT/'scripts/hol-probes/check-l3-amo-alias-replays.py')
guard=importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)
class AliasReplay(unittest.TestCase):
    def fixture(self,directory):
        root=Path(directory)
        for name in {r[i] for r in guard.CASES.values() for i in (0,2)}:
            path=root/name
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_text((ROOT/name).read_text())
        return root
    def test_all_instruction_aliases(self):
        self.assertEqual(len(guard.CASES),48)
        self.assertTrue(guard.check())
    def test_missing_rd0_replay(self):
        with tempfile.TemporaryDirectory() as directory:
            root=self.fixture(directory)
            p=root/'Flapjack/Test/L3AMOArithmeticParity.lean'
            p.write_text(p.read_text().replace('-- Original amoxor_w_aligned_rd0;', '-- Original renamed;'))
            with self.assertRaises(ValueError): guard.check(root)
    def test_address_alias_changed_to_rs2(self):
        with tempfile.TemporaryDirectory() as directory:
            root=self.fixture(directory)
            p=root/'Flapjack/Test/L3AMOMinMaxParity.lean'
            text=p.read_text();start=text.index('-- Original amomax_d_aligned_rd2;')
            text=text[:start]+text[start:].replace('0 0 2 2 3','0 0 3 2 3',1)
            p.write_text(text)
            with self.assertRaises(ValueError): guard.check(root)
    def test_changed_original_memory_result(self):
        with tempfile.TemporaryDirectory() as directory:
            root=self.fixture(directory)
            p=root/'scripts/hol-probes/l3_amo_minmax_probe.out'
            p.write_text(p.read_text().replace('amomax_w_aligned_rd0=', 'amomax_w_aligned_rd0=(0,'))
            with self.assertRaises(ValueError): guard.check(root)
if __name__=='__main__': unittest.main()
