"""Full native Encode capture, carrier coverage and fixture drift guards."""
import importlib.util
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[2]
SPEC=importlib.util.spec_from_file_location("encode_check", ROOT / "scripts/l3/check-encode-fixtures.py")
CHECK=importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)
class EncodeCapture(unittest.TestCase):
    def setUp(self):
        self.text=(ROOT / "scripts/hol-probes/l3_encode_probe.out").read_text()
    def test_whole_capture_and_kernel_fixture(self):
        CHECK.check_inventory((ROOT / "Flapjack/RiscV/L3/Types.lean").read_text())
        self.assertEqual(len(CHECK.CLAUSES),163)
        self.assertEqual(len(CHECK.parse(self.text)),634)
        self.assertEqual(CHECK.fixture(self.text),(ROOT / "Flapjack/Test/L3EncodeParity.lean").read_text())
    def test_missing_reordered_duplicate_unreduced_out_of_range(self):
        rows=self.text.splitlines()
        variants=[rows[:-1],rows+[rows[-1]],rows[:20]+[rows[21],rows[20]]+rows[22:],
                  rows[:20]+[rows[20].split('=')[0]+'=w2n (Encode i)']+rows[21:],
                  rows[:20]+[rows[20].split('=')[0]+'=4294967296']+rows[21:]]
        for variant in variants:
            with self.subTest(variant=variant[20]),self.assertRaises(ValueError):
                CHECK.parse('\n'.join(variant))
    def test_original_carrier_and_hypotheses(self):
        for old,new in [('word32','word64'),('Encode_hypotheses=0','Encode_hypotheses=1')]:
            with self.subTest(old=old),self.assertRaises(ValueError):CHECK.parse(self.text.replace(old,new))
    def test_riscv_mi_exclusions_are_exact(self):
        source=(ROOT / "Flapjack/RiscV/L3/Types.lean").read_text()
        # Restoring an excluded original clause is drift, not silent coverage.
        restored=source.replace('  | EBREAK\n  | ECALL\n','  | EBREAK\n  | ECALL\n  | WFI\n',1)
        self.assertNotEqual(restored,source)
        with self.assertRaises(ValueError):CHECK.check_inventory(restored)
        self.assertNotIn('Encode_FADD_S_0',CHECK.fixture(self.text))
        self.assertNotIn('Encode_MULW_0',CHECK.fixture(self.text))
        self.assertIn('Encode_ADDIW_0',CHECK.fixture(self.text))
        self.assertEqual(len(CHECK.retained_clauses()),55)
    def test_payload_width_and_missing_constructor(self):
        source=(ROOT / "Flapjack/RiscV/L3/Types.lean").read_text()
        for mutated in [source.replace('  | UnknownInstruction\n',''),source.replace('FETCH_FAULT (a0 : (BitVec 64))','FETCH_FAULT (a0 : (BitVec 32))')]:
            with self.assertRaises(ValueError):CHECK.check_inventory(mutated)
    def test_original_zero_encodings_and_numeric_drift(self):
        data=CHECK.parse(self.text)
        self.assertEqual(data['Encode_UnknownInstruction_0'],0)
        for ctor in ['FETCH_FAULT','FETCH_MISALIGNED']:
            for profile in range(4):self.assertEqual(data[f'Encode_{ctor}_{profile}'],0)
        # Mutate the first observation retained by riscv-mi; excluded clauses
        # are captured but intentionally not replayed.
        first=next(row for row in self.text.splitlines() if row.startswith('Encode_ADDI_0='))
        modified=self.text.replace(first,first.split('=')[0]+'=1')
        self.assertNotEqual(CHECK.fixture(modified),CHECK.fixture(self.text))
