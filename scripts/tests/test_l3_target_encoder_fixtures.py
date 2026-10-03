"""Fail-closed full native target AST/byte and source partial-table evidence."""
import importlib.util
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[2]
SPEC=importlib.util.spec_from_file_location('target_encoder_check',ROOT/'scripts/l3/check-target-encoder-fixtures.py')
CHECK=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(CHECK)
class TargetEncoderCapture(unittest.TestCase):
    def setUp(self):self.text=(ROOT/'scripts/hol-probes/l3_target_encoder_probe.out').read_text()
    def test_full_capture_and_fixture(self):
        self.assertEqual(len(CHECK.samples()),300)
        self.assertEqual(len(CHECK.capture(self.text)),600)
        self.assertEqual(CHECK.fixture(self.text),(ROOT/'Flapjack/Test/RiscVNativeTargetParity.lean').read_text())
    def test_constructor_modes_and_boundaries(self):
        rows=CHECK.samples();groups={r['group'] for r in rows}
        self.assertEqual(groups,{'Skip','Const','BinopReg','BinopImm','ShiftReg','ShiftImm','Div','LongMul','LongDiv','AddCarry','AddOverflow','SubOverflow','Mem','FP','Jump','JumpCmpReg','JumpCmpImm','Call','JumpReg','Loc'})
        self.assertEqual(sum(r['group']=='FP' for r in rows),16)
        self.assertEqual(sum(r['group'].startswith('JumpCmp') for r in rows),128)
        self.assertTrue(any('18446744073709551615w' in r['hol'] and r['group']=='ShiftImm' for r in rows))
    def test_missing_extra_reordered_rows(self):
        rows=self.text.splitlines();n=len(CHECK.HEADERS)
        for mutated in [rows[:-1],rows+[rows[-1]],rows[:n]+[rows[n+1],rows[n]]+rows[n+2:]]:
            with self.assertRaises(ValueError):CHECK.capture('\n'.join(mutated))
    def test_partial_helpers_and_original_type(self):
        for old,new in [('bop_i_undefined=riscv_bop_i Sub','bop_i_undefined=ADDI'),('sh_undefined=riscv_sh Ror','sh_undefined=SLLI'),('riscv_ast_type=:64 asm','riscv_ast_type=:32 asm'),('riscv_ast_hypotheses=0','riscv_ast_hypotheses=1')]:
            with self.subTest(old=old),self.assertRaises(ValueError):CHECK.capture(self.text.replace(old,new))
    def test_unreduced_ast_and_bytes(self):
        row=CHECK.capture(self.text);ast=row['Target_Skip_0_ast']
        for mutated in [ast.replace('"n2w"','"Encode"'),ast.replace('(ty "riscv" "instruction")','(ty "riscv" "rawInstType")')]:
            with self.assertRaises(ValueError):CHECK.ast_term(mutated)
        for value in ['[256]','[word_extract w]','[1;2;]','[~1]']:
            with self.assertRaises(ValueError):CHECK.byte_values(value)
    def test_byte_or_ast_drift_changes_kernel_fixture(self):
        original=CHECK.fixture(self.text)
        self.assertNotEqual(original,CHECK.fixture(self.text.replace('Target_Skip_0_bytes=[19;0;0;0]','Target_Skip_0_bytes=[20;0;0;0]')))
