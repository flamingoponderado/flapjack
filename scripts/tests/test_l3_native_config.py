"""Reject source native-config omissions and fabricated empty encoder fields."""
import importlib.util
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[2]
SPEC=importlib.util.spec_from_file_location('native_config_check',ROOT/'scripts/hol-probes/check-l3-native-config.py')
CHECK=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(CHECK)
class NativeConfig(unittest.TestCase):
    def setUp(self):self.text=(ROOT/'scripts/hol-probes/l3_native_config_probe.out').read_text()
    def test_original_full_config(self):
        CHECK.check(self.text)
        self.assertEqual(len(CHECK.EXPECTED),103)
        self.assertEqual(sum(x.startswith('cfg_imm_') for x in CHECK.EXPECTED),78)
    def test_type_whole_encoder_and_bound_policy_drift(self):
        for old,new in [(':64 asm_config',':32 asm_config'),('encode := riscv_enc','encode := (λx. [])'),('riscv_config.encode = riscv_enc','riscv_config.encode = (λx. [])'),('cfg_imm_Sub_1=F','cfg_imm_Sub_1=T')]:
            with self.subTest(old=old),self.assertRaises(ValueError):CHECK.check(self.text.replace(old,new))
    def test_missing_reordered_duplicate_policy(self):
        rows=[x for x in self.text.splitlines() if x]
        for changed in [rows[:-1],rows+[rows[-1]],rows[:25]+list(reversed(rows[25:]))]:
            with self.assertRaises(ValueError):CHECK.check('\n'.join(changed))
