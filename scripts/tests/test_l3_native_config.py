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
    def test_lean_complete_config_drift(self):
        lean=(ROOT / CHECK.LEAN_PATH).read_text()
        changes=[
            ("AsmConfigExact 64", "AsmConfigExact 32"),
            ("isa := .riscv", "isa := .armv8"),
            ("encode := riscvEnc", "encode := fun _ => []"),
            ("regCount := 32", "regCount := 31"),
            ("avoidRegs := [0,2,3,4,31]", "avoidRegs := [0,2,3,4]"),
            ("fpRegCount := 0", "fpRegCount := 1"),
            ("linkReg := some 1", "linkReg := none"),
            ("twoRegArith := false", "twoRegArith := true"),
            ("bigEndian := false", "bigEndian := true"),
            ("(-2048 : BitVec 64).slt i", "(-2048 : BitVec 64).sle i"),
            ("(-2048 : BitVec 64).sle i", "(-2048 : BitVec 64).ult i"),
            ("i.sle 2047", "i.sle 2048"),
            ("addrOffset := (-2048,2047)", "addrOffset := (-2047,2047)"),
            ("hwOffset := (-2048,2047)", "hwOffset := (-2048,2048)"),
            ("byteOffset := (-2048,2047)", "byteOffset := (0,2047)"),
            ("jumpOffset := (-2147483648,0x7FFFF7FF)", "jumpOffset := (-2147483648,0x7FFFFFFF)"),
            ("cjumpOffset := (-1048576+8,1048575+4)", "cjumpOffset := (-1048576,1048575)"),
            ("locOffset := (-2147483648,0x7FFFF7FF)", "locOffset := (-2147483648,0x7FFFFFFF)"),
            ("codeAlignment := 2", "codeAlignment := 1"),
            ("def riscvConfig :", "def riscvConfig (assumed : True) :")]
        for old,new in changes:
            with self.subTest(old=old):
                self.assertIn(old,lean)
                with self.assertRaises(ValueError):CHECK.check(self.text,lean.replace(old,new,1))
    def test_lean_comments_formatting_and_unrelated_proof(self):
        lean=(ROOT / CHECK.LEAN_PATH).read_text()
        changed=lean.replace("encode := riscvEnc", "encode /- nested /- note -/ -/ := riscvEnc")
        changed=changed.replace("[0,2,3,4,31]", "[0, 2, 3, 4, 31]")
        changed=changed.replace(":= rfl", ":= by rfl")
        CHECK.check(self.text,changed)
    def test_commented_baseline_and_duplicate_do_not_mask_drift(self):
        lean=(ROOT / CHECK.LEAN_PATH).read_text()
        expected=CHECK.LEAN_EXPECTED["riscvConfig"]
        for changed in ["/- "+expected+" -/\n"+lean.replace("codeAlignment := 2","codeAlignment := 1"),
                        lean+"\n"+expected]:
            with self.assertRaises(ValueError):CHECK.check(self.text,changed)
    def test_missing_reordered_duplicate_policy(self):
        rows=[x for x in self.text.splitlines() if x]
        for changed in [rows[:-1],rows+[rows[-1]],rows[:25]+list(reversed(rows[25:]))]:
            with self.assertRaises(ValueError):CHECK.check('\n'.join(changed))
