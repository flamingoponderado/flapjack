"""Fail-closed full native target AST/byte and source partial-table evidence."""
import importlib.util
from pathlib import Path
import unittest
import re
import tempfile
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
    def test_all_source_carrier_constructors_are_observed(self):
        inventory=CHECK.check_constructor_inventory()
        # riscv-mi: the original `fp` datatype and `inst` constructor `FP` are
        # excluded (10 families/63 constructors in the full original).
        self.assertEqual(len(inventory),9)
        self.assertEqual(sum(map(len,inventory.values())),46)
        self.assertNotIn("fp",inventory)
        self.assertNotIn("FP",inventory["inst"])
        rows=CHECK.samples()
        for family,names in inventory.items():
            for name in names:
                with self.subTest(family=family,name=name):
                    remaining=[r for r in rows if not re.search(r"\b"+name+r"\b",r["hol"])]
                    with self.assertRaises(ValueError):CHECK.check_constructor_inventory(remaining)
    def test_every_operator_reg_imm_mode_is_required(self):
        rows=CHECK.samples()
        inventory=CHECK.source_inventory()
        for constructor,family in [("Binop","binop"),("Shift","shift"),("JumpCmp","cmp")]:
            for op in inventory[family]:
                for mode in ["Reg","Imm"]:
                    with self.subTest(constructor=constructor,op=op,mode=mode):
                        remaining=[r for r in rows if not all(re.search(r"\b"+n+r"\b",r["hol"]) for n in [constructor,op,mode])]
                        with self.assertRaises(ValueError):CHECK.check_constructor_inventory(remaining)
    def test_lean_sample_or_commented_hol_constructor_cannot_fill_gap(self):
        rows=CHECK.samples()
        for changed in [
            [dict(r,lean=r["lean"].replace(".load32",".load16")) for r in rows],
            [r for r in rows if r["group"]!="Call"]+[dict(rows[0],hol="Inst Skip (* Call (* nested *) *)")]]:
            with self.assertRaises(ValueError):CHECK.check_constructor_inventory(changed)
    def source_root(self,directory):
        root=Path(directory)
        paths={p for _,p in CHECK.CARRIER_SOURCES.values()}
        paths.update(["cakeml/compiler/encoders/asm/asmScript.sml","cakeml/semantics/astScript.sml",
                      "scripts/hol-probes/l3_target_encoder_probeScript.sml"])
        for name in paths:
            p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text((ROOT/name).read_text())
        return root
    def test_source_lean_carrier_drift(self):
        for old,new in [("| store32","| store32Extra"),("abbrev HolMemop := Flapjack.WordMemOp","abbrev HolMemop := Flapjack.WordMemOp\nabbrev HolFp := WordLangFp"),
                        ("  | mem (operator : HolMemop) (destination : Nat) (address : HolAddr width)\n","  | mem (operator : HolMemop) (destination : Nat) (address : HolAddr width)\n  | fp (operation : Nat)\n")]:
            with self.subTest(old=old),tempfile.TemporaryDirectory() as directory:
                root=self.source_root(directory)
                name="Flapjack/MemOp.lean" if old.startswith("|") else "Flapjack/Compiler/Encoders/Asm.lean"
                p=root/name;text=p.read_text();self.assertIn(old,text);p.write_text(text.replace(old,new,1))
                with self.assertRaises(ValueError):CHECK.check_constructor_inventory(root=root)
    def test_new_matching_original_and_lean_constructor_requires_observation(self):
        with tempfile.TemporaryDirectory() as directory:
            root=self.source_root(directory)
            p=root/"cakeml/compiler/encoders/asm/asmScript.sml"
            p.write_text(p.read_text().replace("asm = Inst ('a inst)", "asm = Custom num | Inst ('a inst)",1))
            p=root/"Flapjack/Compiler/Encoders/Asm.lean"
            p.write_text(p.read_text().replace("inductive HolAsm (width : Nat) [NeZero width] where",
                                            "inductive HolAsm (width : Nat) [NeZero width] where\n  | custom (value : Nat)",1))
            with self.assertRaisesRegex(ValueError,"missing native constructor observations"):
                CHECK.check_constructor_inventory(root=root)
    def test_original_probe_sample_input_drift(self):
        with tempfile.TemporaryDirectory() as directory:
            root=self.source_root(directory)
            p=root/"scripts/hol-probes/l3_target_encoder_probeScript.sml"
            p.write_text(p.read_text().replace("riscv_ast (Inst Skip)","riscv_ast (Inst (Const 0 0w))",1))
            with self.assertRaises(ValueError):CHECK.check_probe_samples(root=root)
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
