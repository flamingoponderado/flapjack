import importlib.util
import re
import unittest
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("helper_links", ROOT / "scripts/hol-probes/check-riscv-target-helper-links.py")
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)

class TargetHelperLinkTests(unittest.TestCase):
    def test_original_universal_helper_statements(self):
        M.check((ROOT / "scripts/hol-probes/riscv_target_helper_links_probe.out").read_text())

    def test_rejects_narrowing_and_unspecified_slot_fabrication(self):
        for old, new in [("∀b r1 r2 i.", "∀r1 r2 i."), ("if b = Sub", "if b = Add"),
                         ("_hypotheses=0", "_hypotheses=1"), ("_proved=T", "_proved=F"),
                         ("riscv_sh sh", "SLLI"), ("riscv_shv sh", "SLL")]:
            with self.subTest(old=old), self.assertRaises(ValueError):
                M.check("\n".join(M.EXPECTED).replace(old,new))

    def test_all_non_encode_fields_are_related(self):
        source = (ROOT / "Flapjack/Compiler/Encoders/Asm.lean").read_text()
        carrier = source.split("structure AsmConfig (width : Nat) where",1)[1].split("\n\n",1)[0]
        carrier = re.sub(r"/--.*?-/", "", carrier, flags=re.S)
        fields = re.findall(r"^  (\w+) :",carrier,re.M)
        relation = (ROOT / "Flapjack/Compiler/Encoders/RiscV/Target/HelperLinks.lean").read_text()
        theorem = relation.split("theorem riscvConfig_checks_projections :",1)[1].split(":= by",1)[0]
        actual = re.findall(r"riscvConfigForChecks\.(\w+) = riscvConfig\.(\w+)",theorem)
        self.assertEqual(actual, [(field,field) for field in ["isa","regCount","avoidRegs","fpRegCount","linkReg","twoRegArith","bigEndian","validImm","addrOffset","hwOffset","byteOffset","jumpOffset","cjumpOffset","locOffset","codeAlignment"]])
        self.assertEqual({a for a,b in actual},set(fields)-{"encode"})
        self.assertNotIn("@[hol", relation)

if __name__ == "__main__":
    unittest.main()
