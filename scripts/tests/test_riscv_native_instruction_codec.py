import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

class NativeInstructionCodecTests(unittest.TestCase):
    def test_exhaustive_production_cases(self):
        model = (ROOT / "Flapjack/RiscV/Model.lean").read_text().split("inductive Instruction (width : Nat) where", 1)[1].split("deriving DecidableEq, Repr", 1)[0]
        codec = (ROOT / "Flapjack/RiscV/Encoding/NativeInstruction.lean").read_text().split("def nativeInstruction :", 1)[1].split("/-- Universal byte-order", 1)[0]
        expected = re.findall(r"^  \| (\w+)", model, re.M)
        actual = re.findall(r"^  \| \.(\w+)", codec, re.M)
        self.assertEqual(actual, expected)
        self.assertEqual(len(set(actual)), len(actual))
        self.assertNotIn("| _", codec)
        self.assertNotIn("holArb", codec)

    def test_all_constructor_kernel_regressions(self):
        codec = (ROOT / "Flapjack/RiscV/Encoding/NativeInstruction.lean").read_text()
        names = re.findall(r"^  \| \.(\w+)", codec, re.M)
        tests = (ROOT / "Flapjack/Test/RiscVNativeInstructionParity.lean").read_text()
        for name in names:
            self.assertEqual(len(re.findall(r"example : encodeInstruction \(width := 64\) \(Instruction\." + name + r"[ )]", tests)), 3, name)
        self.assertEqual(tests.count(":= by decide"), 3 * len(names))
        for opcode in ["SB", "SH", "SW", "SD"]:
            self.assertIn(".Store (." + opcode + " (nativeRegister a, nativeRegister d,", codec)
        self.assertNotIn("@[hol", codec)

if __name__ == "__main__":
    unittest.main()
