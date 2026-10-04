"""Regression contracts for original expanded memory instruction ports."""
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HOL = "HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml"


def statement(source, name):
    match = re.search(r"theorem " + name + r"\b([\s\S]*?) := by", source)
    if match is None:
        raise ValueError("missing public theorem " + name)
    return match.group(1)


class ExpandedMemoryTests(unittest.TestCase):
    def test_load_conclusions(self):
        source = (ROOT / "Flapjack/RiscV/L3/Step/LoadStep.lean").read_text()
        for op, count in [("LD", 8), ("LW", 4), ("LH", 2), ("LB", 1),
                          ("LWU", 4), ("LHU", 2), ("LBU", 1)]:
            with self.subTest(op=op):
                stmt = statement(source, "dfn" + op)
                conclusion = stmt.split(" : «dfn'", 1)[1]
                self.assertNotIn("rawReadData", conclusion)
                self.assertEqual(conclusion.count("s.MEM8"), count)
                self.assertEqual(conclusion.count("++"), count - 1)
                self.assertIn("hrd : rd ≠ 0", stmt)
                self.assertIn("mstatus.VM = 0#5", stmt)
                self.assertEqual("haligned :" in stmt, count != 1)
                self.assertEqual(stmt.count("mcpuid.ArchBase ≠"), 2 if op in ("LD", "LWU") else 0)
                self.assertIn('@[hol "' + HOL + '" "' + op + '"]\ntheorem dfn' + op + ' ', source)
                self.assertNotIn('@[hol "' + HOL + '" "' + op + '"]\ntheorem dfn' + op + 'Raw', source)

    def test_store_conclusions(self):
        source = (ROOT / "Flapjack/RiscV/L3/Step/StoreStep.lean").read_text()
        for op, count in [("SD", 8), ("SW", 4), ("SH", 2), ("SB", 1)]:
            with self.subTest(op=op):
                stmt = statement(source, "dfn" + op)
                conclusion = stmt.split(" : «dfn'", 1)[1]
                self.assertNotIn("rawWriteData", conclusion)
                self.assertNotIn("GPR rs2", conclusion)
                self.assertEqual(conclusion.count("holUpdate"), count)
                self.assertEqual(conclusion.count("if rs2 = 0 then 0#8"), count)
                self.assertEqual(conclusion.count("if rs1 = 0"), count)
                for j in range(count):
                    self.assertIn(f"holWordExtract 8 {j * 8 + 7} {j * 8}", conclusion)
                self.assertIn("mstatus.VM = 0#5", stmt)
                self.assertEqual("haligned :" in stmt, count != 1)
                self.assertEqual(stmt.count("mcpuid.ArchBase ≠"), 2 if op == "SD" else 0)
                self.assertIn('@[hol "' + HOL + '" "' + op + '"]\ntheorem dfn' + op + ' ', source)
                self.assertNotIn('@[hol "' + HOL + '" "' + op + '"]\ntheorem dfn' + op + 'Raw', source)


if __name__ == "__main__":
    unittest.main()
