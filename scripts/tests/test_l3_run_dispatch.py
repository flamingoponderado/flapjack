"""Reject missing or narrowed original full dispatcher evidence."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("run_dispatch_check", ROOT / "scripts/hol-probes/check-l3-run-dispatch.py")
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)

class FullRunCapture(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / "scripts/hol-probes/l3_run_dispatch_probe.out").read_text()

    def test_complete_original_capture(self):
        CHECK.check_rows(self.text)
        self.assertEqual(len(CHECK.CLAUSES), 163)
        self.assertEqual(len(CHECK.expected_rows()), 328)

    def test_missing_middle_clause(self):
        with self.assertRaises(ValueError):
            CHECK.check_rows("\n".join(x for x in self.text.splitlines() if not x.startswith("Run_FCVT_LU_D_equation=")))

    def test_wrong_handler(self):
        with self.assertRaises(ValueError):
            CHECK.check_rows(self.text.replace("= dfn'ADD x s", "= dfn'SUB x s"))

    def test_narrowed_payload_quantifier(self):
        with self.assertRaises(ValueError):
            CHECK.check_rows(self.text.replace("Run_ADD_equation=∀x s.", "Run_ADD_equation=∀s."))

    def test_identity_and_nullary_cases(self):
        for key in ["Run_FENCE_equation", "Run_FENCE_I_equation", "Run_WFI_equation", "Run_UnknownInstruction_equation"]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                CHECK.check_rows(self.text.replace(key+"=", key+"=T "))

    def test_duplicate_or_extra_row(self):
        for extra in ["Run_type=:instruction -> riscv_state -> riscv_state\n", "Run_NEW_proof=T\n"]:
            with self.subTest(extra=extra), self.assertRaises(ValueError):
                CHECK.check_rows(self.text + extra)
