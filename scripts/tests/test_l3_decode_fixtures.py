"""Keep complete decoder oracle expectations concrete and source-derived."""
import importlib.util
from pathlib import Path
import unittest
from unittest import mock
ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("native_decode_fixtures", ROOT / "scripts/l3/check-decode-fixtures.py")
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)

class DecodeSourceFixtures(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.text = (ROOT / "scripts/hol-probes/l3_decode_probe.out").read_text()

    def test_complete_numeric_fixture_reproduces(self):
        self.assertEqual(CHECK.fixture(self.text), (ROOT / "Flapjack/Test/L3DecodeParity.lean").read_text())

    def test_every_source_guard_path_has_bounded_samples(self):
        data = CHECK.source_samples()
        self.assertEqual((len(data["Decode"]["rows"]), len(data["Decode"]["infeasible"])), (164, 0))
        self.assertEqual((len(data["DecodeRVC"]["rows"]), len(data["DecodeRVC"]["infeasible"])), (49, 3))
        rows = CHECK.sample_inputs()
        self.assertEqual(len(rows), 621)
        self.assertEqual(len({x["label"] for x in rows}), 621)
        for row in rows:
            self.assertLess(row["word"], 1 << row["width"])
            self.assertGreaterEqual(row["word"], 0)

    def test_literal_guard_solver(self):
        self.assertIsNone(CHECK.solve([[1], [-1]]))
        self.assertEqual(CHECK.solve([[1], [-1, 2]]), {1: True, 2: True})

    def test_missing_duplicate_or_extra_original_row(self):
        for text in ["\n".join(self.text.splitlines()[1:]), self.text + self.text.splitlines()[0] + "\n", self.text + "Decode_NEW=0\n"]:
            with self.subTest(text=text[:40]), self.assertRaises(ValueError):
                CHECK.capture_rows(text)

    def test_changed_type_or_hypotheses(self):
        for text in [self.text.replace("Decode_hypotheses=0", "Decode_hypotheses=1"), self.text.replace(":word32 -> instruction", ":word16 -> instruction")]:
            with self.assertRaises(ValueError):
                CHECK.capture_rows(text)

    def test_unreduced_decoder_and_helper_rejected(self):
        for name, outer in [("Decode", "Decode"), ("DecodeRVC", "DecodeRVC")]:
            ty = '(ty "riscv" "instruction")'
            with self.assertRaises(ValueError):
                CHECK.value_term(f'(c "riscv" "{name}" {ty})', outer)
        # A constructor with a source helper inside is still not an independent numeric payload.
        value = '(a (c "riscv" "Load" (ty "min" "fun" (ty "riscv" "Load") (ty "riscv" "instruction"))) (c "bitstring" "v2w" (ty "riscv" "Load")))'
        with self.assertRaises(ValueError):
            CHECK.value_term(value, "Load")

    def test_riscv_mi_rejections_are_exact(self):
        fixture = CHECK.fixture(self.text)
        self.assertEqual(fixture.count("riscv-mi rejects the original removed instruction"), 418)
        self.assertNotIn("FArith", fixture)
        rows = CHECK.capture_rows(self.text)
        names = CHECK.constructor_names()
        with mock.patch.object(CHECK, "constructor_names", lambda: names | {"FMADD_S"}):
            with self.assertRaisesRegex(ValueError, "restored"):
                CHECK.check_exclusions(rows)
        with mock.patch.object(CHECK, "EXCLUDED_CONSTRUCTORS", CHECK.EXCLUDED_CONSTRUCTORS | {"Bogus"}):
            with self.assertRaisesRegex(ValueError, "stale"):
                CHECK.check_exclusions(rows)
