"""Fail closed on the three reviewed pinned L3 BL-generated declarations."""
from pathlib import Path
import runpy
import shutil
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
CHECKER = runpy.run_path(str(ROOT / "scripts/check-hol-refs.py"))
SOURCE_ERROR = CHECKER["l3_boolify_source_error"]
DECLARATIONS = CHECKER["hol_declaration_lines"]
SCRIPT = CHECKER["L3_BOOLIFY_SCRIPT"]
GENERATORS = CHECKER["L3_BOOLIFY_GENERATORS"]
EXPECTED = CHECKER["L3_BOOLIFY_DECLARATIONS"]


class L3BoolifyReferences(unittest.TestCase):
    def fixture(self, root):
        for name in (SCRIPT, *GENERATORS):
            target = root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / name, target)

    def test_real_pinned_sources_and_exact_generation_lines(self):
        self.assertIsNone(SOURCE_ERROR(ROOT))
        names = DECLARATIONS(ROOT / SCRIPT, {})
        for name, (_width, line) in EXPECTED.items():
            self.assertEqual(names[name], [line])

    def test_no_unreviewed_generated_width_or_bitify_name(self):
        names = DECLARATIONS(ROOT / SCRIPT, {})
        for name in ("boolify1_def", "boolify64_def", "boolify0_def", "bitify8_def"):
            self.assertNotIn(name, names)

    def test_each_factory_or_model_pin_failure_rejects_all_generated_names(self):
        for failed_source in (SCRIPT, *GENERATORS):
            with self.subTest(source=failed_source):
                def rejected(_root, source):
                    return "changed pinned bytes" if source == failed_source else None
                with patch.dict(SOURCE_ERROR.__globals__, {"hol_submodule_source_error": rejected}):
                    self.assertIsNotNone(SOURCE_ERROR(ROOT))
                    names = DECLARATIONS(ROOT / SCRIPT, {})
                    for name in EXPECTED:
                        self.assertNotIn(name, names)

    def test_changed_width_trigger_rejected_even_with_mocked_byte_pin(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            self.fixture(root)
            p = root / SCRIPT
            lines = p.read_text().splitlines()
            _width, line = EXPECTED["boolify16_def"]
            lines[line - 1] = "BL(64,Var(\"h\",F16)),"
            p.write_text("\n".join(lines) + "\n")
            with patch.dict(SOURCE_ERROR.__globals__, {"hol_submodule_source_error": lambda *_: None}):
                self.assertIsNotNone(SOURCE_ERROR(root))
                names = DECLARATIONS(p, {})
                for name in EXPECTED:
                    self.assertNotIn(name, names)

    def test_same_bl_calls_in_unrelated_script_do_not_declare_names(self):
        with tempfile.TemporaryDirectory() as temp:
            p = Path(temp) / "OtherScript.sml"
            p.write_text((ROOT / SCRIPT).read_text())
            names = DECLARATIONS(p, {})
            for name in EXPECTED:
                self.assertNotIn(name, names)

    def test_explicit_wrong_line_reference_is_rejected(self):
        # One shared declaration cache: the script is parsed once, not per call.
        cache = {}
        for name, (_width, line) in EXPECTED.items():
            self.assertIsNotNone(CHECKER["hol_ref_error"](ROOT / SCRIPT, name, line + 1, cache))
            self.assertIsNone(CHECKER["hol_ref_error"](ROOT / SCRIPT, name, line, cache))


if __name__ == "__main__":
    unittest.main()
