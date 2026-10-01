#!/usr/bin/env python3
"""Regression tests for the captured HOL probe row checker."""

import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "check-hol-probe-rows.py"
SPEC = importlib.util.spec_from_file_location("check_hol_probe_rows", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
ROWS = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = ROWS
SPEC.loader.exec_module(ROWS)

PROBE_SCRIPT = """\
fun print_eval label q =
  let val th = EVAL q in
    (print (label ^ "="); print_term (rconc th); print "\\n")
  end;
val _ = print_eval "alpha" ``1``;
val _ = print_eval "beta" ``2``;
"""


class ProbeRowCheckerTest(unittest.TestCase):
    def test_registration_paths_required(self):
        valid = ('run_probe demo_probeScript.sml demo_probe.out alpha beta '
                 '"$cake_dir/demoScript.sml" "$cake_dir/compiler/backend"\n')
        self.assertEqual(ROWS.check_registrations(valid), [])
        self.assertEqual(ROWS.check_registrations(
            'run_probe demo_probeScript.sml demo_probe.out "$cake_dir/demoScript.sml"\n'), [])
        self.assertTrue(ROWS.check_registrations(
            'run_probe demo_probeScript.sml demo_probe.out alpha beta\n'))

    def test_continuation_cannot_absorb_next_registration(self):
        broken = ('run_probe a_probeScript.sml a_probe.out alpha \\\n'
                  'run_probe b_probeScript.sml b_probe.out beta \\\n'
                  '"$cake_dir/demoScript.sml" "$cake_dir/compiler/backend"\n')
        self.assertTrue(ROWS.check_registrations(broken))

    def _probes_dir(self, directory: str, out_text: str) -> Path:
        probes = Path(directory) / "hol-probes"
        probes.mkdir()
        (probes / "demo_probe.out").write_text(out_text, encoding="utf-8")
        (probes / "demo_probeScript.sml").write_text(PROBE_SCRIPT, encoding="utf-8")
        lock = probes / "rows.lock.json"
        records = ROWS.expected_lock(probes)
        lock.write_text(ROWS.render_lock(records), encoding="utf-8")
        return probes

    def test_clean_tree_passes(self):
        ROWS.check(ROWS.PROBES, ROWS.LOCK)
        # New original-HOL fixtures legitimately grow this inventory. Check
        # the complete records against the lock, not a frozen corpus size.
        locked = json.loads(ROWS.LOCK.read_text(encoding="utf-8"))
        self.assertTrue(locked["records"])
        self.assertEqual(ROWS.expected_lock(ROWS.PROBES), locked["records"])

    def test_value_mutation_is_detected(self):
        with tempfile.TemporaryDirectory() as directory:
            probes = self._probes_dir(directory, "alpha=1\nbeta=2\n")
            (probes / "demo_probe.out").write_text("alpha=1\nbeta=999\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "lock differs"):
                ROWS.check(probes, probes / "rows.lock.json")

    def test_label_mutation_is_detected(self):
        with tempfile.TemporaryDirectory() as directory:
            probes = self._probes_dir(directory, "alpha=1\nbeta=2\n")
            (probes / "demo_probe.out").write_text("alpha=1\ngamma=2\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "lock differs|does not print"):
                ROWS.check(probes, probes / "rows.lock.json")

    def test_duplicate_label_is_detected(self):
        with tempfile.TemporaryDirectory() as directory:
            probes = self._probes_dir(directory, "alpha=1\nalpha=2\n")
            with self.assertRaisesRegex(ValueError, "duplicate label"):
                ROWS.check(probes, probes / "rows.lock.json")

    def test_missing_captured_row_is_detected(self):
        with tempfile.TemporaryDirectory() as directory:
            probes = self._probes_dir(directory, "alpha=1\n")
            with self.assertRaisesRegex(ValueError, "does not record"):
                ROWS.check(probes, probes / "rows.lock.json")

    def test_multiline_value_is_parsed_as_one_row(self):
        rows = ROWS.parse_rows("alpha=1\nbeta=Mark\n  (Seq Skip)\n")
        self.assertEqual(rows, [("alpha", "1"), ("beta", "Mark\n  (Seq Skip)")])

    def test_unclassified_probe_script_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            probes = Path(directory) / "hol-probes"
            probes.mkdir()
            (probes / "demo_probe.out").write_text("alpha=1\n", encoding="utf-8")
            (probes / "demo_probeScript.sml").write_text(
                "val _ = print_term (concl th);\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(ValueError, "no statically detectable"):
                ROWS.check(probes, probes / "rows.lock.json")

    def test_unsupported_list_is_documented(self):
        listed = set(ROWS.UNSUPPORTED)
        partial = set(ROWS.PARTIAL_OUT)
        self.assertFalse(listed & partial)
        for name in listed | partial:
            with self.subTest(name=name):
                self.assertTrue((ROWS.PROBES / name).is_file())


if __name__ == "__main__":
    unittest.main()
