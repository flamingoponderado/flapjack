"""Direct reference comparisons must not rely only on digest equality."""

import contextlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import Mock, patch

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location(
    "cake_pinned_parity", ROOT / "scripts/check-cake-pinned-parity.py"
)
parity = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parity)


class DirectComparisonTests(unittest.TestCase):
    def run_case(self, actual):
        reference = subprocess.CompletedProcess([], 0, stdout=b"reference", stderr=b"")
        # Deliberately make the captured observations identical, simulating a
        # collision or defect in the digest layer. Direct bytes must still win.
        capture = {"same": "digest"}
        fixture = Mock()
        fixture.read_text.return_value = json.dumps({
            "cakeml_revision": parity.parity.PINNED_REV,
            "hol_revision": parity.parity.HOL_REV,
            "cases": {"case": capture},
        })
        with (patch.object(parity, "CASES", {"case": "source"}),
              patch.object(parity, "FIXTURE", fixture),
              patch.object(parity, "execute", side_effect=[reference, actual]),
              patch.object(parity, "observation", return_value=capture),
              patch.object(parity.parity, "check_pinned_reference"),
              patch.object(sys, "argv", ["parity", "--check-reference", "/reference"]),
              contextlib.redirect_stdout(io.StringIO())):
            parity.main()

    def test_equal_bytes_pass(self):
        self.run_case(subprocess.CompletedProcess([], 0, stdout=b"reference", stderr=b""))

    def test_different_results_fail_even_when_digests_match(self):
        for actual in (
            subprocess.CompletedProcess([], 0, stdout=b"different", stderr=b""),
            subprocess.CompletedProcess([], 0, stdout=b"reference", stderr=b"different"),
            subprocess.CompletedProcess([], 1, stdout=b"reference", stderr=b""),
        ):
            with self.subTest(actual=actual), self.assertRaisesRegex(SystemExit, "direct output comparison"):
                self.run_case(actual)

    def test_selected_case_does_not_run_other_cases(self):
        capture = {"same": "digest"}
        fixture = Mock()
        fixture.read_text.return_value = json.dumps({
            "cakeml_revision": parity.parity.PINNED_REV,
            "hol_revision": parity.parity.HOL_REV,
            "cases": {"first": capture, "second": capture},
        })
        result = subprocess.CompletedProcess([], 0, stdout=b"result", stderr=b"")
        with (patch.object(parity, "CASES", {"first": "source1", "second": "source2"}),
              patch.object(parity, "FIXTURE", fixture),
              patch.object(parity, "execute", return_value=result) as execute,
              patch.object(parity, "observation", return_value=capture),
              patch.object(sys, "argv", ["parity", "--case", "second"]),
              contextlib.redirect_stdout(io.StringIO())):
            parity.main()
        self.assertEqual(execute.call_count, 1)
        self.assertEqual(execute.call_args.args[1:], ("source2", "second"))

    def test_partial_reference_recording_is_rejected(self):
        with (patch.object(parity, "CASES", {"case": "source"}),
              patch.object(sys, "argv", ["parity", "--case", "case", "--record-reference", "/reference"]),
              contextlib.redirect_stderr(io.StringIO()),
              self.assertRaises(SystemExit) as exit_status):
            parity.main()
        self.assertEqual(exit_status.exception.code, 2)


if __name__ == "__main__":
    unittest.main()
