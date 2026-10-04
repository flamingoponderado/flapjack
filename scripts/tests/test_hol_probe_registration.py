"""Register the previously unregistered cross-format and partial-allocator probes."""
from pathlib import Path
import re
import shlex
import unittest

ROOT = Path(__file__).resolve().parents[2]
REGEN = ROOT / "scripts/hol-probes/regenerate.sh"

# Each probe with its expected (output, source, workdir).
EXPECTED = {
    "l3_riscv_cross_format_probeScript.sml": (
        "l3_riscv_cross_format_probe.out",
        "$hol_dir/examples/l3-machine-code/riscv/model/riscvScript.sml",
        "$hol_dir/examples/l3-machine-code/riscv/model",
    ),
    "machine_ieee_cross_format_probeScript.sml": (
        "machine_ieee_cross_format_probe.out",
        "$hol_dir/src/floating-point/machine_ieeeScript.sml",
        "$hol_dir/src/floating-point",
    ),
    "stack_alloc_generational_alloc_statement_probeScript.sml": (
        "stack_alloc_generational_alloc_statement_probe.out",
        "$cake_dir/compiler/backend/proofs/stack_allocProofScript.sml",
        "$cake_dir/compiler/backend/proofs",
    ),
}


def commands(text):
    lines = iter(text.splitlines())
    for line in lines:
        if not line.startswith("run_probe "):
            continue
        parts = [line]
        while parts[-1].rstrip().endswith("\\"):
            parts.append(next(lines))
        yield shlex.split("\n".join(parts).replace("\\\n", " "))


class CrossFormatProbeRegistration(unittest.TestCase):
    def test_each_probe_has_one_regeneration_route(self):
        entries = list(commands(REGEN.read_text()))
        for probe, (output, source, workdir) in EXPECTED.items():
            with self.subTest(probe=probe):
                selected = [x for x in entries if x[1] == probe]
                self.assertEqual(len(selected), 1)
                self.assertEqual(selected[0][2], output)
                self.assertEqual(selected[0][-2:], [source, workdir])

    def test_every_registered_label_is_captured_in_the_output(self):
        entries = list(commands(REGEN.read_text()))
        for probe, (output, _source, _workdir) in EXPECTED.items():
            with self.subTest(probe=probe):
                selected = [x for x in entries if x[1] == probe]
                self.assertEqual(len(selected), 1)
                required = selected[0][3:-2]
                self.assertTrue(required)
                captured = re.findall(
                    r"^([A-Za-z0-9_]+)=",
                    (ROOT / "scripts/hol-probes" / output).read_text(),
                    re.M,
                )
                captured_set = set(captured)
                for label in required:
                    self.assertIn(label, captured_set)
                self.assertEqual(len(required), len(set(required)))

    def test_certificate_refresh_covers_cross_format_probe(self):
        text = REGEN.read_text()
        match = re.search(r"probe_needs_refresh\(\)\s*\{(.*?)\n\}", text, re.S)
        self.assertIsNotNone(match)
        body = match.group(1)
        self.assertIn("binary_ieee_directed_certificates.sml", body)
        self.assertIn("l3_riscv_cross_format_probeScript.sml", body)
        self.assertIn("l3_riscv_int_to_fp_probeScript.sml", body)


if __name__ == "__main__":
    unittest.main()
