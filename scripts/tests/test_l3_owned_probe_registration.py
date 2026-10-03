"""Keep delivered native model observations discoverable in the HOL driver."""
from pathlib import Path
import re
import shlex
import unittest

ROOT = Path(__file__).resolve().parents[2]
FAMILIES = (
    "immediate_shift", "word_arithmetic", "multiply", "divide", "fp_bits",
    "control_fetch", "fp_memory", "decode_immediates", "boolify_provenance", "run_dispatch", "decode", "write_pc", "decode_any", "update_pc", "next_step", "next_evaluation", "decode_transport", "step_bit_rewrites", "fetch_theorems", "encode", "target_encoder", "native_config",
)


def commands(text):
    lines = iter(text.splitlines())
    for line in lines:
        if not line.startswith("run_probe "):
            continue
        parts = [line]
        while parts[-1].rstrip().endswith("\\"):
            parts.append(next(lines))
        yield shlex.split("\n".join(parts).replace("\\\n", " "))


class NativeProbeRegistration(unittest.TestCase):
    def test_each_delivered_family_has_one_original_regeneration_route(self):
        entries = list(commands((ROOT / "scripts/hol-probes/regenerate.sh").read_text()))
        for family in FAMILIES:
            with self.subTest(family=family):
                name = f"l3_{family}_probeScript.sml"
                selected = [x for x in entries if x[1] == name]
                self.assertEqual(len(selected), 1)
                self.assertEqual(selected[0][2], f"l3_{family}_probe.out")
                if family in ("target_encoder", "native_config"):
                    self.assertEqual(selected[0][-2:], [
                        "$cake_dir/compiler/encoders/riscv/riscv_targetScript.sml",
                        "$cake_dir/compiler/encoders/riscv",
                    ])
                    continue
                location = "step" if family in ("decode_any", "update_pc", "next_step", "next_evaluation", "decode_transport", "step_bit_rewrites", "fetch_theorems") else "model"
                source = "riscv_stepScript.sml" if family in ("decode_any", "update_pc", "next_step", "next_evaluation", "decode_transport", "step_bit_rewrites", "fetch_theorems") else "riscvScript.sml"
                self.assertEqual(selected[0][-2:], [
                    f"$hol_dir/examples/l3-machine-code/riscv/{location}/{source}",
                    f"$hol_dir/examples/l3-machine-code/riscv/{location}",
                ])

    def test_every_captured_label_is_a_required_driver_sentinel(self):
        entries = list(commands((ROOT / "scripts/hol-probes/regenerate.sh").read_text()))
        for family in FAMILIES:
            with self.subTest(family=family):
                selected = [x for x in entries if x[1] == f"l3_{family}_probeScript.sml"]
                self.assertEqual(len(selected), 1)
                required = selected[0][3:-2]
                output = (ROOT / f"scripts/hol-probes/l3_{family}_probe.out").read_text()
                captured = re.findall(r"^([A-Za-z0-9_]+)=", output, re.M)
                self.assertTrue(captured)
                self.assertEqual(len(captured), len(set(captured)))
                self.assertEqual(len(required), len(set(required)))
                self.assertEqual(set(required), set(captured))


if __name__ == "__main__":
    unittest.main()
