import importlib.util
from pathlib import Path
import unittest
ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("slice_guard", ROOT / "scripts/hol-probes/check-riscv-target-slice.py")
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)
class SliceTests(unittest.TestCase):
    def test_full_original_and_negative_guards(self):
        args = [(ROOT / p).read_text() for p in (
            "scripts/hol-probes/riscv_target_slice_probe.out",
            "cakeml/compiler/encoders/riscv/proofs/riscv_targetProofScript.sml",
            "scripts/hol-probes/riscv_target_slice_probeScript.sml",
            "scripts/hol-probes/regenerate.sh")]
        M.check(*args)
        for i, old, new in [(0,"43","42"), (0,"word64","word32"),
                            (0,"hypotheses=0","hypotheses=1"), (0,"proved=T","proved=F"),
                            (2,"63 >< 32","62 >< 32"), (2,"BBLAST_PROVE","TRUTH"),
                            (3,"slice_types slice_hypotheses","slice_hypotheses"),
                            (3,"run_probe riscv_target_slice_probeScript.sml","# removed")]:
            changed = args.copy(); changed[i] = changed[i].replace(old,new)
            with self.subTest(old=old), self.assertRaises(ValueError): M.check(*changed)
