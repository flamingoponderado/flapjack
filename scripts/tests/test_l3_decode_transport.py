"""Original decoder transport statements retain full carriers and premises."""
import importlib.util
from pathlib import Path
import unittest
ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("decode_transport", ROOT / "scripts/hol-probes/check-l3-decode-transport.py")
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)
class DecoderTransport(unittest.TestCase):
    def test_original_universal_capture(self):
        MODULE.check((ROOT / "scripts/hol-probes/l3_decode_transport_probe.out").read_text())
    def test_narrowed_and_circular_mutations(self):
        original = "\n".join(MODULE.EXPECTED)
        replacements = [("w::word32", "w::word16"), ("h::word16", "h::word8"),
          ("i::instruction", "i::word32"),
          ("Decode w = i ⇒", "DecodeAny (Word w) = i ⇒"),
          ("DecodeRVC h = i ⇒", "DecodeAny (Half h) = i ⇒"),
          ("Decode w = i ⇒ ", ""), ("DecodeRVC h = i ⇒ ", ""),
          ("hypotheses=0", "hypotheses=1"), ("proof=T", "proof=F")]
        for before, after in replacements:
            with self.subTest(before=before):
                self.assertIn(before, original)
                with self.assertRaises(ValueError): MODULE.check(original.replace(before, after))
if __name__ == "__main__": unittest.main()
