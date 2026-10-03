"""The committed L3 RISC-V carriers are exactly the mechanical rendering of the model script."""
import pathlib
import runpy
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
RENDER = runpy.run_path(str(ROOT / 'scripts' / 'l3_types_to_lean.py'))['render']
MODEL = 'HOL/examples/l3-machine-code/riscv/model/riscvScript.sml'


class L3TypesToLeanTest(unittest.TestCase):
    def test_riscv_types_match_model(self):
        rendered = RENDER((ROOT / MODEL).read_text(), MODEL)
        committed = (ROOT / 'Flapjack/RiscV/L3/Types.lean').read_text()
        start = committed.index('/-- HOL L3 ')
        end = committed.rindex('end Flapjack.RiscV.L3')
        self.assertEqual(committed[start:end].rstrip('\n'), rendered.rstrip('\n'))


if __name__ == '__main__':
    unittest.main()
