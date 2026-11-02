"""The committed L3 RISC-V carriers are exactly the mechanical rendering of the model script."""
import pathlib
import runpy
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
RENDER = runpy.run_path(str(ROOT / 'scripts' / 'l3_types_to_lean.py'))['render']
MODEL = 'HOL/examples/l3-machine-code/riscv/model/riscvScript.sml'
ARM8_MODEL = 'HOL/examples/l3-machine-code/arm8/model/arm8Script.sml'
ARM8_STATE_CARRIERS = ['ProcState', 'TCR_EL1', 'TCR_EL2_EL3', 'SCTLRType',
                       'BranchType', 'exception', 'arm8_state']


class L3TypesToLeanTest(unittest.TestCase):
    def test_riscv_types_match_model(self):
        rendered = RENDER((ROOT / MODEL).read_text(), MODEL)
        committed = (ROOT / 'Flapjack/RiscV/L3/Types.lean').read_text()
        start = committed.index('/-- HOL L3 ')
        end = committed.rindex('end Flapjack.RiscV.L3')
        self.assertEqual(committed[start:end].rstrip('\n'), rendered.rstrip('\n'))

    def test_arm8_state_carriers_match_model(self):
        rendered = RENDER((ROOT / ARM8_MODEL).read_text(), ARM8_MODEL,
                          ARM8_STATE_CARRIERS)
        committed = (ROOT / 'Flapjack/Compiler/Encoders/Arm8/L3/Types.lean').read_text()
        start = committed.index('/-- HOL L3 ')
        end = committed.rindex('end Flapjack.Compiler.Encoders.Arm8.L3')
        self.assertEqual(committed[start:end].rstrip('\n'), rendered.rstrip('\n'))


if __name__ == '__main__':
    unittest.main()
