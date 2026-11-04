"""The committed L3 RISC-V carriers are exactly the mechanical rendering of the model script."""
import pathlib
import runpy
import subprocess
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
RENDER = runpy.run_path(str(ROOT / 'scripts' / 'l3_types_to_lean.py'))['render']
MODEL = 'HOL/examples/l3-machine-code/riscv/model/riscvScript.sml'
ARM8_MODEL = 'HOL/examples/l3-machine-code/arm8/model/arm8Script.sml'
ARM8_TYPES = ['ProcState', 'TCR_EL1', 'TCR_EL2_EL3', 'SCTLRType', 'BranchType',
              'AccType', 'ExtendType', 'LogicalOp', 'MemOp', 'MemBarrierOp',
              'RevOp', 'SystemHintOp', 'PSTATEField', 'System', 'Debug',
              'LoadStore', 'Branch', 'CRCExt', 'Data', 'instruction',
              'MachineCode', 'exception', 'arm8_state']
# `DecidableEq` derivation fails for these deeply nested carriers; `BEq` is
# enough for the rendered L3 definitions, which compare with `==`.
ARM8_BEQ_ONLY = ('LoadStore', 'Data', 'instruction')


class L3TypesToLeanTest(unittest.TestCase):
    def test_riscv_types_match_model(self):
        rendered = RENDER((ROOT / MODEL).read_text(), MODEL)
        committed = (ROOT / 'Flapjack/RiscV/L3/Types.lean').read_text()
        start = committed.index('/-- HOL L3 ')
        end = committed.rindex('end Flapjack.RiscV.L3')
        self.assertEqual(committed[start:end].rstrip('\n'), rendered.rstrip('\n'))

    def test_arm8_types_match_model(self):
        rendered = RENDER((ROOT / ARM8_MODEL).read_text(), ARM8_MODEL,
                          ARM8_TYPES, ARM8_BEQ_ONLY)
        committed = (ROOT / 'Flapjack/Compiler/Encoders/Arm8/L3/Types.lean').read_text()
        start = committed.index('/-- HOL L3 ')
        end = committed.rindex('end Flapjack.Compiler.Encoders.Arm8.L3')
        self.assertEqual(committed[start:end].rstrip('\n'), rendered.rstrip('\n'))

    def test_cli_reproduces_arm8_types(self):
        # The documented invocation must reproduce the committed carriers,
        # including the `--beq-only` declarations.
        out = subprocess.run(
            [sys.executable, str(ROOT / 'scripts' / 'l3_types_to_lean.py'),
             ARM8_MODEL, ARM8_MODEL, *ARM8_TYPES, '--beq-only', ','.join(ARM8_BEQ_ONLY)],
            capture_output=True, text=True, check=True)
        committed = (ROOT / 'Flapjack/Compiler/Encoders/Arm8/L3/Types.lean').read_text()
        start = committed.index('/-- HOL L3 ')
        end = committed.rindex('end Flapjack.Compiler.Encoders.Arm8.L3')
        self.assertEqual(committed[start:end].rstrip('\n'), out.stdout.rstrip('\n'))

    def test_cli_rejects_missing_beq_only_value(self):
        proc = subprocess.run(
            [sys.executable, str(ROOT / 'scripts' / 'l3_types_to_lean.py'),
             ARM8_MODEL, ARM8_MODEL, '--beq-only'],
            capture_output=True, text=True)
        self.assertNotEqual(proc.returncode, 0)

    def test_unknown_declaration_is_an_error(self):
        proc = subprocess.run(
            [sys.executable, str(ROOT / 'scripts' / 'l3_types_to_lean.py'),
             ARM8_MODEL, ARM8_MODEL, 'SCTRLType'],
            capture_output=True, text=True)
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn('SCTRLType', proc.stderr)

    def test_unknown_beq_only_name_is_an_error(self):
        proc = subprocess.run(
            [sys.executable, str(ROOT / 'scripts' / 'l3_types_to_lean.py'),
             ARM8_MODEL, ARM8_MODEL, *ARM8_TYPES, '--beq-only', 'LoadStore,Typo'],
            capture_output=True, text=True)
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn('Typo', proc.stderr)

    def test_render_rejects_unknown_declaration(self):
        with self.assertRaises(ValueError):
            RENDER((ROOT / ARM8_MODEL).read_text(), ARM8_MODEL, ['SCTRLType'])

    def test_beq_only_name_outside_the_selection_is_an_error(self):
        # `Data` exists in the model but the DECL filter drops it, so the flag
        # would otherwise pass silently and change nothing.
        proc = subprocess.run(
            [sys.executable, str(ROOT / 'scripts' / 'l3_types_to_lean.py'),
             ARM8_MODEL, ARM8_MODEL, 'ProcState', 'arm8_state',
             '--beq-only', 'Data'],
            capture_output=True, text=True)
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn('Data', proc.stderr)

    def test_render_rejects_beq_only_outside_the_selection(self):
        with self.assertRaises(ValueError):
            RENDER((ROOT / ARM8_MODEL).read_text(), ARM8_MODEL,
                   ['ProcState', 'arm8_state'], ('Data',))


if __name__ == '__main__':
    unittest.main()
