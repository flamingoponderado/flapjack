"""The isolated FP section is the complete original HOL root dependency closure."""
import gzip
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]

class L3FpDefsTest(unittest.TestCase):
    def args(self, export):
        return [str(ROOT / 'scripts/hol_terms_to_lean.py'), str(export),
                str(ROOT / 'Flapjack/RiscV/L3/Types.lean'),
                'riscv=HOL/examples/l3-machine-code/riscv/model/riscvScript.sml',
                'riscv_step=HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml']

    def test_complete_selected_closure_matches_source_export(self):
        roots = json.loads((ROOT / 'scripts/l3/fp_roots.json').read_text())
        with tempfile.TemporaryDirectory() as directory:
            export = Path(directory) / 'definitions.sexp'
            export.write_bytes(gzip.decompress((ROOT / 'scripts/l3/riscv_defs.sexp.gz').read_bytes()))
            rendered = subprocess.run([sys.executable, *self.args(export), '--roots=' + ','.join(roots)],
                                      check=True, capture_output=True, text=True).stdout
        committed = (ROOT / 'Flapjack/RiscV/L3/Defs.lean').read_text()
        marker = 'open Flapjack.Basis.Pure.MlString\n\n'
        body = committed.split(marker, 1)[1].rsplit('end Flapjack.RiscV.L3', 1)[0]
        self.assertEqual(body.rstrip('\n'), rendered.rstrip('\n'))
        for name in ('writeFPRS', 'writeFPRD', 'setFP_Invalid', 'round', 'setTrap', 'Delta'):
            self.assertIn('def ' + name + ' ', body)
        for precision in ('S', 'D'):
            for op in ('FMIN', 'FMAX', 'FLT', 'FLE', 'FEQ', 'FCLASS', 'FADD', 'FSUB', 'FMUL', 'FDIV', 'FSQRT', 'FMADD', 'FMSUB', 'FNMADD', 'FNMSUB'):
                self.assertIn("def «dfn'" + op + '_' + precision + '»', body)
            for kind in ('W', 'WU', 'L', 'LU'):
                self.assertIn("def «dfn'FCVT_" + kind + '_' + precision + '»', body)
        for cross in ('S_D', 'D_S'):
            self.assertIn("def «dfn'FCVT_" + cross + '»', body)
        self.assertNotIn('def walk64 ', body)
        self.assertNotIn('def Run ', body)

    def test_generic_hol_carriers_require_only_nonempty(self):
        spec = importlib.util.spec_from_file_location('generic_carrier_renderer', ROOT / 'scripts/hol_terms_to_lean.py')
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        with tempfile.TemporaryDirectory() as directory:
            export = Path(directory) / 'definitions.sexp'
            export.write_bytes(gzip.decompress((ROOT / 'scripts/l3/riscv_defs.sexp.gz').read_bytes()))
            emitted, failed = module.main(['renderer', *self.args(export)[1:]])
        self.assertFalse(failed)
        bodies = {name: text for _, name, _, text, _, _ in emitted}
        exception = bodies["raise'exception"]
        self.assertIn('{Ta : Type} [Nonempty Ta]', exception)
        self.assertIn('(Flapjack.holArb Ta)', exception)
        self.assertNotIn('default', exception)
        self.assertTrue(all('[Inhabited ' not in text for text in bodies.values()))

    def test_model_and_step_fetch_remain_distinct_complete_roots(self):
        spec = importlib.util.spec_from_file_location('fetch_closure_renderer', ROOT / 'scripts/hol_terms_to_lean.py')
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        with tempfile.TemporaryDirectory() as directory:
            export = Path(directory) / 'definitions.sexp'
            export.write_bytes(gzip.decompress((ROOT / 'scripts/l3/riscv_defs.sexp.gz').read_bytes()))
            args = ['renderer', *self.args(export)[1:]]
            model, failed = module.main([*args, '--roots=riscv$Fetch'])
            self.assertFalse(failed)
            model_body = next(text for thy, name, _, text, _, _ in model if (thy, name) == ('riscv', 'Fetch'))
            self.assertIn('def Fetch (_u_ : Unit)', model_body)
            self.assertIn('FetchResult.F_Error', model_body)
            self.assertIn('Internal.FETCH_MISALIGNED', model_body)
            self.assertIn('Internal.FETCH_FAULT', model_body)
            self.assertIn('FetchResult.F_Result', model_body)
            self.assertIn('«write\'Delta»', model_body)
            model_keys = {(thy, name) for thy, name, *_ in model}
            self.assertTrue({('riscv', name) for name in ('Delta', "write'Delta", 'PC', 'translateAddr', 'rawReadInst')} <= model_keys)
            step, failed = module.main([*args, '--roots=riscv_step$Fetch'])
            self.assertFalse(failed)
            step_body = next(text for thy, name, _, text, _, _ in step if (thy, name) == ('riscv_step', 'Fetch'))
            self.assertIn('def Fetch (s : riscv_state)', step_body)
            self.assertIn('rawReadInst (holThe w)', step_body)
            self.assertNotIn('FetchResult', step_body)
            combined, failed = module.main([*args, '--roots=riscv$Fetch,riscv_step$NextRISCV'])
            self.assertFalse(failed)
            bodies = {(thy, name): text for thy, name, _, text, _, _ in combined}
            self.assertIn('def riscv_Fetch ', bodies[('riscv', 'Fetch')])
            self.assertIn('def riscv_step_Fetch ', bodies[('riscv_step', 'Fetch')])
            self.assertIn('riscv_step_Fetch s', bodies[('riscv_step', 'NextRISCV')])
            self.assertNotIn('riscv_Fetch s', bodies[('riscv_step', 'NextRISCV')])

    def test_invalid_root_selection_fails_closed(self):
        spec = importlib.util.spec_from_file_location('fp_selection_renderer', ROOT / 'scripts/hol_terms_to_lean.py')
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        with tempfile.TemporaryDirectory() as directory:
            export = Path(directory) / 'definitions.sexp'
            export.write_bytes(gzip.decompress((ROOT / 'scripts/l3/riscv_defs.sexp.gz').read_bytes()))
            for selection in ('--roots=riscv$missing', '--roots='):
                with self.subTest(selection=selection), self.assertRaisesRegex(ValueError, 'unknown or empty'):
                    module.main(['renderer', *self.args(export)[1:], selection])
            with self.assertRaisesRegex(ValueError, 'at most one'):
                module.main(['renderer', *self.args(export)[1:], '--roots=riscv$GPR', '--roots=riscv$GPR'])

if __name__ == '__main__':
    unittest.main()
