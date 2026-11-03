"""`check-renderings.py` names ARM8 declarations the way the renderer does."""
import gzip
import importlib.util
import pathlib
import runpy
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
LEAN_DECL_NAMES = runpy.run_path(str(ROOT / 'scripts' / 'l3' / 'check-renderings.py'))['lean_decl_names']

ARM8_EXPORT = ROOT / 'scripts' / 'l3' / 'arm8_defs.sexp.gz'
ARM8_TYPES = ROOT / 'Flapjack' / 'Compiler' / 'Encoders' / 'Arm8' / 'L3' / 'Types.lean'
RISCV_EXPORT = ROOT / 'scripts' / 'l3' / 'riscv_defs.sexp.gz'
RISCV_TYPES = ROOT / 'Flapjack' / 'RiscV' / 'L3' / 'Types.lean'


def renderer_module():
    spec = importlib.util.spec_from_file_location(
        'renderer_reset_test', ROOT / 'scripts' / 'hol_terms_to_lean.py')
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def write_export(path, gz_path):
    path.write_bytes(gzip.decompress(gz_path.read_bytes()))


class ModelTheoryResetTest(unittest.TestCase):
    def test_main_resets_the_model_theory_between_calls(self):
        # `main` sets a module-global MODEL_THY from `--thy`; a second call
        # without it must go back to `riscv`, not keep `arm8`.
        module = renderer_module()
        with tempfile.TemporaryDirectory() as directory:
            arm8 = pathlib.Path(directory) / 'arm8.sexp'
            write_export(arm8, ARM8_EXPORT)
            _, failed = module.main(['renderer', str(arm8), str(ARM8_TYPES), '--thy=arm8'])
            self.assertFalse(failed)
            riscv = pathlib.Path(directory) / 'riscv.sexp'
            write_export(riscv, RISCV_EXPORT)
            _, failed = module.main(['renderer', str(riscv), str(RISCV_TYPES)])
            self.assertFalse(failed)


class LeanDeclNamesTest(unittest.TestCase):
    def test_unique_name_is_kept(self):
        emitted = [('arm8', 'Fetch', 'Fetch', 'Fetch_def', 'body', None, False)]
        self.assertEqual(LEAN_DECL_NAMES(emitted), {('arm8', 'Fetch'): 'Fetch'})

    def test_name_shared_by_two_theories_is_prefixed(self):
        # The renderer disambiguates a constant defined in both theories; the
        # gate must use the same name or it would compare one entry twice.
        emitted = [('arm8', 'Fetch', 'arm8_Fetch', 'Fetch_def', 'a', None, False),
                   ('arm8_step', 'Fetch', 'arm8_step_Fetch', 'Fetch_def', 'b', None, False)]
        names = LEAN_DECL_NAMES(emitted)
        self.assertEqual(names[('arm8', 'Fetch')], 'arm8_Fetch')
        self.assertEqual(names[('arm8_step', 'Fetch')], 'arm8_step_Fetch')


if __name__ == '__main__':
    unittest.main()
