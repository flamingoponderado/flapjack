"""`check-renderings.py` names ARM8 declarations the way the renderer does."""
import pathlib
import runpy
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
LEAN_DECL_NAMES = runpy.run_path(str(ROOT / 'scripts' / 'l3' / 'check-renderings.py'))['lean_decl_names']


class LeanDeclNamesTest(unittest.TestCase):
    def test_unique_name_is_kept(self):
        emitted = [('arm8', 'Fetch', 'Fetch_def', 'body', None, False)]
        self.assertEqual(LEAN_DECL_NAMES(emitted), {('arm8', 'Fetch'): 'Fetch'})

    def test_name_shared_by_two_theories_is_prefixed(self):
        # The renderer disambiguates a constant defined in both theories; the
        # gate must use the same name or it would compare one entry twice.
        emitted = [('arm8', 'Fetch', 'Fetch_def', 'a', None, False),
                   ('arm8_step', 'Fetch', 'Fetch_def', 'b', None, False)]
        names = LEAN_DECL_NAMES(emitted)
        self.assertEqual(names[('arm8', 'Fetch')], 'arm8_Fetch')
        self.assertEqual(names[('arm8_step', 'Fetch')], 'arm8_step_Fetch')


if __name__ == '__main__':
    unittest.main()
