"""The original HOL FP root closure is excluded from riscv-mi; retained roots render completely."""
import gzip
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
MODEL = 'HOL/examples/l3-machine-code/riscv/model/riscvScript.sml'


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


class L3FpDefsTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.renderer = load('l3_fp_renderer', 'scripts/hol_terms_to_lean.py')
        cls.checks = load('l3_fp_checks', 'scripts/l3/check-renderings.py')
        cls.restriction = json.loads((ROOT / 'scripts/l3/riscv-mi-restriction.json').read_text())
        cls.directory = tempfile.TemporaryDirectory()
        directory = Path(cls.directory.name)
        cls.export = directory / 'definitions.sexp'
        cls.export.write_bytes(gzip.decompress((ROOT / 'scripts/l3/riscv_defs.sexp.gz').read_bytes()))
        # Definitions are rendered against the complete original HOL carriers.
        cls.types = directory / 'Types.lean'
        cls.types.write_text(cls.checks.type_rendering(ROOT))

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def main(self, *extra):
        return self.renderer.main(['renderer', str(self.export), str(self.types), *extra])

    def test_fp_closure_is_excluded(self):
        roots = json.loads((ROOT / 'scripts/l3/fp_roots.json').read_text())
        closure, failed = self.main('--roots=' + ','.join(roots))
        self.assertFalse(failed)
        keys = {thy + '$' + name for thy, name, *_ in closure}
        removed = set(self.restriction['definitions']['removed'])
        native = {self.checks.hol_key(key) for key in self.checks.sources()}
        # The original FP selection also named two shared integer state helpers.
        shared = {'riscv$GPR', 'riscv$NextFetch'}
        self.assertTrue(shared <= set(roots))
        self.assertTrue({tuple(root.split('$', 1)) for root in shared} <= native)
        # Every FP root and every FP-only helper of the closure lacks a native counterpart.
        self.assertTrue(set(roots) - shared <= removed)
        self.assertFalse({tuple(root.split('$', 1)) for root in set(roots) - shared} & native)
        fp_only = {'riscv$round', 'riscv$l3round', 'riscv$setFP_Invalid', 'riscv$writeFPRS',
                   'riscv$writeFPRD', 'riscv$FPRS', 'riscv$FPRD', 'riscv$fcsr', 'riscv$fpr'}
        self.assertTrue(fp_only <= keys & removed)
        committed = (ROOT / 'Flapjack/RiscV/L3/Defs.lean').read_text()
        for name in ('writeFPRS', 'writeFPRD', 'setFP_Invalid', 'round', 'l3round', 'fcsr'):
            self.assertNotIn('def ' + name + ' ', committed)
        self.assertNotIn("dfn'F", committed)

    def test_removed_set_is_exact(self):
        generated = self.checks.renderings()
        actual = self.checks.sources()
        self.checks.check_removed(actual, generated, self.restriction)
        for change in (lambda r: r.append('riscv$GPR'), lambda r: r.pop(), lambda r: r.append('riscv$missing')):
            removed = list(self.restriction['definitions']['removed'])
            change(removed)
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.checks.check_removed(actual, generated, {'definitions': {'removed': removed}})

    def test_generic_hol_carriers_require_only_nonempty(self):
        emitted, failed = self.main()
        self.assertFalse(failed)
        bodies = {name: text for _, name, _, text, _, _ in emitted}
        exception = bodies["raise'exception"]
        self.assertIn('{Ta : Type} [Nonempty Ta]', exception)
        self.assertIn('(Flapjack.holArb Ta)', exception)
        self.assertNotIn('default', exception)
        self.assertTrue(all('[Inhabited ' not in text for text in bodies.values()))

    def test_model_and_step_fetch_remain_distinct_complete_roots(self):
        model, failed = self.main('--roots=riscv$Fetch')
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
        # The step Fetch body is checked in the combined render (where it is
        # only renamed); the model render above already shows that an
        # isolated root keeps its natural name.
        combined, failed = self.main('--roots=riscv$Fetch,riscv_step$NextRISCV')
        self.assertFalse(failed)
        bodies = {(thy, name): text for thy, name, _, text, _, _ in combined}
        self.assertIn('def riscv_Fetch ', bodies[('riscv', 'Fetch')])
        self.assertIn('def riscv_step_Fetch (s : riscv_state)', bodies[('riscv_step', 'Fetch')])
        self.assertIn('rawReadInst (holThe w)', bodies[('riscv_step', 'Fetch')])
        self.assertNotIn('FetchResult', bodies[('riscv_step', 'Fetch')])
        self.assertIn('riscv_step_Fetch s', bodies[('riscv_step', 'NextRISCV')])
        self.assertNotIn('riscv_Fetch s', bodies[('riscv_step', 'NextRISCV')])

    def test_invalid_root_selection_fails_closed(self):
        # `--roots=` reaches the same subset check as an unknown root.
        with self.assertRaisesRegex(ValueError, 'unknown or empty'):
            self.main('--roots=riscv$missing')
        with self.assertRaisesRegex(ValueError, 'at most one'):
            self.main('--roots=riscv$GPR', '--roots=riscv$GPR')

    def test_committed_types_match_restricted_rendering(self):
        self.checks.check_types(ROOT, self.restriction)


if __name__ == '__main__':
    unittest.main()
