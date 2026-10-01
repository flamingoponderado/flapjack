"""Bounded source provenance checks for ml_monadBaseLib exception functions."""
import pathlib
import runpy
import tempfile
import unittest

SCRIPTS = pathlib.Path(__file__).resolve().parents[1]
RECOGNIZE = runpy.run_path(str(SCRIPTS / 'hol_sml_declarations.py'))['monad_exception_declarations']
CHECK = runpy.run_path(str(SCRIPTS / 'check-hol-refs.py'))['hol_declaration_lines']
INDEX = runpy.run_path(str(SCRIPTS / 'index-hol.py'))['parse_file']

EXN = 'Datatype:\n  err = Fail string | Subscript\nEnd\n'
CALL = 'val exn_functions = define_monad_exception_functions ``:err`` ``:st``;\n'
NAMES = ('raise_Fail_def', 'handle_Fail_def', 'raise_Subscript_def', 'handle_Subscript_def')


class MonadExceptionTest(unittest.TestCase):
    def test_call(self):
        self.assertEqual(RECOGNIZE(EXN + CALL), [(NAMES, 4, 4)])

    def test_multiline_variant_and_call(self):
        source = ('Datatype:\n  err = Fail string\n      | Subscript\nEnd\n' +
                  CALL.replace('``:err`` ', '``:err``\n  '))
        self.assertEqual(RECOGNIZE(source), [(NAMES, 5, 6)])

    def test_actual_originals(self):
        reg_alloc = (SCRIPTS.parent / 'cakeml/compiler/backend/reg_alloc/reg_allocScript.sml').read_text()
        self.assertEqual(RECOGNIZE(reg_alloc), [(NAMES, 106, 106)])
        # linear_scan uses the ancestor theory's state_exn (its local copy is commented).
        linear = (SCRIPTS.parent / 'cakeml/compiler/backend/reg_alloc/linear_scanScript.sml').read_text()
        self.assertEqual(RECOGNIZE(linear), [])

    def test_rejected_forms(self):
        bad = [
            EXN + CALL.replace('define_monad_exception_functions', 'other_factory'),
            EXN + CALL.replace('``:err``', 'err_type'),
            EXN + CALL.replace('``:err``', '``:unknown``'),
            EXN + CALL.replace('``:st``', 'state_type'),
            EXN + CALL.replace(';', ''),
            EXN + '(* ' + CALL + ' *)\n',
            '(*' + EXN + '*)\n' + CALL,
            EXN + 'local\n' + CALL + 'in\nend;\n',
            EXN + 'val define_monad_exception_functions = other;\n' + CALL,
            EXN + 'fun define_monad_exception_functions a b = other;\n' + CALL,
            EXN + EXN + CALL,
            EXN.replace('Fail string | Subscript', 'Fail string | Fail num') + CALL,
            EXN.replace('Fail string', 'Fail (num list)') + CALL,
            EXN.replace('Fail string | Subscript', '<| a : num |>') + CALL,
            EXN.replace('Subscript', 'subscript') + CALL,
            CALL + EXN,
        ]
        for source in bad:
            with self.subTest(source=source):
                self.assertEqual(RECOGNIZE(source), [])

    def test_checker_and_index_share_span(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            path = root / 'fixtureScript.sml'
            path.write_text('Theory fixture\n' + EXN + CALL)
            lines = CHECK(path, {})
            self.assertEqual({name: lines[name] for name in NAMES}, {name: [5] for name in NAMES})
            entries, _, _ = INDEX(root, path)
            self.assertEqual([(x.kind, x.name, x.start, x.end) for x in entries if x.name in NAMES],
                             [('Definition', name, 5, 5) for name in NAMES])


if __name__ == '__main__':
    unittest.main()
