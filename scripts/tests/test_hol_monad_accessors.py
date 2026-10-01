"""Bounded source provenance checks for ml_monadBaseLib-generated accessors."""
import pathlib
import runpy
import tempfile
import unittest

SCRIPTS = pathlib.Path(__file__).resolve().parents[1]
RECOGNIZE = runpy.run_path(str(SCRIPTS / 'hol_sml_declarations.py'))['monad_accessor_declarations']
CHECK = runpy.run_path(str(SCRIPTS / 'check-hol-refs.py'))['hol_declaration_lines']
INDEX = runpy.run_path(str(SCRIPTS / 'index-hol.py'))['parse_file']

RECORD = 'Datatype:\n  st = <| items : num list (* c; d *)\n     ; size : num\n     |>\nEnd\n'
ACCESS = 'val accessors = define_monad_access_funs ``:st``;\n'
SELECT = 'val items_accessors = el 1 accessors;\n'
MANIP = 'val arr = define_MFarray_manip_funs [items_accessors] sub_exn upd_exn;\n'
GETSET = ('get_items_def', 'set_items_def', 'get_size_def', 'set_size_def')
ARRAY = ('items_length_def', 'items_sub_def', 'update_items_def')
SOURCE = RECORD + ACCESS + SELECT + MANIP


class MonadAccessorTest(unittest.TestCase):
    def test_access_and_manip(self):
        self.assertEqual(RECOGNIZE(SOURCE), [(GETSET, 6, 6), (ARRAY, 8, 8)])

    def test_multiline_manip(self):
        source = RECORD + ACCESS + SELECT + MANIP.replace(' [', '\n  [')
        self.assertEqual(RECOGNIZE(source), [(GETSET, 6, 6), (ARRAY, 8, 9)])

    def test_second_field_selected(self):
        source = (RECORD + ACCESS + 'val size_accessors = el 2 accessors;\n' +
                  MANIP.replace('items_accessors', 'size_accessors'))
        self.assertEqual(RECOGNIZE(source)[1][0],
                         ('size_length_def', 'size_sub_def', 'update_size_def'))

    def test_actual_originals(self):
        reg_alloc = (SCRIPTS.parent / 'cakeml/compiler/backend/reg_alloc/reg_allocScript.sml').read_text()
        found = RECOGNIZE(reg_alloc)
        self.assertEqual([(start, end, len(names)) for names, start, end in found],
                         [(83, 83, 24), (113, 115, 15)])
        self.assertIn('set_dim_def', found[0][0])
        self.assertIn('update_move_related_def', found[1][0])
        self.assertNotIn('dim_sub_def', found[1][0])
        linear = (SCRIPTS.parent / 'cakeml/compiler/backend/reg_alloc/linear_scanScript.sml').read_text()
        self.assertEqual([(start, end, len(names)) for names, start, end in RECOGNIZE(linear)],
                         [(335, 335, 10), (361, 361, 15)])

    def test_rejected_access_forms(self):
        bad = [
            RECORD + ACCESS.replace('define_monad_access_funs', 'other_factory'),
            RECORD + ACCESS.replace('``:st``', 'st_type'),
            RECORD + ACCESS.replace('``:st``', '``:num list``'),
            RECORD + ACCESS.replace('``:st``', '``:unknown``'),
            RECORD + ACCESS.replace(';', ''),
            RECORD + '(* ' + ACCESS + ' *)\n',
            RECORD + 'local\n' + ACCESS + 'in\nend;\n',
            RECORD + 'val _ = let\n' + ACCESS + 'in () end;\n',
            RECORD + 'val define_monad_access_funs = other;\n' + ACCESS,
            RECORD + 'fun define_monad_access_funs t = other;\n' + ACCESS,
            RECORD + RECORD + ACCESS,
            RECORD.replace('size : num', 'items : num') + ACCESS,
            '(*' + RECORD + '*)\n' + ACCESS,
        ]
        for source in bad:
            with self.subTest(source=source):
                self.assertEqual(RECOGNIZE(source), [])

    def test_rejected_manip_forms(self):
        bad = [
            RECORD + ACCESS + SELECT + MANIP.replace('define_MFarray_manip_funs', 'other_manip'),
            RECORD + ACCESS + SELECT + MANIP.replace('items_accessors', 'unknown_accessors'),
            RECORD + ACCESS + SELECT.replace('el 1', 'el 3') + MANIP,
            RECORD + ACCESS + SELECT.replace('el 1', 'el 0') + MANIP,
            RECORD + ACCESS + SELECT.replace('el 1 accessors', 'el k accessors') + MANIP,
            RECORD + ACCESS + SELECT.replace('accessors;', 'others;') + MANIP,
            RECORD + ACCESS + SELECT + 'val items_accessors = other;\n' + MANIP,
            RECORD + ACCESS + 'val accessors = other;\n' + SELECT + MANIP,
            RECORD + ACCESS + SELECT + 'fun define_MFarray_manip_funs a b c = other;\n' + MANIP,
            RECORD + ACCESS + SELECT + MANIP.replace(';', ''),
            RECORD + ACCESS + SELECT + MANIP.replace('[items_accessors]', '(make ())'),
            RECORD + ACCESS + 'local\n' + SELECT + 'in\nend;\n' + MANIP,
            RECORD + ACCESS + 'val el = other;\n' + SELECT + MANIP,
            RECORD + ACCESS + 'fun el k l = other;\n' + SELECT + MANIP,
            RECORD + ACCESS + 'val (el, other) = make;\n' + SELECT + MANIP,
            RECORD + ACCESS + SELECT + 'val el = other;\n' + MANIP,
            RECORD + ACCESS + 'val accessors = other;\n' + SELECT + MANIP,
            RECORD + ACCESS + SELECT + MANIP.replace('[items_accessors]', '[items_accessors, items_accessors]'),
        ]
        for source in bad:
            with self.subTest(source=source):
                self.assertEqual(RECOGNIZE(source)[1:], [])

    def test_generator_must_precede_selection(self):
        # An earlier non-generator binding is what the selection reads; a later
        # generator call with the same name must not lend it provenance.
        for source in [
            RECORD + 'val accessors = other;\n' + SELECT + MANIP + ACCESS,
            RECORD + SELECT + MANIP + ACCESS,
            RECORD + 'val accessors = other;\n' + SELECT + ACCESS + MANIP,
        ]:
            with self.subTest(source=source):
                generated = [name for names, _, _ in RECOGNIZE(source) for name in names]
                self.assertFalse(set(ARRAY) & set(generated))

    def test_checker_and_index_share_span(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            path = root / 'fixtureScript.sml'
            path.write_text('Theory fixture\n' + SOURCE)
            lines = CHECK(path, {})
            self.assertEqual({name: lines[name] for name in GETSET}, {name: [7] for name in GETSET})
            self.assertEqual({name: lines[name] for name in ARRAY}, {name: [9] for name in ARRAY})
            entries, _, _ = INDEX(root, path)
            generated = [(x.kind, x.name, x.start, x.end) for x in entries
                         if x.name in GETSET + ARRAY]
            self.assertEqual(generated, [('Definition', name, 7, 7) for name in GETSET] +
                             [('Definition', name, 9, 9) for name in ARRAY])


if __name__ == '__main__':
    unittest.main()
