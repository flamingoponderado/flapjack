"""Bounded source provenance checks for define_run-generated declarations."""
import pathlib
import runpy
import tempfile
import unittest

SCRIPTS = pathlib.Path(__file__).resolve().parents[1]
RECOGNIZE = runpy.run_path(str(SCRIPTS / 'hol_sml_declarations.py'))['define_run_declarations']
CHECK = runpy.run_path(str(SCRIPTS / 'check-hol-refs.py'))['hol_declaration_lines']
INDEX = runpy.run_path(str(SCRIPTS / 'index-hol.py'))['parse_file']
BINDING = 'val run_seed_def = define_run ``:state`` ["items"] "seed";\n'


class DefineRunTest(unittest.TestCase):
    def test_inline(self):
        self.assertEqual(RECOGNIZE(BINDING), [('seed', 'run_seed_def', 1, 1)])

    def test_empty_fields(self):
        self.assertEqual(RECOGNIZE(BINDING.replace('["items"]', '[]'))[0][:2],
                         ('seed', 'run_seed_def'))

    def test_earlier_literal_fields(self):
        source = 'val fields = ["items", "tags"];\n' + BINDING.replace('["items"]', 'fields')
        self.assertEqual(RECOGNIZE(source), [('seed', 'run_seed_def', 2, 2)])

    def test_multiline(self):
        source = 'val fields = ["items"];\nval run_seed_def = define_run ``:state``\n fields\n "seed";\n'
        self.assertEqual(RECOGNIZE(source), [('seed', 'run_seed_def', 2, 4)])

    def test_actual_original(self):
        source = (SCRIPTS.parent / 'cakeml/compiler/backend/reg_alloc/reg_allocScript.sml').read_text()
        self.assertEqual(RECOGNIZE(source), [('ira_state', 'run_ira_state_def', 1466, 1468)])

    def test_hol_let_does_not_open_sml_scope(self):
        source = 'Definition sample_def:\n sample x = let y = x in y\nEnd\n' + BINDING
        self.assertEqual(RECOGNIZE(source), [('seed', 'run_seed_def', 4, 4)])

    def test_inline_hol_proof_closes(self):
        self.assertEqual(RECOGNIZE('Theorem sample: T Proof simp[] QED\n' + BINDING),
                         [('seed', 'run_seed_def', 2, 2)])

    def test_local_shadow_does_not_escape(self):
        source = 'local\n  val define_run = other;\nin\nend;\n' + BINDING
        self.assertEqual(RECOGNIZE(source), [('seed', 'run_seed_def', 5, 5)])

    def test_rejected_forms(self):
        bad = [
            BINDING.replace('define_run', 'other_generator'),
            BINDING.replace('define_run', 'define_run_alias'),
            BINDING.replace('define_run', 'make define_run'),
            BINDING.replace('run_seed_def', 'run_other_def'),
            BINDING.replace('run_seed_def', 'seed_def'),
            BINDING.replace('"seed";', 'name;'),
            BINDING.replace('``:state``', 'state_type'),
            BINDING.replace('``:state``', '``:num list``'),
            BINDING.replace('["items"]', 'unknown_fields'),
            BINDING.replace('["items"]', 'make_fields ()'),
            BINDING.replace('["items"]', '[field_name]'),
            BINDING.replace('["items"]', '["bad-field"]'),
            BINDING.replace(';', ''),
            BINDING.replace('``:state``', '``:state'),
            '(* ' + BINDING + ' *)\n',
            'val text = "' + BINDING.replace('"', '\\"').replace('\n', '') + '";\n',
            'val term = ``' + BINDING + '``;\n',
            'local\n' + BINDING + 'in\nend;\n',
            'val _ = let\n' + BINDING + 'in () end;\n',
            'structure Example = struct\n' + BINDING + 'end;\n',
            'Definition bogus_def:\n' + BINDING + 'End\n',
            'Theorem bogus:\n' + BINDING + 'Proof simp[] QED\n',
            'val define_run = other;\n' + BINDING,
            'val (define_run, other) = make;\n' + BINDING,
            'val alias as define_run = other;\n' + BINDING,
            'fun define_run a b c = other;\n' + BINDING,
            '(* val fields = ["items"]; *)\n' + BINDING.replace('["items"]', 'fields'),
            'local\nval fields = ["items"];\nin\nend;\n' + BINDING.replace('["items"]', 'fields'),
            'val fields = ["items"];\nval fields = unknown;\n' + BINDING.replace('["items"]', 'fields'),
            'val fields = ["items"];\nval fields = ["other"];\n' + BINDING.replace('["items"]', 'fields'),
            'val fields = ["items"];\nval (fields, other) = make;\n' + BINDING.replace('["items"]', 'fields'),
            'val fields = ["items"];\nval (\n fields, other) = make;\n' + BINDING.replace('["items"]', 'fields'),
            'val fields = ["items"];\nval other as fields = make;\n' + BINDING.replace('["items"]', 'fields'),
            'val fields = ["items"];\nfun fields x = x;\n' + BINDING.replace('["items"]', 'fields'),
        ]
        for source in bad:
            with self.subTest(source=source):
                self.assertEqual(RECOGNIZE(source), [])

    def test_checker_and_index_share_span(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            path = root / 'fixtureScript.sml'
            path.write_text('Theory fixture\n' + BINDING)
            self.assertEqual(CHECK(path, {})['seed'], [2])
            self.assertEqual(CHECK(path, {})['run_seed_def'], [2])
            entries, _, _ = INDEX(root, path)
            self.assertEqual([(x.kind, x.name, x.start, x.end) for x in entries],
                             [('Datatype', 'seed', 2, 2), ('Definition', 'run_seed_def', 2, 2)])


if __name__ == '__main__':
    unittest.main()
