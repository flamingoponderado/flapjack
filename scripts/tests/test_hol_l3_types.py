"""Bounded source provenance checks for L3 Import Construct/Record type declarations."""
import pathlib
import runpy
import tempfile
import unittest

SCRIPTS = pathlib.Path(__file__).resolve().parents[1]
RECOGNIZE = runpy.run_path(str(SCRIPTS / 'hol_sml_declarations.py'))['l3_type_declarations']
CHECK = runpy.run_path(str(SCRIPTS / 'check-hol-refs.py'))['hol_declaration_lines']
INDEX = runpy.run_path(str(SCRIPTS / 'index-hol.py'))['parse_file']

START = 'open HolKernel boolLib bossLib Import\n\nval () = Import.start "m"\n\n'
CONSTRUCT = 'val _ = Construct [("kind",[("A",[]),("B",[F16])])]\n;\n'
MULTI = 'val _ = Construct\n  [("t1",[("C",[CTy"t2"])]),\n   ("t2",[("D",[])])]\n;\n'
RECORD = 'val _ = Record\n  ("st",\n   [("pc",F64),("ok",bTy)])\n;\n'


class L3TypesTest(unittest.TestCase):
    def test_forms(self):
        self.assertEqual(RECOGNIZE(START + CONSTRUCT), [(('kind',), 5, 5)])
        self.assertEqual(RECOGNIZE(START + MULTI), [(('t1', 't2'), 5, 7)])
        self.assertEqual(RECOGNIZE(START + RECORD), [(('st',), 5, 7)])

    def test_actual_riscv_model(self):
        model = (SCRIPTS.parent / 'HOL/examples/l3-machine-code/riscv/model/riscvScript.sml').read_text()
        found = RECOGNIZE(model)
        self.assertEqual(len(found), 50)
        names = [name for names, _, _ in found for name in names]
        self.assertIn(('riscv_state',), [names for names, _, _ in found])
        self.assertEqual(names[0], 'rawInstType')
        self.assertIn('instruction', names)
        self.assertIn('MachineCSR', names)

    def test_rejected_forms(self):
        bad = [
            CONSTRUCT,
            START.replace('Import.start', 'Import.other') + CONSTRUCT,
            START + '(* ' + CONSTRUCT + ' *)\n',
            START + 'local\n' + CONSTRUCT + 'in\nend;\n',
            START + 'val Construct = other;\n' + CONSTRUCT,
            START + 'fun Record x = x;\n' + RECORD,
            START + CONSTRUCT.replace('[("kind"', '[(kind'),
            START + CONSTRUCT.replace('"kind"', '"bad name"'),
            START + RECORD.replace('("st",', '[("st",'),
            START + 'val _ = Construct [("dup",[]),("dup",[])]\n;\n',
            START + 'val x = Construct [("kind",[])]\n;\n',
            START + 'val _ = Construct [("kind",[("A",[])])\n',
        ]
        for source in bad:
            with self.subTest(source=source):
                self.assertEqual(RECOGNIZE(source), [])

    def test_checker_and_index_share_span(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            path = root / 'mScript.sml'
            path.write_text(START + MULTI + RECORD)
            lines = CHECK(path, {})
            self.assertEqual({name: lines[name] for name in ('t1', 't2', 'st')},
                             {'t1': [5], 't2': [5], 'st': [9]})
            entries, _, _ = INDEX(root, path)
            self.assertEqual([(x.kind, x.name, x.start, x.end) for x in entries
                              if x.name in ('t1', 't2', 'st')],
                             [('Datatype', 't1', 5, 7), ('Datatype', 't2', 5, 7),
                              ('Datatype', 'st', 9, 11)])


if __name__ == '__main__':
    unittest.main()
