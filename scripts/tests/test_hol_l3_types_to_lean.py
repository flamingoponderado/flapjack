"""The committed L3 RISC-V carriers are exactly the restricted mechanical rendering of the model script."""
import copy
import json
import pathlib
import runpy
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
RENDER = runpy.run_path(str(ROOT / 'scripts' / 'l3_types_to_lean.py'))['render']
MODEL = 'HOL/examples/l3-machine-code/riscv/model/riscvScript.sml'
RESTRICTION = json.loads((ROOT / 'scripts/l3/riscv-mi-restriction.json').read_text())


class L3TypesToLeanTest(unittest.TestCase):
    def render(self, restriction):
        return RENDER((ROOT / MODEL).read_text(), MODEL, restriction)

    def test_riscv_types_match_restricted_model(self):
        rendered = self.render(RESTRICTION['types'])
        committed = (ROOT / 'Flapjack/RiscV/L3/Types.lean').read_text()
        start = committed.index('/-- HOL L3 ')
        end = committed.rindex('end Flapjack.RiscV.L3')
        self.assertEqual(committed[start:end].rstrip('\n'), rendered.rstrip('\n'))

    def test_floating_point_carriers_are_absent(self):
        committed = (ROOT / 'Flapjack/RiscV/L3/Types.lean').read_text()
        for name in ('FPCSR', 'UserCSR', 'Rounding', 'FConv', 'FArith', 'FPLoad', 'FPStore'):
            self.assertIn(name, RESTRICTION['types']['removed'])
            self.assertNotIn(' ' + name + ' where', committed)
        for field in ('c_fpr', 'c_UCSR', 'fp_data'):
            self.assertNotIn(field, committed)

    def test_unrestricted_rendering_keeps_full_tagged_model(self):
        full = self.render(None)
        self.assertIn('inductive FArith where', full)
        self.assertIn('"riscv_state"]\nstructure riscv_state', full)

    def test_reduced_types_are_untagged(self):
        rendered = self.render(RESTRICTION['types'])
        for name in RESTRICTION['types']['untagged']:
            self.assertNotIn('"' + name + '"]', rendered)
        self.assertIn('"rawInstType"]\ninductive rawInstType', rendered)

    def test_restriction_fails_closed(self):
        def mutated(change):
            restriction = copy.deepcopy(RESTRICTION['types'])
            change(restriction)
            return restriction
        bad = [
            lambda r: r['removed'].append('NoSuchType'),
            lambda r: r['removed_constructors'].update({'System': ['NoSuchCtor']}),
            lambda r: r['removed_fields'].update({'riscv_state': ['no_such_field']}),
            lambda r: r['removed_fields'].update({'System': ['EBREAK']}),
            lambda r: r['untagged'].remove('riscv_state'),
            lambda r: r['untagged'].append('FPCSR'),
            lambda r: r.update({'extra': []}),
        ]
        for change in bad:
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.render(mutated(change))


if __name__ == '__main__':
    unittest.main()
