"""The committed L3 RISC-V definitions are exactly the rendering of the committed HOL export."""
import gzip
import importlib.util
import pathlib
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]


class L3DefsToLeanTest(unittest.TestCase):
    def test_bit_field_insert_rejects_out_of_range_input(self):
        spec = importlib.util.spec_from_file_location('l3_bound_renderer', ROOT / 'scripts/hol_terms_to_lean.py')
        renderer = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = renderer
        spec.loader.exec_module(renderer)
        class Numeric:
            @staticmethod
            def nat_literal(x):
                return x if isinstance(x, int) else None
        original = renderer.nat_literal
        renderer.nat_literal = Numeric.nat_literal
        try:
            bit = renderer.Ty('min', 'bool', ())
            index = renderer.Ty('fcp', 'bit0', (renderer.Ty('one', 'one', ()),))
            word = renderer.Var('w', renderer.Ty('fcp', 'cart', (bit, index)))
            with self.assertRaisesRegex(renderer.Unrenderable, 'exceed word width'):
                renderer.special_bit_field_insert(None, None, [2, 0, word, word], {})
            with self.assertRaisesRegex(renderer.Unrenderable, 'checked literal bounds'):
                renderer.special_bit_field_insert(None, None, [], {})
        finally:
            renderer.nat_literal = original

    def test_ieee_comparison_closure_and_real_qualifiers(self):
        body = (ROOT / 'Flapjack/RiscV/L3/Defs.lean').read_text()
        for suffix in ['S', 'D']:
            for op in ['FMIN', 'FMAX', 'FLT', 'FLE', 'FEQ']:
                name = "dfn'" + op + '_' + suffix
                self.assertIn('"' + name + '_def" (reals_as_rational_cuts)]', body)
                self.assertIn('def «' + name + '»', body)
        self.assertIn("exponent := v.extractLsb' 23 8", body)
        self.assertIn("exponent := v.extractLsb' 52 11", body)
        self.assertIn('| .lt =>', body)
        self.assertNotIn('| .LT =>', body)

    def test_integer_memory_closure_is_present(self):
        body = (ROOT / 'Flapjack/RiscV/L3/Defs.lean').read_text()
        for name in ['walk64', 'translate64', 'translateAddr', 'Fetch',
                     "«dfn'LB»", "«dfn'LBU»", "«dfn'LH»", "«dfn'LHU»",
                     "«dfn'LW»", "«dfn'LWU»", "«dfn'LD»",
                     "«dfn'SB»", "«dfn'SH»", "«dfn'SW»", "«dfn'SD»"]:
            self.assertRegex(body, r'(?:noncomputable )?def ' + __import__('re').escape(name) + r'\s')
        self.assertIn('termination_by arg0.2.2.2.2.2', body)

    def test_riscv_defs_match_export(self):
        with tempfile.TemporaryDirectory() as directory:
            export = pathlib.Path(directory) / 'riscv_defs.sexp'
            export.write_bytes(gzip.decompress((ROOT / 'scripts/l3/riscv_defs.sexp.gz').read_bytes()))
            rendered = subprocess.run(
                [sys.executable, str(ROOT / 'scripts/hol_terms_to_lean.py'), str(export),
                 str(ROOT / 'Flapjack/RiscV/L3/Types.lean'),
                 'riscv=HOL/examples/l3-machine-code/riscv/model/riscvScript.sml',
                 'riscv_step=HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml'],
                check=True, capture_output=True, text=True).stdout
        committed = (ROOT / 'Flapjack/RiscV/L3/Defs.lean').read_text()
        marker = 'open Flapjack.Basis.Pure.MlString\n\n'
        body = committed[committed.index(marker) + len(marker):committed.rindex('end Flapjack.RiscV.L3')]
        self.assertEqual(body.rstrip('\n'), rendered.rstrip('\n'))


if __name__ == '__main__':
    unittest.main()
