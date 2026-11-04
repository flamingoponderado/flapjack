"""Guards in scripts/hol_terms_to_lean.py that keep unsound renderings out.

Each test exercises a case where the renderer must either avoid a capture or
report `Unrenderable` instead of emitting a Lean term that means something
different from the HOL term.
"""
import pathlib
import runpy
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
M = runpy.run_path(str(ROOT / 'scripts' / 'hol_terms_to_lean.py'))

Var = M['Var']
Const = M['Const']
Comb = M['Comb']
Ty = M['Ty']
TyVar = M['TyVar']
Renderer = M['Renderer']
Unrenderable = M['Unrenderable']
insert_predicate = M['insert_predicate']
symbolic_field_bounds = M['symbolic_field_bounds']
render_multi = M['render_multi']

NUM = Ty('num', 'num', ())
NUM_TO_NUM = Ty('min', 'fun', (NUM, NUM))


def numeral(n):
    """HOL's binary numeral term for `n` (LSB-first BIT1/BIT2 chain)."""
    t = Const('arithmetic', 'ZERO', NUM)
    while n > 0:
        if n % 2 == 1:
            t = Comb(Const('arithmetic', 'BIT1', NUM_TO_NUM), t)
            n = (n - 1) // 2
        else:
            t = Comb(Const('arithmetic', 'BIT2', NUM_TO_NUM), t)
            n = (n - 2) // 2
    return Comb(Const('arithmetic', 'NUMERAL', NUM_TO_NUM), t)


def add(l, r):
    ty = Ty('min', 'fun', (NUM, Ty('min', 'fun', (NUM, NUM))))
    return Comb(Comb(Const('arithmetic', '+', ty), l), r)


Lam = M['Lam']


class InsertTest(unittest.TestCase):
    def render(self, a, b, xs):
        return insert_predicate(Renderer({}, {}), {}, [a, b], xs)

    def test_binder_avoids_free_variable(self):
        self.assertEqual(self.render(Var('a', NUM), Var('s', NUM), ['a', 's']),
                         '(fun x => x = a || s x)')

    def test_binder_renamed_when_operand_uses_x(self):
        self.assertEqual(self.render(Var('x', NUM), Var('s', NUM), ['x', 's']),
                         "(fun x' => x' = x || s x')")

    def test_binder_renamed_when_either_operand_uses_x(self):
        self.assertEqual(self.render(Var('s', NUM), Var('x', NUM), ['s', 'x']),
                         "(fun x' => x' = s || x x')")

    def test_primed_variable_renders_with_underscore_and_does_not_clash(self):
        self.assertEqual(self.render(Var("x'", NUM), Var('s', NUM), ['x_', 's']),
                         '(fun x => x = x_ || s x)')

    def test_free_variable_of_a_different_type_is_still_taken(self):
        # HOL variables are (name, type) pairs: binding `x : num` does not bind
        # a free `x : word64`, so the predicate binder must not reuse `x`.
        xw = Var('x', word(64))
        lam = Lam(Var('x', NUM), xw)
        self.assertEqual(self.render(lam, Var('s', NUM), ['(fun x => x)', 's']),
                         "(fun x' => x' = (fun x => x) || s x')")

    def test_uses_the_renderer_env_names(self):
        # The operand renders as `u_x`, so the binder `x` captures nothing.
        env = {('x', NUM): 'u_x'}
        self.assertEqual(insert_predicate(Renderer({}, {}), env,
                                          [Var('x', NUM), Var('s', NUM)], ['u_x', 's']),
                         '(fun x => x = u_x || s x)')

    def test_env_name_collision_renames(self):
        # Another variable rendered as `x` must not be captured.
        env = {('y', NUM): 'x'}
        self.assertEqual(insert_predicate(Renderer({}, {}), env,
                                          [Var('y', NUM), Var('s', NUM)], ['x', 's']),
                         "(fun x' => x' = x || s x')")

    def test_bound_x_does_not_force_a_rename(self):
        # `(fun x => x) INSERT s` binds its own `x`; the predicate binder may
        # stay `x` because no free variable named `x` can be captured.
        self.assertEqual(self.render(Lam(Var('x', NUM), Var('x', NUM)), Var('s', NUM),
                                     ['(fun x => x)', 's']),
                         '(fun x => x = (fun x => x) || s x)')

    def test_escaped_primed_variable_is_compared_by_identifier(self):
        # `x'` is not in `env`, so `Renderer.var` escapes it as `«x'»`; the
        # binder must still skip `x'` and take `x''` rather than compare the
        # escaped text with the plain name.
        self.assertEqual(self.render(Var('x', NUM), Var("x'", NUM), ['x', '«x\'»']),
                         "(fun x'' => x'' = x || «x'» x'')")



class BitFieldInsertBoundsTest(unittest.TestCase):
    def test_movewide_shape_is_accepted(self):
        low = Var('pos', NUM)
        self.assertTrue(symbolic_field_bounds(add(low, numeral(15)), low, 16))

    def test_wrong_step_is_rejected(self):
        low = Var('pos', NUM)
        self.assertFalse(symbolic_field_bounds(add(low, numeral(31)), low, 16))

    def test_wrong_low_operand_is_rejected(self):
        low = Var('pos', NUM)
        self.assertFalse(symbolic_field_bounds(add(low, numeral(15)), Var('q', NUM), 16))

    def test_non_addition_is_rejected(self):
        low = Var('pos', NUM)
        self.assertFalse(symbolic_field_bounds(low, low, 16))



def fcp(n):
    """The HOL fcp index type for `n` bits (`bit0` doubles, `bit1` adds one)."""
    t = Ty('one', 'one', ())
    for b in bin(n)[2:][1:]:
        t = Ty('fcp', 'bit1' if b == '1' else 'bit0', (t,))
    return t


def word(n):
    return Ty('fcp', 'cart', (Ty('min', 'bool', ()), fcp(n)))


WORD16 = word(16)
WORD64 = word(64)
BFI_TYPE = Ty('min', 'fun', (NUM, Ty('min', 'fun', (NUM, Ty('min', 'fun', (
    WORD16, Ty('min', 'fun', (WORD64, WORD64))))))))
BFI_TYPE_NARROW = Ty('min', 'fun', (NUM, Ty('min', 'fun', (NUM, Ty('min', 'fun', (
    WORD16, Ty('min', 'fun', (WORD16, WORD16))))))))


class BitFieldInsertRenderTest(unittest.TestCase):
    def setUp(self):
        self.r = Renderer({}, {})
        self.c = Const('min', 'bit_field_insert', BFI_TYPE)
        self.low = Var('pos', NUM)
        self.imm = Var('imm', WORD16)
        self.target = Var('v', WORD64)

    def render(self, high):
        return M['special_bit_field_insert'](
            self.r, self.c, [high, self.low, self.imm, self.target], {})

    def test_movewide_symbolic_bounds_are_rendered(self):
        out = self.render(add(self.low, numeral(15)))
        self.assertIn('holBitFieldInsert', out)

    def test_literal_bounds_are_rendered(self):
        self.low = numeral(0)
        out = self.render(numeral(15))
        self.assertIn('holBitFieldInsert', out)

    def test_result_width_is_not_required_to_bound_high(self):
        # HOL's `word_modify` visits only result indices, so a `high` past the
        # result width still agrees with HOL; the guard bounds the input index
        # (`high - low < input width`), which is what can differ.
        self.c = Const('min', 'bit_field_insert', BFI_TYPE_NARROW)
        out = self.render(add(self.low, numeral(15)))
        self.assertIn('holBitFieldInsert', out)

    def test_unchecked_symbolic_bounds_are_rejected(self):
        with self.assertRaises(Unrenderable):
            self.render(add(self.low, numeral(31)))

    def test_literal_bounds_wider_than_input_are_rejected(self):
        self.low = numeral(0)
        with self.assertRaises(Unrenderable):
            self.render(numeral(31))


class WidthExprTest(unittest.TestCase):
    def test_width_one_type_is_one_bit(self):
        # HOL's `one` index type is `one$one`, not an `fcp` op.
        self.assertEqual(M['dimension_expr'](Ty('one', 'one', ())), 1)
        self.assertEqual(M['dimension_expr'](Ty('fcp', 'bit1', (Ty('one', 'one', ()),))), 3)
        self.assertEqual(M['word_width_expr'](word(1)), 1)
        self.assertEqual(M['word_width_expr'](word(16)), 16)

    def test_type_variable_index_is_a_dimension_variable(self):
        # The renderer prefixes type variables (`N` -> `TN`).
        self.assertEqual(M['dimension_expr'](TyVar('N')), 'TN')
        self.assertEqual(M['word_width_expr'](
            Ty('fcp', 'cart', (Ty('min', 'bool', ()), TyVar('N')))), 'TN')

    def test_word_width_rejects_non_index_types(self):
        # An index that is itself a word type denotes `2^8`, not 8; a bare
        # variable or a non-cart type is not a word.
        nested = Ty('fcp', 'cart', (Ty('min', 'bool', ()), word(8)))
        self.assertIsNone(M['word_width_expr'](nested))
        self.assertIsNone(M['word_width_expr'](TyVar('N')))
        self.assertIsNone(M['word_width_expr'](Ty('one', 'one', ())))


class RenderMultiTest(unittest.TestCase):
    def setUp(self):
        self.r = Renderer({}, {})
        self.f = Const('min', 'num2foo', Ty('min', 'fun', (NUM, NUM)))

    def test_arity_mismatch_is_rejected(self):
        out = [(self.f, [Var('a', NUM)], Var('a', NUM)),
               (self.f, [Var('a', NUM), Var('b', NUM)], Var('a', NUM))]
        with self.assertRaises(Unrenderable):
            render_multi(self.r, 'num2foo', out)

    def test_different_constants_are_rejected(self):
        g = Const('min', 'num2bar', Ty('min', 'fun', (NUM, NUM)))
        out = [(self.f, [Var('a', NUM)], Var('a', NUM)),
               (g, [Var('b', NUM)], Var('b', NUM))]
        with self.assertRaises(Unrenderable):
            render_multi(self.r, 'num2foo', out)

    def test_recursion_is_reported(self):
        self.r.defined[('min', 'num2foo')] = 'num2foo'
        out = [(self.f, [numeral(0)], Comb(self.f, numeral(0))),
               (self.f, [numeral(1)], numeral(1))]
        text, recursive = render_multi(self.r, 'num2foo', out)
        self.assertTrue(recursive)
        self.assertIn('num2foo', text)

    def test_non_recursive_multi_clause_is_reported_as_such(self):
        out = [(self.f, [numeral(0)], numeral(0)),
               (self.f, [numeral(1)], numeral(1))]
        text, recursive = render_multi(self.r, 'num2foo', out)
        self.assertFalse(recursive)
        self.assertIn('| 0 => 0', text)

    def test_default_arm_reuses_the_first_clause_body(self):
        # The default arm must not render the first clause a second time.
        calls = []
        original = self.r.tm
        def counting(t, env):
            calls.append(t)
            return original(t, env)
        self.r.tm = counting
        out = [(self.f, [numeral(0)], numeral(0)),
               (self.f, [numeral(1)], numeral(1))]
        text, _ = render_multi(self.r, 'num2foo', out)
        self.assertEqual(len(calls), 2)
        self.assertIn('| _ => 0', text)


class ExtraTypesPathTest(unittest.TestCase):
    def test_missing_configured_extra_types_file_raises(self):
        # A configured extra types module must exist: silently dropping it
        # loses constructors and surfaces later as an unrelated render error.
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            sexp = pathlib.Path(d, 'defs.sexp')
            sexp.write_text('')
            types = pathlib.Path(d, 'Types.lean')
            types.write_text('')
            saved = dict(M['EXTRA_TYPES_PATH'])
            M['EXTRA_TYPES_PATH']['arm8'] = (
                pathlib.Path(d, 'missing.lean'), ('ShiftType', 'MoveWideOp'))
            try:
                with self.assertRaises(FileNotFoundError):
                    M['main'](['prog', str(sexp), str(types), '--thy=arm8'])
            finally:
                M['EXTRA_TYPES_PATH'].clear()
                M['EXTRA_TYPES_PATH'].update(saved)
                M['MODEL_THY'] = 'riscv'

    def test_configured_type_missing_from_extra_file_raises(self):
        # Only the named types are imported from the hand-written module; a
        # rename there must fail loudly rather than silently drop the datatype.
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            sexp = pathlib.Path(d, 'defs.sexp')
            sexp.write_text('')
            types = pathlib.Path(d, 'Types.lean')
            types.write_text('')
            extra = pathlib.Path(d, 'extra.lean')
            extra.write_text('inductive ShiftType where\n  | LSL\n')
            saved = dict(M['EXTRA_TYPES_PATH'])
            M['EXTRA_TYPES_PATH']['arm8'] = (extra, ('ShiftType', 'MoveWideOp'))
            try:
                with self.assertRaises(ValueError):
                    M['main'](['prog', str(sexp), str(types), '--thy=arm8'])
            finally:
                M['EXTRA_TYPES_PATH'].clear()
                M['EXTRA_TYPES_PATH'].update(saved)
                M['MODEL_THY'] = 'riscv'


if __name__ == '__main__':
    unittest.main()
