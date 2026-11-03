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
Renderer = M['Renderer']
Unrenderable = M['Unrenderable']
fresh_binder = M['fresh_binder']
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


class InsertTest(unittest.TestCase):
    def test_binder_avoids_free_variable(self):
        self.assertEqual(insert_predicate(['a', 's']), '(fun x => x = a || s x)')

    def test_binder_renamed_when_operand_uses_x(self):
        self.assertEqual(insert_predicate(['x', 's']), "(fun x' => x' = x || s x')")

    def test_binder_renamed_for_both_operands(self):
        self.assertEqual(insert_predicate(["x'", 'x']), "(fun x'' => x'' = x' || x x'')")

    def test_fresh_binder_leaves_unrelated_names_alone(self):
        self.assertEqual(fresh_binder('x', ['y', 's']), 'x')


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

    def test_step_larger_than_input_width_is_rejected(self):
        # A 16-bit input cannot hold `pos + 31` at every `pos`.
        low = Var('pos', NUM)
        self.assertFalse(symbolic_field_bounds(add(low, numeral(31)), low, 16))
        self.assertTrue(symbolic_field_bounds(add(low, numeral(31)), low, 32))


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

    def test_unchecked_symbolic_bounds_are_rejected(self):
        with self.assertRaises(Unrenderable):
            self.render(add(self.low, numeral(31)))

    def test_literal_bounds_wider_than_input_are_rejected(self):
        self.low = numeral(0)
        with self.assertRaises(Unrenderable):
            self.render(numeral(31))


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


if __name__ == '__main__':
    unittest.main()
