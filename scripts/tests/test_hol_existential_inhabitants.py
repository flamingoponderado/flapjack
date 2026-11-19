"""Guards for the two dedicated GC inhabitance qualifiers."""
import runpy
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
REFS = runpy.run_path(str(SCRIPTS / "check-hol-refs.py"))
EXPORT = runpy.run_path(str(SCRIPTS / "check_hol_ref_export.py"))
MAP = runpy.run_path(str(SCRIPTS / "check_hol_theorem_map.py"))


class ExistentialInhabitantsTest(unittest.TestCase):
    def scan(self, qualifier):
        source = ('@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" '
                  '"state_rel_gc_gen" ' + qualifier + ']')
        return list(REFS["hol_attribute_sites"](
            [source], include_hol_existential_inhabitants=True))[0][-1]

    def test_exact_order_is_preserved(self):
        self.assertEqual(self.scan('(hol_existential_inhabitants := [T2._t2, W1._w1, W2._w2])'),
                         ('T2._t2', 'W1._w1', 'W2._w2'))

    def test_repeated_or_malformed_qualifier_fails_closed(self):
        qualifier = '(hol_existential_inhabitants := [T2._t2])'
        self.assertEqual(self.scan(qualifier + ' ' + qualifier), ('',))
        self.assertEqual(self.scan('(hol_existential_inhabitants := T2._t2)'), ('',))

    def test_gc_lemma_qualifier_has_separate_metadata(self):
        source = ('@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" '
                  '"gc_lemma_gen" (gc_lemma_existential_inhabitants := [W1._w1, W2._w2])]')
        site = list(REFS['hol_attribute_sites'](
            [source], include_hol_existential_inhabitants=True,
            include_gc_lemma_existential_inhabitants=True))[0]
        self.assertEqual(site[-2:], ((), ('W1._w1', 'W2._w2')))
        repeated = source.replace(')]', ') (gc_lemma_existential_inhabitants := [W1._w1, W2._w2])]')
        repeated_site = list(REFS['hol_attribute_sites'](
            [repeated], include_gc_lemma_existential_inhabitants=True))[0]
        self.assertEqual(repeated_site[-1], ('',))

    def test_audited_gc_store_is_existential_and_requires_opt_in(self):
        check = REFS['fmap_as_finite_support_relation_errors']
        entries = (('st', ''),)
        existential = 'theorem example : ∃ (st : HolFiniteMapExact Nat Nat), True := by trivial'
        parameter = 'theorem example (st : HolFiniteMapExact Nat Nat) : True := by trivial'
        self.assertTrue(check([], entries, 'Example.lean', existential))
        self.assertEqual(check([], entries, 'Example.lean', existential, audited_gc_store=True), [])
        self.assertTrue(check([], entries, 'Example.lean', parameter, audited_gc_store=True))
        let_result = ('theorem example : (let n := 1; '
                      '∃ (st : HolFiniteMapExact Nat Nat), True) := by trivial')
        self.assertEqual(check([], entries, 'Example.lean', let_result, audited_gc_store=True), [])

    def test_gc_lemma_export_metadata_must_match(self):
        fields = ['W1._w1', 'W2._w2']
        manifest = {'hol_path': 'cakeml/test.sml', 'hol_name': 'example',
                    'lean_path': 'Flapjack/Example.lean', 'lean_name': 'example',
                    'statement_status': 'reviewed_exact', 'gc_lemma_existential_inhabitants': fields}
        exported = {'hol_path': manifest['hol_path'], 'hol_name': 'example',
                    'lean_name': 'Example.example', 'qualifiers': {}}
        with self.assertRaises(ValueError):
            EXPORT['check_records']([manifest], [exported])
        del manifest['gc_lemma_existential_inhabitants']
        exported['qualifiers']['gc_lemma_existential_inhabitants'] = fields
        with self.assertRaises(ValueError):
            EXPORT['check_records']([manifest], [exported])

    def test_export_and_manifest_preserve_metadata(self):
        fields = ['T2._t2', 'W1._w1', 'W2._w2']
        self.assertIn('hol_existential_inhabitants', EXPORT['ALLOWED_QUALIFIERS'])
        self.assertEqual(EXPORT['manifest_qualifiers']({'hol_existential_inhabitants': fields})
                         ['hol_existential_inhabitants'], fields)

    def test_export_mismatch_is_rejected_in_both_directions(self):
        fields = ['T2._t2', 'W1._w1', 'W2._w2']
        manifest = {'hol_path': 'cakeml/test.sml', 'hol_name': 'example',
                    'lean_path': 'Flapjack/Example.lean', 'lean_name': 'example',
                    'statement_status': 'reviewed_exact', 'hol_existential_inhabitants': fields}
        exported = {'hol_path': manifest['hol_path'], 'hol_name': 'example',
                    'lean_name': 'Example.example', 'qualifiers': {}}
        with self.assertRaises(ValueError):
            EXPORT['check_records']([manifest], [exported])
        del manifest['hol_existential_inhabitants']
        exported['qualifiers']['hol_existential_inhabitants'] = fields
        with self.assertRaises(ValueError):
            EXPORT['check_records']([manifest], [exported])

    def test_manifest_rejects_wrong_witness_pairs(self):
        hol_path = 'cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml'
        lean_path = 'Flapjack/Compiler/Backend/DataToWord/Proofs/Gc/StateRelGc.lean'
        fields = ('T2._t2', 'W1._w1', 'W2._w2')
        relation = (('st', ''), ('WordSemStateFiniteExact', 'fpRegs'),
                    ('WordSemStateFiniteExact', 'store'))
        tag = (hol_path, 'state_rel_gc_gen', (), (), (), (), False, relation,
               False, True, (), (), None, (), (), False, False, (), (), (), (),
               (), (), (), (), (), (), fields)
        record = {'hol_path': hol_path, 'hol_name': 'state_rel_gc_gen',
                  'lean_path': lean_path, 'lean_name': 'stateRel_gcGen',
                  'statement_status': 'reviewed_fmap_as_finite_support_relation_words_as_type_indexed_bitvec',
                  'fmap_as_finite_support_relation': ['st', 'WordSemStateFiniteExact.fpRegs',
                                                       'WordSemStateFiniteExact.store'],
                  'words_as_type_indexed_bitvec': True,
                  'hol_existential_inhabitants': list(fields),
                  'reviewer': 'source comparison of hol_existential_inhabitants and finite maps'}
        tagged = {(lean_path, 'stateRel_gcGen'): tag}
        self.assertEqual(MAP['validate_inventory']([record], set(), tagged, set()), [])
        record['hol_existential_inhabitants'] = ['T2._t2', 'W1._w1', 'W1._w2']
        self.assertTrue(MAP['validate_inventory']([record], set(), tagged, set()))

    def test_gc_lemma_manifest_requires_its_two_distinct_witnesses(self):
        hol_path = 'cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml'
        lean_path = 'Flapjack/Compiler/Backend/DataToWord/Proofs/Gc/GcLemma.lean'
        fields = ('W1._w1', 'W2._w2')
        relation = (('st', ''), ('WordSemStateFiniteExact', 'fpRegs'),
                    ('WordSemStateFiniteExact', 'store'))
        tag = (hol_path, 'gc_lemma_gen', (), (), (), (), False, relation,
               False, True, (), (), None, (), (), False, False, (), (), (), (),
               (), (), (), (), (), (), (), fields)
        record = {'hol_path': hol_path, 'hol_name': 'gc_lemma_gen',
                  'lean_path': lean_path, 'lean_name': 'gcLemma_gen',
                  'statement_status': 'reviewed_fmap_as_finite_support_relation_words_as_type_indexed_bitvec',
                  'fmap_as_finite_support_relation': ['st', 'WordSemStateFiniteExact.fpRegs',
                                                       'WordSemStateFiniteExact.store'],
                  'words_as_type_indexed_bitvec': True,
                  'gc_lemma_existential_inhabitants': list(fields),
                  'reviewer': 'source comparison of gc_lemma_existential_inhabitants and finite maps'}
        tagged = {(lean_path, 'gcLemma_gen'): tag}
        self.assertEqual(MAP['validate_inventory']([record], set(), tagged, set()), [])
        record['gc_lemma_existential_inhabitants'] = ['W1._w1', 'W1._w2']
        self.assertTrue(MAP['validate_inventory']([record], set(), tagged, set()))


if __name__ == '__main__':
    unittest.main()
