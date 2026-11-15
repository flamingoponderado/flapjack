"""The nested-list qualifier checks its relation and observers."""

import runpy
import unittest
from pathlib import Path


CHECK = runpy.run_path(str(Path(__file__).resolve().parents[1] / "check-hol-refs.py"))
PATH = "cakeml/compiler/backend/proofs/clos_annotateProofScript.sml"
LEAN = "Flapjack/Compiler/Backend/ClosAnnotate/Proofs/ValueRelation.lean"
ATTRIBUTE = f'@[hol "{PATH}" "v_rel" (nested_list_rel_as_mutual := [FunctionsRel])]'


class NestedListQualifierTest(unittest.TestCase):
    def test_both_members_and_no_others(self):
        text = f"{ATTRIBUTE}\ninductive ValueRel : Prop\n{ATTRIBUTE}\ninductive EnvOk : Prop\n"
        lines = text.splitlines()
        sites = list(CHECK["hol_attribute_sites"](lines, include_nested_list_rel=True))
        self.assertEqual(len(sites), 2)
        for site in sites:
            self.assertEqual(site[-1], ("FunctionsRel",))
            self.assertEqual(CHECK["nested_list_rel_errors"](lines, LEAN, site[0], PATH, "v_rel", site[-1]), [])
            self.assertTrue(CHECK["nested_list_rel_errors"](lines, "Flapjack/Other.lean", site[0], PATH, "v_rel", site[-1]))
        one_member = lines[:2]
        self.assertTrue(CHECK["nested_list_rel_errors"](one_member, LEAN, 1, PATH, "v_rel", ("FunctionsRel",)))
        extra = lines + [ATTRIBUTE, "inductive FunctionsRel : Prop"]
        self.assertTrue(CHECK["nested_list_rel_errors"](extra, LEAN, 1, PATH, "v_rel", ("FunctionsRel",)))

    def test_duplicate_and_wrong_auxiliary_are_rejected(self):
        for suffix in ("(nested_list_rel_as_mutual := [FunctionsRel])", ""):
            attr = f'@[hol "{PATH}" "v_rel" (nested_list_rel_as_mutual := [Other]) {suffix}]'
            lines = [attr, "inductive ValueRel : Prop"]
            site = next(CHECK["hol_attribute_sites"](lines, include_nested_list_rel=True))
            self.assertTrue(CHECK["nested_list_rel_errors"](lines, LEAN, 1, PATH, "v_rel", site[-1]))

    def test_default_observer_requires_envok_and_relation_peers(self):
        observer_attr = f'@[hol "{PATH}" "env_set_default" (nested_list_rel_as_mutual := [FunctionsRel])]'
        lines = [ATTRIBUTE, "inductive ValueRel : Prop", ATTRIBUTE, "inductive EnvOk : Prop",
                 observer_attr, "theorem envSetDefault : EnvOk 0 := by trivial"]
        validate = CHECK["nested_list_rel_errors"]
        self.assertEqual(validate(lines, LEAN, 5, PATH, "env_set_default", ("FunctionsRel",)), [])
        for bad in ("theorem envSetDefault : EnvOk (FunctionsRel 0) := by trivial",):
            changed = [*lines[:-1], bad]
            self.assertTrue(validate(changed, LEAN, 5, PATH, "env_set_default", ("FunctionsRel",)))
        self.assertTrue(validate(lines[4:], LEAN, 1, PATH, "env_set_default", ("FunctionsRel",)))

    def test_general_observers_and_wrong_relation_tag(self):
        attr = f'@[hol "{PATH}" "env_ok_shifted_env" (nested_list_rel_as_mutual := [FunctionsRel])]'
        peers = [ATTRIBUTE, "inductive ValueRel : Prop", ATTRIBUTE, "inductive EnvOk : Prop"]
        validate = CHECK["nested_list_rel_errors"]
        for decl in ("theorem arbitrary : EnvOk 0 := by trivial",
                     "theorem arbitrary : ValueRel 0 := by trivial"):
            self.assertEqual(validate(peers + [attr, decl], LEAN, 5, PATH,
                                      "env_ok_shifted_env", ("FunctionsRel",)), [])
        bad = peers + [ATTRIBUTE, "theorem fake : EnvOk 0 := by trivial"]
        self.assertTrue(validate(bad, LEAN, 5, PATH, "v_rel", ("FunctionsRel",)))
        other = [attr, "theorem arbitrary : EnvOk 0 := by trivial"]
        self.assertEqual(validate(other, "Flapjack/Compiler/Backend/ClosAnnotate/Proofs/Other.lean", 1, PATH,
                                  "env_ok_shifted_env", ("FunctionsRel",)), [])
        self.assertTrue(validate(other, "Flapjack/Other.lean", 1, PATH,
                                 "env_ok_shifted_env", ("FunctionsRel",)))

    def test_combined_observer_requires_map_fields_and_witness(self):
        module = "Flapjack.Compiler.Backend.ClosAnnotate.Proofs.StateRelation.Original"
        path = CHECK["ROOT"] / "Flapjack/Compiler/Backend/ClosAnnotate/Proofs/StateRelation/Original.lean"
        lines = path.read_text(encoding="utf-8").splitlines()
        site = next(site for site in CHECK["hol_attribute_sites"](lines, include_nested_list_rel=True)
                    if site[2] == "state_rel_def")
        signature = CHECK["tagged_declaration_text"](lines, site[0])
        validate = CHECK["fmap_as_finite_support_errors"]
        self.assertEqual(validate(lines, ("refs", "code"), module, signature), [])
        no_witness = [line.replace("holFmapAsFiniteSupportWitness", "missingWitness") for line in lines]
        self.assertTrue(validate(no_witness, ("refs", "code"), module, signature))
        self.assertTrue(validate(lines, ("refs", "missing"), module, signature))

    def test_only_reviewed_observer_combination_is_accepted(self):
        allowed = CHECK["nested_list_combination_allowed"]
        self.assertTrue(allowed(("refs", "code"), False, False))
        self.assertFalse(allowed(("refs", "code"), True, False))
        self.assertFalse(allowed(("refs",), False, False))
        self.assertFalse(allowed((), False, True))  # includes relation and words qualifiers

    def test_thunk_map_combination_is_narrow(self):
        allowed = CHECK["nested_thunk_map_combination"]
        args = [PATH, "rel_update_thunk",
                "Flapjack/Compiler/Backend/ClosAnnotate/Proofs/ThunkOperations.lean",
                "relUpdateThunkSource", ("FunctionsRel",), (),
                (("State", "refs"), ("State", "code"), ("sourceRefs", "")), ("targetRefs",)]
        self.assertTrue(allowed(*args))
        for index, bad in [(0, "cakeml/otherScript.sml"), (1, "other"),
                           (2, "Flapjack/Other.lean"), (3, "other"),
                           (4, ("Other",)), (5, ("refs", "code")),
                           (6, (("State", "code"), ("State", "refs"), ("sourceRefs", ""))),
                           (6, (("State", "refs"), ("State", "code"))),
                           (6, args[6] + (("other", ""),)), (7, ()),
                           (7, ("targetRefs", "other"))]:
            changed = args.copy()
            changed[index] = bad
            self.assertFalse(allowed(*changed), (index, bad))

    def test_thunk_map_witnesses_remain_required(self):
        path = CHECK["ROOT"] / "Flapjack/Compiler/Backend/ClosAnnotate/Proofs/ThunkOperations.lean"
        lines = path.read_text(encoding="utf-8").splitlines()
        site = next(site for site in CHECK["hol_attribute_sites"](lines, include_nested_list_rel=True)
                    if site[2] == "rel_update_thunk")
        signature = CHECK["tagged_declaration_text"](lines, site[0])
        module = "Flapjack.Compiler.Backend.ClosAnnotate.Proofs.ThunkOperations"
        relation = (("State", "refs"), ("State", "code"), ("sourceRefs", ""))
        relation_errors = CHECK["fmap_as_finite_support_relation_errors"]
        existential_errors = CHECK["fmap_as_finite_support_existentials_errors"]
        self.assertEqual(relation_errors(lines, relation, module, signature), [])
        self.assertEqual(existential_errors(lines, module, signature, "relUpdateThunkSource", ("targetRefs",)), [])
        missing_relation = [line.replace("holFmapAsFiniteSupportRelationWitness_State", "missingWitness") for line in lines]
        self.assertTrue(relation_errors(missing_relation, relation, module, signature))
        missing_existential = [line.replace("holFmapAsFiniteSupportExistentialWitness_relUpdateThunkSource_targetRefs", "missingWitness") for line in lines]
        self.assertTrue(existential_errors(missing_existential, module, signature, "relUpdateThunkSource", ("targetRefs",)))
        self.assertTrue(existential_errors(lines, module, signature, "relUpdateThunkSource", ("missing",)))


if __name__ == "__main__":
    unittest.main()
