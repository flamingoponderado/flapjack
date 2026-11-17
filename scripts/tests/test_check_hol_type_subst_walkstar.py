"""Source checks for independent substitution maps in both HOL cases."""

import json
import runpy
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CHECK = runpy.run_path(str(ROOT / "scripts/check-hol-refs.py"))["type_subst_walkstar_observer_errors"]
PATH = "Flapjack/Compiler/Inference/InferProps/TypeSubstWalkstar.lean"
REF = ("cakeml/compiler/inference/inferPropsScript.sml", "subst_infer_subst_swap")
BINDERS = ("type_s", "list_s")
SOURCE = (ROOT / PATH).read_text()
DEPENDENCIES = tuple((ROOT / path).read_text() for path in (
    "Flapjack/Compiler/Inference/Infer.lean", "Flapjack/Compiler/Inference/Unify/Walkstar.lean",
    "Flapjack/Compiler/Inference/Unify/Substitution.lean", "Flapjack/Compiler/Inference/Unify/Walk/Term.lean",
    "Flapjack/Compiler/Inference/Unify/Walk.lean"))
ROWS = json.loads((ROOT / "docs/HOL-THEOREM-MAP.json").read_text())


class TypeSubstWalkstarSourceTest(unittest.TestCase):
    def check(self, source=SOURCE, path=PATH, ref=REF, binders=BINDERS, dependencies=DEPENDENCIES, rows=ROWS):
        return CHECK(source, path, ref, binders, dependencies, rows)

    def test_actual_statement_and_dependencies(self):
        self.assertEqual(self.check(), [])

    def test_site_and_independent_occurrences(self):
        for args in ({"path": "Other.lean"}, {"ref": (REF[0], "other")},
                     {"binders": ("type_s", "type_s")}, {"binders": ("list_s", "type_s")}):
            with self.subTest(args=args):
                self.assertTrue(self.check(**args))

    def test_statement_and_carrier_mutations_fail(self):
        for source in (
            SOURCE.replace("tWfs s →\n      tWalkstar", "True →\n      tWalkstar"),
            SOURCE.replace("List.range names.length", "List.range (names.length + 1)"),
            SOURCE.replace("offset + n", "n + offset"),
            SOURCE.replace("s : HolFiniteMapExact Nat InferT", "s : HolFiniteMapExact Nat Nat"),
            SOURCE.replace("mutual\n", "abbrev SemanticT := Bool\nmutual\n", 1),
            SOURCE.replace("mutual\n", "export Other (inferTypeSubst)\nmutual\n", 1),
            SOURCE.replace("public import Flapjack.Compiler.Inference.Infer.TypeSubst\n",
                           "public import Flapjack.Compiler.Inference.Infer.TypeSubst Other\n"),
            SOURCE.replace("(map : HolFiniteMapExact Nat InferT) (key : Nat)",
                           "(map : HolFiniteMapExact Nat InferT) (key : Nat) (extra : True)"),
        ):
            with self.subTest(source=source[-120:]):
                self.assertTrue(self.check(source=source))

    def test_dependency_rows_are_unique_and_reviewed(self):
        for name in ("inferTypeSubst", "inferTypeSubstList", "tWfs", "walkstarEqn", "tWalkstarEqn1", "tWalkEqn", "tVwalkEq", "InferT", "SemanticT", "MlString"):
            rows = [row for row in ROWS if row.get("lean_name") != name]
            with self.subTest(name=name):
                self.assertTrue(self.check(rows=rows))
            row = next(row for row in ROWS if row.get("lean_name") == name)
            with self.subTest(duplicate=name):
                self.assertTrue(self.check(rows=ROWS + [row]))

    def test_changed_dependency_definitions_fail(self):
        mutations = (
            DEPENDENCIES[0].replace("(s.lookup v).getD (.varDb 0)", "(.uvar 0)", 1),
            DEPENDENCIES[1].replace("decodeInferT (walkstar", "decodeInferT (walk", 1),
            DEPENDENCIES[2].replace("wfs (subst.map2", "False ∧ wfs (subst.map2", 1),
            DEPENDENCIES[3].replace("decodeInferT (walk (subst.map2", "decodeInferT (walkstar (subst.map2", 1),
            DEPENDENCIES[4].replace("decodeInferT (vwalk", "decodeInferT (walkstar", 1),
        )
        for index, source in enumerate(mutations):
            changed = list(DEPENDENCIES)
            changed[index] = source
            with self.subTest(index=index):
                self.assertTrue(self.check(dependencies=tuple(changed)))


if __name__ == "__main__":
    unittest.main()
